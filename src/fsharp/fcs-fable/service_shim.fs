// Copyright (c) Microsoft Corporation.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

// Open up the compiler as an incremental service for parsing,
// type checking and intellisense-like environment-reporting.

namespace Microsoft.FSharp.Compiler.SourceCodeServices

#nowarn "1182"

open System
//open System.IO
open System.Text
open System.Threading
//open System.Reflection.Emit
//open System.Runtime
open System.Collections.Generic

//open Microsoft.FSharp.Core.Printf
open Microsoft.FSharp.Compiler 
open Microsoft.FSharp.Compiler.AbstractIL
open Microsoft.FSharp.Compiler.AbstractIL.IL
open Microsoft.FSharp.Compiler.AbstractIL.Diagnostics 
open Microsoft.FSharp.Compiler.AbstractIL.Internal  
open Microsoft.FSharp.Compiler.AbstractIL.Internal.Library  

open Microsoft.FSharp.Compiler.AccessibilityLogic
open Microsoft.FSharp.Compiler.Ast
open Microsoft.FSharp.Compiler.CompileOps
//open Microsoft.FSharp.Compiler.Driver
open Microsoft.FSharp.Compiler.ErrorLogger
open Microsoft.FSharp.Compiler.Lib
open Microsoft.FSharp.Compiler.ReferenceResolver
open Microsoft.FSharp.Compiler.PrettyNaming
open Microsoft.FSharp.Compiler.Parser
open Microsoft.FSharp.Compiler.Range
open Microsoft.FSharp.Compiler.Lexhelp
open Microsoft.FSharp.Compiler.Layout
open Microsoft.FSharp.Compiler.Tast
open Microsoft.FSharp.Compiler.Tastops
open Microsoft.FSharp.Compiler.Tastops.DebugPrint
open Microsoft.FSharp.Compiler.TcGlobals 
open Microsoft.FSharp.Compiler.Infos
open Microsoft.FSharp.Compiler.InfoReader
open Microsoft.FSharp.Compiler.NameResolution
open Microsoft.FSharp.Compiler.TypeChecker
open Microsoft.FSharp.Compiler.SourceCodeServices.ItemDescriptionsImpl 

open Internal.Utilities
open Internal.Utilities.Collections
open Microsoft.FSharp.Collections

//-------------------------------------------------------------------------
// From IncrementalBuild.fs
//------------------------------------------------------------------------
[<RequireQualifiedAccess>]
type FSharpErrorSeverity = 
    | Warning 
    | Error

type FSharpErrorInfo(fileName, s:pos, e:pos, severity: FSharpErrorSeverity, message: string, subcategory: string, errorNum: int) = 
    member __.StartLine = Line.toZ s.Line
    member __.StartLineAlternate = s.Line
    member __.EndLine = Line.toZ e.Line
    member __.EndLineAlternate = e.Line
    member __.StartColumn = s.Column
    member __.EndColumn = e.Column
    member __.Severity = severity
    member __.Message = message
    member __.Subcategory = subcategory
    member __.FileName = fileName
    member __.ErrorNumber = errorNum
    member __.WithStart(newStart) = FSharpErrorInfo(fileName, newStart, e, severity, message, subcategory, errorNum)
    member __.WithEnd(newEnd) = FSharpErrorInfo(fileName, s, newEnd, severity, message, subcategory, errorNum)
    override __.ToString()= sprintf "%s (%d,%d)-(%d,%d) %s %s %s" fileName (int s.Line) (s.Column + 1) (int e.Line) (e.Column + 1) subcategory (if severity=FSharpErrorSeverity.Warning then "warning" else "error")  message
            
    /// Decompose a warning or error into parts: position, severity, message, error number
    static member (*internal*) CreateFromException(exn, isError, trim:bool, fallbackRange:range) = 
        let m = match GetRangeOfDiagnostic exn with Some m -> m | None -> fallbackRange 
        let e = if trim then m.Start else m.End
        let msg = bufs (fun buf -> OutputPhasedDiagnostic ErrorLogger.ErrorStyle.DefaultErrors buf exn false)
        let errorNum = GetDiagnosticNumber exn
        FSharpErrorInfo(m.FileName, m.Start, e, (if isError then FSharpErrorSeverity.Error else FSharpErrorSeverity.Warning), msg, exn.Subcategory(), errorNum)
        
    /// Decompose a warning or error into parts: position, severity, message, error number
    static member internal CreateFromExceptionAndAdjustEof(exn, isError, trim:bool, fallbackRange:range, (linesCount:int, lastLength:int)) = 
        let r = FSharpErrorInfo.CreateFromException(exn,isError,trim,fallbackRange)
                
        // Adjust to make sure that errors reported at Eof are shown at the linesCount        
        let startline, schange = min (r.StartLineAlternate, false) (linesCount, true)
        let endline,   echange = min (r.EndLineAlternate, false)   (linesCount, true)
        
        if not (schange || echange) then r
        else
            let r = if schange then r.WithStart(mkPos startline lastLength) else r
            if echange then r.WithEnd(mkPos  endline (1 + lastLength)) else r

//-------------------------------------------------------------------------
// From ServiceUntypedParse.fs
//------------------------------------------------------------------------
[<Sealed>]
type FSharpParseFileResults(errors : FSharpErrorInfo[], input : Ast.ParsedInput option, parseHadErrors : bool, dependencyFiles : string list) = 
    member scope.Errors = errors
    member scope.ParseHadErrors = parseHadErrors
    member scope.ParseTree = input


//-------------------------------------------------------------------------
// From service.fs
//------------------------------------------------------------------------

// A scope represents everything we get back from the typecheck of a file.
// It acts like an in-memory database about the file.
// It is effectively immutable and not updated: when we re-typecheck we just drop the previous
// scope object on the floor and make a new one.
[<Sealed>]
type internal TypeCheckInfo
        (// Information corresponding to miscellaneous command-line options (--define, etc).
        _sTcConfig: TcConfig,
        g: TcGlobals,
        // The signature of the assembly being checked, up to and including the current file
        ccuSig: ModuleOrNamespaceType,
        thisCcu: CcuThunk,
        tcImports: TcImports,
        tcAccessRights: AccessorDomain,
        projectFileName: string ,
        mainInputFileName: string ,
        sResolutions: TcResolutions,
        sSymbolUses: TcSymbolUses,
        // This is a name resolution environment to use if no better match can be found.
        sFallback: NameResolutionEnv,
        //loadClosure : LoadClosure option,
        reactorOps : IReactorOperations,
        checkAlive : (unit -> bool),
        textSnapshotInfo:obj option) =

    member x.ScopeResolutions = sResolutions
    member x.ScopeSymbolUses = sSymbolUses
    member x.TcGlobals = g
    member x.TcImports = tcImports
    member x.CcuSig = ccuSig
    member x.ThisCcu = thisCcu
    member x.PartialAssemblySignature() = FSharpAssemblySignature(g, thisCcu, tcImports, None, ccuSig)
    member x.AccessRights = tcAccessRights


module internal Parser = 

        // We'll need number of lines for adjusting error messages at EOF
    let GetFileInfoForLastLineErrors (source: string) = 
        // number of lines in the source file
        let lastLine = (source |> Seq.sumBy (fun c -> if c = '\n' then 1 else 0)) + 1
        // length of the last line
        let lastLineLength = source.Length - source.LastIndexOf("\n") - 1 //("\n",StringComparison.Ordinal) - 1
        lastLine, lastLineLength
         
    let ReportError (tcConfig:TcConfig, allErrors, mainInputFileName, fileInfo, (exn, sev)) = 
        [ let isError = (sev = FSharpErrorSeverity.Error) || ReportWarningAsError (tcConfig.globalWarnLevel, tcConfig.specificWarnOff, tcConfig.specificWarnOn, tcConfig.specificWarnAsError, tcConfig.specificWarnAsWarn, tcConfig.globalWarnAsError) exn                
          if (isError || ReportWarning (tcConfig.globalWarnLevel, tcConfig.specificWarnOff, tcConfig.specificWarnOn) exn) then 
            let oneError trim exn = 
                [ // We use the first line of the file as a fallbackRange for reporting unexpected errors.
                  // Not ideal, but it's hard to see what else to do.
                  let fallbackRange = rangeN mainInputFileName 1
                  let ei = FSharpErrorInfo.CreateFromExceptionAndAdjustEof (exn, isError, trim, fallbackRange, fileInfo)
                  if allErrors || (ei.FileName=mainInputFileName) || (ei.FileName=Microsoft.FSharp.Compiler.TcGlobals.DummyFileNameForRangesWithoutASpecificLocation) then
                      yield ei ]
                      
            let mainError,relatedErrors = SplitRelatedDiagnostics exn 
            yield! oneError false mainError
            for e in relatedErrors do 
                yield! oneError true e ]

    let CreateErrorInfos (tcConfig:TcConfig, allErrors, mainInputFileName, errors) = 
        let fileInfo = (Int32.MaxValue, Int32.MaxValue)
        [| for (exn,isError) in errors do 
              yield! ReportError (tcConfig, allErrors, mainInputFileName, fileInfo, (exn, isError)) |]
                            

    /// Error handler for parsing & type checking while processing a single file
    type ErrorHandler(reportErrors, mainInputFileName, tcConfig: TcConfig, source: string) =
        let mutable tcConfig = tcConfig
        let errorsAndWarningsCollector = new ResizeArray<_>()
        let mutable errorCount = 0
         
        // We'll need number of lines for adjusting error messages at EOF
        let fileInfo = GetFileInfoForLastLineErrors source
         
        // This function gets called whenever an error happens during parsing or checking
        let diagnosticSink sev (exn:PhasedDiagnostic) = 
            // Sanity check here. The phase of an error should be in a phase known to the language service.
            let exn =
                if not(exn.IsPhaseInCompile()) then
                    // Reaching this point means that the error would be sticky if we let it prop up to the language service.
                    // Assert and recover by replacing phase with one known to the language service.
                    System.Diagnostics.Debug.Assert(false, sprintf "The subcategory '%s' seen in an error should not be seen by the language service" (exn.Subcategory()))
                    {exn with Phase=BuildPhase.TypeCheck}
                else exn
            if reportErrors then 
                let report exn = 
                    for ei in ReportError (tcConfig, false, mainInputFileName, fileInfo, (exn, sev)) do
                        errorsAndWarningsCollector.Add ei
                        if sev = FSharpErrorSeverity.Error then 
                            errorCount <- errorCount + 1
                      
                match exn with
#if EXTENSIONTYPING
                | {Exception = (:? TypeProviderError as tpe)} ->
                    tpe.Iter (fun e ->
                        let newExn = {exn with Exception = e}
                        report newExn
                    )
#endif
                | e -> report e
      
        let errorLogger = 
            { new ErrorLogger("ErrorHandler") with 
                member x.DiagnosticSink (exn, isError) = diagnosticSink (if isError then FSharpErrorSeverity.Error else FSharpErrorSeverity.Warning) exn
                member x.ErrorCount = errorCount }
      
      
        // Public members
        member x.ErrorLogger = errorLogger
        member x.CollectedDiagnostics = errorsAndWarningsCollector.ToArray()
        member x.ErrorCount = errorCount
        member x.TcConfig with set tc = tcConfig <- tc
        member x.AnyErrors = errorCount > 0


    /// ParseOneFile builds all the information necessary to report errors, match braces and build scopes 
    ///
    /// projectSourceFiles is only used to compute isLastCompiland, and is ignored if Build.IsScript(mainInputFileName)  is true.
    let ParseOneFile (source: string, matchBracesOnly: bool, reportErrors: bool, mainInputFileName: string, projectSourceFiles: string list, tcConfig: TcConfig) =

          // Initialize the error handler 
          let errHandler = new ErrorHandler(reportErrors, mainInputFileName, tcConfig, source)

          let lexbuf = UnicodeLexing.StringAsLexbuf source

          // Collector for parens matching
          let matchPairRef = new ResizeArray<_>()

          use unwindEL = PushErrorLoggerPhaseUntilUnwind(fun _oldLogger -> errHandler.ErrorLogger)
          use unwindBP = PushThreadBuildPhaseUntilUnwind (BuildPhase.Parse)

          // Errors on while parsing project arguments 

          let parseResult = 

              // If editing a script then define INTERACTIVE otherwise COMPILED.
              // If this parsing is for intellisense, also define EDITING
#if FABLE_COMPILER
              let conditionalCompilationDefines =
                  ["COMPILED"] // ["INTERACTIVE";"EDITING"]
                  @ tcConfig.conditionalCompilationDefines
              let lightSyntaxStatus = LightSyntaxStatus(true,true)
#else
              let conditionalCompilationDefines =
                SourceFileImpl.AdditionalDefinesForUseInEditor(mainInputFileName) @ tcConfig.conditionalCompilationDefines 
        
              let lightSyntaxStatusInital = tcConfig.ComputeLightSyntaxInitialStatus mainInputFileName
              let lightSyntaxStatus = LightSyntaxStatus(lightSyntaxStatusInital,true)
#endif
              // Note: we don't really attempt to intern strings across a large scope
              let lexResourceManager = new Lexhelp.LexResourceManager()
              let lexargs = mkLexargs(mainInputFileName,
                                      conditionalCompilationDefines,
                                      lightSyntaxStatus,
                                      lexResourceManager,
                                      ref [],
                                      errHandler.ErrorLogger)
              Lexhelp.usingLexbufForParsing (lexbuf, mainInputFileName) (fun lexbuf -> 
                  try 
                    let skip = true
                    let tokenizer = LexFilter.LexFilter (lightSyntaxStatus, tcConfig.compilingFslib, Lexer.token lexargs skip, lexbuf)
                    let lexfun = tokenizer.Lexer
                    if matchBracesOnly then 
                        // Quick bracket matching parse  
                        let parenTokensBalance t1 t2 = 
                            match t1,t2 with 
                            | (LPAREN,RPAREN) 
                            | (LPAREN,RPAREN_IS_HERE) 
                            | (LBRACE,RBRACE) 
                            | (LBRACE,RBRACE_IS_HERE) 
                            | (SIG,END) 
                            | (STRUCT,END) 
                            | (LBRACK_BAR,BAR_RBRACK)
                            | (LBRACK,RBRACK)
                            | (LBRACK_LESS,GREATER_RBRACK)
                            | (BEGIN,END) -> true 
                            | (LQUOTE q1,RQUOTE q2) when q1 = q2 -> true 
                            | _ -> false
                        let rec matchBraces stack = 
                            match lexfun lexbuf,stack with 
                            | tok2,((tok1,m1) :: stack') when parenTokensBalance tok1 tok2-> 
                                if matchBracesOnly then 
                                    matchPairRef.Add (m1, lexbuf.LexemeRange)
                                matchBraces stack'
                            | ((LPAREN | LBRACE | LBRACK | LBRACK_BAR | LQUOTE _ | LBRACK_LESS) as tok),_ -> matchBraces ((tok,lexbuf.LexemeRange) :: stack)
                            | (EOF _ | LEX_FAILURE _),_ -> ()
                            | _ -> matchBraces stack

                        matchBraces []
                        None
                    else 
                        let isLastCompiland = 
                            projectSourceFiles.Length >= 1 && 
                            System.String.Compare(projectSourceFiles.[projectSourceFiles.Length-1],mainInputFileName,StringComparison.CurrentCultureIgnoreCase)=0
                        let isLastCompiland = isLastCompiland || CompileOps.IsScript(mainInputFileName)  
#if FABLE_COMPILER
                        let isExe = false // true for NodeJS?
#else
                        let isExe = tcConfig.target.IsExe
#endif
                        let parseResult = ParseInput(lexfun,errHandler.ErrorLogger,lexbuf,None,mainInputFileName,(isLastCompiland,isExe))
                        Some parseResult
                  with e -> 
                    errHandler.ErrorLogger.ErrorR(e)
                    None)
                

          errHandler.CollectedDiagnostics,
          matchPairRef.ToArray(),
          parseResult,
          errHandler.AnyErrors


    /// Indicates if the type check got aborted because it is no longer relevant.
    type TypeCheckAborted = Yes | No of TypeCheckInfo

    // Type check a single file against an initial context, gleaning both errors and intellisense information.
    let TypeCheckOneFile
          (parseResults: FSharpParseFileResults,
           source: string,
           mainInputFileName: string,
           projectFileName: string,
           tcConfig: TcConfig,
           tcGlobals: TcGlobals,
           tcImports: TcImports,
           tcState: TcState,
           //loadClosure: LoadClosure option,
           // These are the errors and warnings seen by the background compiler for the entire antecedant 
           backgroundDiagnostics: (PhasedDiagnostic * FSharpErrorSeverity) list,    
           reactorOps: IReactorOperations,
           // Used by 'FSharpDeclarationListInfo' to check the IncrementalBuilder is still alive.
           checkAlive : (unit -> bool),
           textSnapshotInfo : obj option) = 
        
        //async {
            match parseResults.ParseTree with 
            // When processing the following cases, we don't need to type-check
            | None -> //return
                [||], TypeCheckAborted.Yes, []
                   
            // Run the type checker...
            | Some parsedMainInput ->
                // Initialize the error handler 
                let errHandler = new ErrorHandler(true, mainInputFileName, tcConfig, source)
            
                use _unwindEL = PushErrorLoggerPhaseUntilUnwind (fun _oldLogger -> errHandler.ErrorLogger)
                use _unwindBP = PushThreadBuildPhaseUntilUnwind (BuildPhase.TypeCheck)      
            
#if !FABLE_COMPILER
                // Apply nowarns to tcConfig (may generate errors, so ensure errorLogger is installed)
                let tcConfig = ApplyNoWarnsToTcConfig tcConfig (parsedMainInput,Path.GetDirectoryName mainInputFileName)
#endif
                        
                // update the error handler with the modified tcConfig
                errHandler.TcConfig <- tcConfig
            
                // Play background errors and warnings for this file.
                for (err,sev) in backgroundDiagnostics do
                    diagnosticSink (err, (sev = FSharpErrorSeverity.Error))
            
#if !FABLE_COMPILER
                // If additional references were brought in by the preprocessor then we need to process them
                match loadClosure with
                | Some loadClosure ->
                    // Play unresolved references for this file.
                    tcImports.ReportUnresolvedAssemblyReferences(loadClosure.UnresolvedReferences)
            
                    // If there was a loadClosure, replay the errors and warnings from resolution, excluding parsing
                    loadClosure.LoadClosureRootFileDiagnostics |> List.iter diagnosticSink
            
                    let fileOfBackgroundError err = (match GetRangeOfDiagnostic (fst err) with Some m-> m.FileName | None -> null)
                    let sameFile file hashLoadInFile = 
                        (0 = String.Compare(hashLoadInFile, file, StringComparison.OrdinalIgnoreCase))
            
                    //  walk the list of #loads and keep the ones for this file.
                    let hashLoadsInFile = 
                        loadClosure.SourceFiles 
                        |> List.filter(fun (_,ms) -> ms<>[]) // #loaded file, ranges of #load
            
                    let hashLoadBackgroundDiagnostics, otherBackgroundDiagnostics = 
                        backgroundDiagnostics 
                        |> List.partition (fun backgroundError -> 
                            hashLoadsInFile 
                            |>  List.exists (fst >> sameFile (fileOfBackgroundError backgroundError)))
            
                    // Create single errors for the #load-ed files.
                    // Group errors and warnings by file name.
                    let hashLoadBackgroundDiagnosticsGroupedByFileName = 
                        hashLoadBackgroundDiagnostics 
                        |> List.map(fun err -> fileOfBackgroundError err,err) 
                        |> List.groupByFirst  // fileWithErrors, error list
            
                    //  Join the sets and report errors. 
                    //  It is by-design that these messages are only present in the language service. A true build would report the errors at their
                    //  spots in the individual source files.
                    for (fileOfHashLoad, rangesOfHashLoad) in hashLoadsInFile do
                        for errorGroupedByFileName in hashLoadBackgroundDiagnosticsGroupedByFileName do
                            if sameFile (fst errorGroupedByFileName) fileOfHashLoad then
                                for rangeOfHashLoad in rangesOfHashLoad do // Handle the case of two #loads of the same file
                                    let diagnostics = snd errorGroupedByFileName |> List.map(fun (pe,f)->pe.Exception,f) // Strip the build phase here. It will be replaced, in total, with TypeCheck
                                    let errors = [ for (err,sev) in diagnostics do if sev = FSharpErrorSeverity.Error then yield err ]
                                    let warnings = [ for (err,sev) in diagnostics do if sev = FSharpErrorSeverity.Warning then yield err ]
                                    
                                    let message = HashLoadedSourceHasIssues(warnings,errors,rangeOfHashLoad)
                                    if errors=[] then warning(message)
                                    else errorR(message)
            
                    // Replay other background errors.
                    for (phasedError,sev) in otherBackgroundDiagnostics do
                        if sev = FSharpErrorSeverity.Warning then 
                            warning phasedError.Exception 
                        else errorR phasedError.Exception
            
                | None -> 
                    // For non-scripts, check for disallow #r and #load.
                    ApplyMetaCommandsFromInputToTcConfig tcConfig (parsedMainInput,Path.GetDirectoryName mainInputFileName) |> ignore
#endif

                // A problem arises with nice name generation, which really should only 
                // be done in the backend, but is also done in the typechecker for better or worse. 
                // If we don't do this the NNG accumulates data and we get a memory leak. 
                tcState.NiceNameGenerator.Reset()
                
                // Typecheck the real input.  
                let sink = TcResultsSinkImpl(tcGlobals, source = source)
            
#if FABLE_COMPILER
                let tcEnvAtEndOpt =
                    try
                        let checkForErrors() = (parseResults.ParseHadErrors || errHandler.ErrorCount > 0)
                        let (tcEnvAtEnd, _, typedImplFiles), tcState =
                            TypeCheckOneInputAndFinishEventually(checkForErrors,tcConfig, tcImports, tcGlobals, None, TcResultsSink.WithSink sink, tcState, parsedMainInput)
                            |> Eventually.force
                        Some (tcEnvAtEnd, typedImplFiles, tcState)
                    with
                    | e ->
                        errorR e
                        Some(tcState.TcEnvFromSignatures, [], tcState)
#else
                let! ct = Async.CancellationToken
                let! tcEnvAtEndOpt =
                    async {
                        try
                            let checkForErrors() = (parseResults.ParseHadErrors || errHandler.ErrorCount > 0)
                            // Typecheck is potentially a long running operation. We chop it up here with an Eventually continuation and, at each slice, give a chance
                            // for the client to claim the result as obsolete and have the typecheck abort.
                            let projectDir = Path.GetDirectoryName(projectFileName)
                            let capturingErrorLogger = CompilationErrorLogger("TypeCheckOneFile", tcConfig)
                            let errorLogger = GetErrorLoggerFilteringByScopedPragmas(false,GetScopedPragmasForInput(parsedMainInput), capturingErrorLogger)
                            
                            let! result = 
                                TypeCheckOneInputAndFinishEventually(checkForErrors,tcConfig, tcImports, tcGlobals, None, TcResultsSink.WithSink sink, tcState, parsedMainInput)
                                |> Eventually.repeatedlyProgressUntilDoneOrTimeShareOverOrCanceled 50L ct (fun f -> f())
                                |> Eventually.forceAsync 
                                    (fun (work: unit -> Eventually<_>) ->
                                        reactorOps.EnqueueAndAwaitOpAsync("TypeCheckOneFile", 
                                            fun _ -> 
                                                // Reinstall the compilation globals each time we start or restart
                                                use unwind = new CompilationGlobalsScope (errorLogger, BuildPhase.TypeCheck, projectDir)
                                                work()))
                            return result |> Option.map (fun ((tcEnvAtEnd, _, typedImplFiles), tcState) -> tcEnvAtEnd, typedImplFiles, tcState)
                        with
                        | e ->
                            errorR e
                            return Some(tcState.TcEnvFromSignatures, [], tcState)
                    }
#endif
                
                let errors = errHandler.CollectedDiagnostics
                
                match tcEnvAtEndOpt with
                | Some (tcEnvAtEnd, _typedImplFiles, tcState) ->
                    let scope = 
                        TypeCheckInfo(tcConfig, tcGlobals, 
                                    tcState.PartialAssemblySignature, 
                                    tcState.Ccu,
                                    tcImports,
                                    tcEnvAtEnd.AccessRights,
                                    //typedImplFiles,
                                    projectFileName, 
                                    mainInputFileName, 
                                    sink.GetResolutions(), 
                                    sink.GetSymbolUses(), 
                                    tcEnvAtEnd.NameEnv,
                                    //loadClosure,
                                    reactorOps,
                                    checkAlive,
                                    textSnapshotInfo)     
                    //return
                    errors, TypeCheckAborted.No scope, _typedImplFiles
                | None -> //return
                    errors, TypeCheckAborted.Yes, []
        //}

//type  UnresolvedReferencesSet = UnresolvedReferencesSet of UnresolvedAssemblyReference list

// NOTE: may be better just to move to optional arguments here
type FSharpProjectOptions =
    { 
      ProjectFileName: string
      ProjectFileNames: string[]
      OtherOptions: string[]
      ReferencedProjects: (string * FSharpProjectOptions)[]
      IsIncompleteTypeCheckEnvironment : bool
      UseScriptResolutionRules : bool      
      LoadTime : System.DateTime
      //UnresolvedReferences : UnresolvedReferencesSet option
      //OriginalLoadReferences: (range * string) list
      //ExtraProjectInfo : obj option
    }
[<Sealed>] 
type FSharpProjectContext internal (thisCcu: CcuThunk, assemblies: FSharpAssembly list, ad: AccessorDomain) =

    /// Get the assemblies referenced
    member __.GetReferencedAssemblies() = assemblies

    member __.AccessibilityRights = FSharpAccessibilityRights(thisCcu, ad)


[<Sealed>]
// 'details' is an option because the creation of the tcGlobals etc. for the project may have failed.
type FSharpCheckProjectResults internal (keepAssemblyContents, errors: FSharpErrorInfo[], details:(TcGlobals*TcImports*CcuThunk*ModuleOrNamespaceType*TcSymbolUses list*TopAttribs option*option<_> * ILAssemblyRef * AccessorDomain * TypedImplFile list option * string list) option, reactorOps: IReactorOperations) =

    let getDetails() = 
        match details with 
        | None -> invalidOp ("The project has no results due to critical errors in the project options. Check the HasCriticalErrors before accessing the detaild results. Errors: " + String.concat "\n" [ for e in errors -> e.Message ])
        | Some d -> d

    member info.Errors = errors

    member info.HasCriticalErrors = details.IsNone

    member info.AssemblySignature =  
        let (tcGlobals, tcImports, thisCcu, ccuSig, _tcSymbolUses, topAttribs, _tcAssemblyData, _ilAssemRef, _ad, _tcAssemblyExpr, _dependencyFiles) = getDetails()
        FSharpAssemblySignature(tcGlobals, thisCcu, tcImports, topAttribs, ccuSig)

    member info.AssemblyContents =  
        if not keepAssemblyContents then invalidOp "The 'keepAssemblyContents' flag must be set to tru on the FSharpChecker in order to access the checked contents of assemblies"
        let (tcGlobals, tcImports, thisCcu, _ccuSig, _tcSymbolUses, _topAttribs, _tcAssemblyData, _ilAssemRef, _ad, tcAssemblyExpr, _dependencyFiles) = getDetails()
        let mimpls = 
            match tcAssemblyExpr with 
            | None -> []
            | Some mimpls -> mimpls
        FSharpAssemblyContents(tcGlobals, thisCcu, tcImports, mimpls)

    member info.ProjectContext = 
        let (tcGlobals, tcImports, thisCcu, _ccuSig, _tcSymbolUses, _topAttribs, _tcAssemblyData, _ilAssemRef, ad, _tcAssemblyExpr, _dependencyFiles) = getDetails()
        let assemblies = 
            [ for x in tcImports.GetImportedAssemblies() do
                yield FSharpAssembly(tcGlobals, tcImports, x.FSharpViewOfMetadata) ]
        FSharpProjectContext(thisCcu, assemblies, ad)


[<Sealed>]
/// A live object of this type keeps the background corresponding background builder (and type providers) alive (through reference-counting).
//
// There is an important property of all the objects returned by the methods of this type: they do not require 
// the corresponding background builder to be alive. That is, they are simply plain-old-data through pre-formatting of all result text.
type FSharpCheckFileResults internal (errors: FSharpErrorInfo[], scopeOptX: TypeCheckInfo option, dependencyFiles: string list, builderX: option<_>, reactorOpsX:IReactorOperations) =

    // This may be None initially, or may be set to None when the object is disposed or finalized
    let mutable details = match scopeOptX with None -> None | Some scopeX -> Some (scopeX, builderX, reactorOpsX)

    // Run an operation that can be called from any thread
    let threadSafeOp dflt f = 
        match details with
        | None -> 
            dflt()
        // | Some (_ , Some builder, _) when not builder.IsAlive -> 
        //     System.Diagnostics.Debug.Assert(false,"unexpected dead builder") 
        //     dflt()
        | Some (scope, builderOpt, ops) -> 
            f(scope, builderOpt, ops)

    member info.Errors = errors

    member info.HasFullTypeCheckInfo = details.IsSome

    member info.PartialAssemblySignature = 
        threadSafeOp 
            (fun () -> failwith "not available") 
            (fun (scope, _builder, _reactor) -> 
            // This operation is not asynchronous - PartialAssemblySignature can be run on the calling thread
            scope.PartialAssemblySignature())


//-------------------------------------------------------------------------
// InteractiveChecker
//-------------------------------------------------------------------------
type InteractiveChecker(references: string list, readAllBytes: string -> byte[]) =
    
    //let references = ["mscorlib";"System";"System.Core";"System.Data";"System.IO";"System.Xml";"System.Numerics"]

    // load signature data
    let GetSignatureData ((filename:string), ilScopeRef, (ilModule:ILModuleDef option), (bytes:byte[])) : TastPickle.PickledDataWithReferences<PickledCcuInfo> = 
        TastPickle.unpickleObjWithDanglingCcus filename ilScopeRef ilModule TastPickle.unpickleCcuInfo bytes

    let tcConfig = TcConfig()
    let tcImports = TcImports()
    let ilGlobals = IL.EcmaMscorlibILGlobals

    let LoadMod ccuName =
        let fileName = ccuName + ".dll"
        let bytes = readAllBytes fileName
        let opts = ILBinaryReader.mkDefault ilGlobals
        let reader = ILBinaryReader.OpenILModuleReaderFromBytes fileName bytes opts
        reader.ILModuleDef //reader.ILAssemblyRefs

    let memoize_mod = new MemoizationTable<_,_> (LoadMod, keyComparer=HashIdentity.Structural)

    let LoadSig ccuName =
        let fileName = ccuName + ".sigdata"
        let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
        let ilModule = memoize_mod.Apply ccuName
        let bytes = readAllBytes fileName
        let data = GetSignatureData (fileName, ilScopeRef, Some ilModule, bytes)
        data

    let memoize_sig = new MemoizationTable<_,_> (LoadSig, keyComparer=HashIdentity.Structural)

    let GetCustomAttributesOfIlModule (ilModule:ILModuleDef) = 
        (match ilModule.Manifest with Some m -> m.CustomAttrs | None -> ilModule.CustomAttrs).AsList 

    let GetAutoOpenAttributes ilg ilModule = 
        ilModule |> GetCustomAttributesOfIlModule |> List.choose (TryFindAutoOpenAttr ilg)

    let GetInternalsVisibleToAttributes ilg ilModule = 
        ilModule |> GetCustomAttributesOfIlModule |> List.choose (TryFindInternalsVisibleToAttr ilg)
  
    let mkCcuInfo ilg ilScopeRef ilModule ccu =
          { ILScopeRef = ilScopeRef
            FSharpViewOfMetadata = ccu
            AssemblyAutoOpenAttributes = GetAutoOpenAttributes ilg ilModule
            AssemblyInternalsVisibleToAttributes = GetInternalsVisibleToAttributes ilg ilModule
#if EXTENSIONTYPING
            IsProviderGenerated = false
            TypeProviders = []
#endif
            FSharpOptimizationData = notlazy None }

    let GetCcuIL m ccuName =
        let auxModuleLoader = function
            | ILScopeRef.Local -> failwith "Unsupported reference"
            | ILScopeRef.Module x -> memoize_mod.Apply x.Name
            | ILScopeRef.Assembly x -> memoize_mod.Apply x.Name
        let ilModule = memoize_mod.Apply ccuName
        let fileName = ilModule.Name //ccuName + ".dll"
        let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
        let invalidateCcu = new Event<_>()
        let ccu = Import.ImportILAssembly(tcImports.GetImportMap,m,auxModuleLoader,ilScopeRef,tcConfig.implicitIncludeDir,Some fileName,ilModule,invalidateCcu.Publish)
        let ccuInfo = mkCcuInfo ilGlobals ilScopeRef ilModule ccu
        ccuInfo

    let rec GetCcuFS m sysCcus ccuName =
        let data = memoize_sig.Apply ccuName
        let ilModule = memoize_mod.Apply ccuName
        let fileName = ilModule.Name //ccuName + ".sigdata"
        let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)

        let GetRawTypeForwarders ilModule =
            match ilModule.Manifest with 
            | Some manifest -> manifest.ExportedTypes
            | None -> mkILExportedTypes []
#if EXTENSIONTYPING
        let invalidateCcu = new Event<_>()
#endif
        let minfo : PickledCcuInfo = data.RawData
        let codeDir = minfo.compileTimeWorkingDir
        let ccuData : CcuData = 
              { ILScopeRef = ilScopeRef
                Stamp = newStamp()
                FileName = Some fileName 
                QualifiedName = Some (ilScopeRef.QualifiedName)
                SourceCodeDirectory = codeDir
                IsFSharp = true
                Contents = minfo.mspec
#if EXTENSIONTYPING
                InvalidateEvent=invalidateCcu.Publish
                IsProviderGenerated = false
                ImportProvidedType = (fun ty -> Import.ImportProvidedType (tcImports.GetImportMap()) m ty)
#endif
                UsesFSharp20PlusQuotations = minfo.usesQuotations
                MemberSignatureEquality = (fun ty1 ty2 -> Tastops.typeEquivAux EraseAll (tcImports.GetTcGlobals()) ty1 ty2)
                TypeForwarders = Import.ImportILAssemblyTypeForwarders(tcImports.GetImportMap, m, GetRawTypeForwarders ilModule)
                }

        let ccu = CcuThunk.Create(ccuName, ccuData)
        let ccuInfo = mkCcuInfo ilGlobals ilScopeRef ilModule ccu
        let ccuInfos = [ccuInfo] @ sysCcus
        let findCcuInfo name = (ccuInfos |> List.find (fun x -> x.FSharpViewOfMetadata.AssemblyName = name)).FSharpViewOfMetadata
        let rawData = data.Fixup findCcuInfo
        ccuInfo

    let m = range.Zero
    let refCcus = references |> List.map (GetCcuIL m)
    let sysCcus = refCcus |> List.filter (fun x -> x.FSharpViewOfMetadata.AssemblyName <> "FSharp.Core")
    let sysCcu = sysCcus |> List.find (fun x -> x.FSharpViewOfMetadata.AssemblyName = "mscorlib")
    let fslibCcu = GetCcuFS m sysCcus "FSharp.Core"
    let ccuInfos = [fslibCcu] @ sysCcus
    let ccuMap = ccuInfos |> List.map (fun ccuInfo -> ccuInfo.FSharpViewOfMetadata.AssemblyName, ccuInfo) |> Map.ofList

    // search over all imported CCUs for each cached type
    let ccuHasType (ccu : CcuThunk) (nsname : string list) (tname : string) =
        match (Some ccu.Contents, nsname) ||> List.fold (fun entityOpt n -> match entityOpt with None -> None | Some entity -> entity.ModuleOrNamespaceType.AllEntitiesByCompiledAndLogicalMangledNames.TryFind n) with
        | Some ns ->
                match Map.tryFind tname ns.ModuleOrNamespaceType.TypesByMangledName with
                | Some _ -> true
                | None -> false
        | None -> false

    // Search for a type
    let tryFindSysTypeCcu nsname typeName =
        let search = sysCcus |> List.tryFind (fun ccuInfo -> ccuHasType ccuInfo.FSharpViewOfMetadata nsname typeName)
        match search with
        | Some x -> Some x.FSharpViewOfMetadata
        | None ->
            printfn "Cannot find type %s.%s" (String.concat "." nsname) typeName
            None

    let tcGlobals = TcGlobals(tcConfig.compilingFslib, ilGlobals, fslibCcu.FSharpViewOfMetadata,
                                tcConfig.implicitIncludeDir, tcConfig.mlCompatibility,
                                tcConfig.isInteractive, tryFindSysTypeCcu, tcConfig.emitDebugInfoInQuotations,
                                (tcConfig.primaryAssembly.Name = "mscorlib"), tcConfig.noDebugData )

    // let tcGlobals = TcGlobals (tcConfig.compilingFslib, sysCcu.FSharpViewOfMetadata, ilGlobals, fslibCcu.FSharpViewOfMetadata,
    //                              tcConfig.implicitIncludeDir, tcConfig.mlCompatibility, using40environment,
    //                              tcConfig.isInteractive, getTypeCcu, tcConfig.emitDebugInfoInQuotations)

#if DEBUG
    // the global_g reference cell is used only for debug printing
    do global_g := Some tcGlobals
#endif
    // do this prior to parsing, since parsing IL assembly code may refer to mscorlib
    do tcImports.SetCcuMap(ccuMap)
    do tcImports.SetTcGlobals(tcGlobals)

    let niceNameGen = NiceNameGenerator()
    let amap = tcImports.GetImportMap()
    let rng = rangeN Lexhelp.stdinMockFilename 0

    let assemblyName = "Project"
    let ccus = ccuInfos |> List.map (fun x -> x.FSharpViewOfMetadata, x.AssemblyAutoOpenAttributes, x.AssemblyInternalsVisibleToAttributes)
    let tcEnv = CreateInitialTcEnv (tcGlobals, amap, rng, assemblyName, ccus)
    let tcState = GetInitialTcState (rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, niceNameGen, tcEnv)
    let reactorOps = 
        { new IReactorOperations with 
                member __.EnqueueAndAwaitOpAsync (desc, op) = async.Return (op())
                member __.EnqueueOp (desc, op) = op() }

    member x.ParseScript (mainInputFileName, source) =
        //let mainInputFileName = "stdin.fsx" 
        // Note: projectSourceFiles is only used to compute isLastCompiland, and is ignored if Build.IsScript(mainInputFileName) is true (which it is in this case).
        let projectSourceFiles = []
        let parseErrors, _matchPairs, inputOpt, anyErrors =
            Parser.ParseOneFile (source, false, true, mainInputFileName, projectSourceFiles, tcConfig)
        let dependencyFiles = [] // interactions have no dependencies
        let parseResults = FSharpParseFileResults(parseErrors, inputOpt, parseHadErrors = anyErrors, dependencyFiles = dependencyFiles)
        parseResults

    member x.ParseAndCheckScript (mainInputFileName, source) =
         //let mainInputFileName = "stdin.fsx" 
         // Note: projectSourceFiles is only used to compute isLastCompiland, and is ignored if Build.IsScript(mainInputFileName) is true (which it is in this case).
         let projectSourceFiles = []
         let parseErrors, _matchPairs, inputOpt, anyErrors =
             Parser.ParseOneFile (source, false, true, mainInputFileName, projectSourceFiles, tcConfig)
         let dependencyFiles = [] // interactions have no dependencies
         let parseResults = FSharpParseFileResults(parseErrors, inputOpt, parseHadErrors = anyErrors, dependencyFiles = dependencyFiles)

         let backgroundErrors = []
         let tcResults =
            Parser.TypeCheckOneFile(parseResults,
                                     source,
                                     mainInputFileName,
                                     "project",
                                     tcConfig,
                                     tcGlobals,
                                     tcImports,
                                     tcState,
                                     //loadClosure,
                                     backgroundErrors,
                                     reactorOps,
                                     (fun () -> true),
                                     None)
            //|> Async.RunSynchronously

         match tcResults with 
         | tcErrors, Parser.TypeCheckAborted.No scope, tcImplFiles ->
             let errors = [|  yield! parseErrors; yield! tcErrors |]
             let typeCheckResults = FSharpCheckFileResults (errors, Some scope, dependencyFiles, None, reactorOps)   
             let projectResults = FSharpCheckProjectResults (true, errors, Some(tcGlobals, tcImports, scope.ThisCcu, scope.CcuSig, [scope.ScopeSymbolUses], None, None, mkSimpleAssRef "stdin", tcState.TcEnvFromImpls.AccessRights, Some tcImplFiles, dependencyFiles), reactorOps)
             parseResults, typeCheckResults, projectResults
         | _ -> 
             failwith "unexpected aborted"


module AstPrint =

    let attribsOfSymbol (s:FSharpSymbol) =
        let tryOr f def =
            try f() with _ -> def
        [ match s with
            | :? FSharpField as v ->
                yield "field"
                if v.IsCompilerGenerated then yield "compgen"
                if v.IsDefaultValue then yield "default"
                if v.IsMutable then yield "mutable"
                if v.IsVolatile then yield "volatile"
                if v.IsStatic then yield "static"
                if v.IsLiteral then yield sprintf "%A" v.LiteralValue.Value

            | :? FSharpEntity as v ->
                v.TryFullName |> ignore // check there is no failure here
                match v.BaseType with
                | Some t when t.HasTypeDefinition && t.TypeDefinition.TryFullName.IsSome ->
                    yield sprintf "inherits %s" t.TypeDefinition.FullName
                | _ -> ()
                if v.IsNamespace then yield "namespace"
                if v.IsFSharpModule then yield "module"
                if v.IsByRef then yield "byref"
                if v.IsClass then yield "class"
                if v.IsDelegate then yield "delegate"
                if v.IsEnum then yield "enum"
                if v.IsFSharpAbbreviation then yield "abbrev"
                if v.IsFSharpExceptionDeclaration then yield "exception"
                if v.IsFSharpRecord then yield "record"
                if v.IsFSharpUnion then yield "union"
                if v.IsInterface then yield "interface"
                if v.IsMeasure then yield "measure"
#if EXTENSIONTYPING
                if v.IsProvided then yield "provided"
                if v.IsStaticInstantiation then yield "static_inst"
                if v.IsProvidedAndErased then yield "erased"
                if v.IsProvidedAndGenerated then yield "generated"
#endif
                if v.IsUnresolved then yield "unresolved"
                if v.IsValueType then yield "valuetype"

            | :? FSharpMemberOrFunctionOrValue as v ->
                yield "owner: " + (tryOr (fun () -> v.EnclosingEntity.CompiledName) "<unknown>")
                if v.IsActivePattern then yield "active_pattern"
                if v.IsDispatchSlot then yield "dispatch_slot"
                if v.IsModuleValueOrMember && not v.IsMember then yield "val"
                if v.IsMember then yield "member"
                if v.IsProperty then yield "property"
                if v.IsExtensionMember then yield "extension_member"
                if v.IsPropertyGetterMethod then yield "property_getter"
                if v.IsPropertySetterMethod then yield "property_setter"
                if v.IsEvent then yield "event"
                if v.EventForFSharpProperty.IsSome then yield "property_event"
                if v.IsEventAddMethod then yield "event_add"
                if v.IsEventRemoveMethod then yield "event_remove"
                if v.IsTypeFunction then yield "type_func"
                if v.IsCompilerGenerated then yield "compiler_gen"
                if v.IsImplicitConstructor then yield "implicit_ctor"
                if v.IsMutable then yield "mutable"
                if v.IsOverrideOrExplicitInterfaceImplementation then yield "override_impl"
                if not v.IsInstanceMember then yield "static"
                if v.IsInstanceMember && not v.IsInstanceMemberInCompiledCode && not v.IsExtensionMember then yield "funky"
                if v.IsExplicitInterfaceImplementation then yield "interface_impl"
                yield sprintf "%A" v.InlineAnnotation
                // if v.IsConstructorThisValue then yield "ctorthis"
                // if v.IsMemberThisValue then yield "this"
                // if v.LiteralValue.IsSome then yield "literal"
            | _ -> () ]

    let rec printFSharpDecls prefix decls = seq {
        let mutable i = 0
        for decl in decls do
            i <- i + 1
            match decl with
            | FSharpImplementationFileDeclaration.Entity (e, sub) ->
                yield sprintf "%s%i) ENTITY: %s %A" prefix i e.CompiledName (attribsOfSymbol e)
                if not (Seq.isEmpty e.Attributes) then
                    yield sprintf "%sattributes: %A" prefix (Seq.toList e.Attributes)
                if not (Seq.isEmpty e.DeclaredInterfaces) then
                    yield sprintf "%sinterfaces: %A" prefix (Seq.toList e.DeclaredInterfaces)
                yield ""
                yield! printFSharpDecls (prefix + "\t") sub
            | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue (meth, args, body) ->
                yield sprintf "%s%i) METHOD: %s %A" prefix i meth.CompiledName (attribsOfSymbol meth)
                yield sprintf "%stype: %A" prefix meth.FullType
                yield sprintf "%sargs: %A" prefix args
                // if not meth.IsCompilerGenerated then
                yield sprintf "%sbody: %A" prefix body
                yield ""
            | FSharpImplementationFileDeclaration.InitAction (expr) ->
                yield sprintf "%s%i) ACTION" prefix i
                yield sprintf "%s%A" prefix expr
                yield ""
    }
