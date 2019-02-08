// Copyright (c) Microsoft Corporation.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

// Open up the compiler as an incremental service for parsing,
// type checking and intellisense-like environment-reporting.

namespace Microsoft.FSharp.Compiler.SourceCodeServices

#nowarn "1182"

open Internal.Utilities
open Internal.Utilities.Collections
open Microsoft.FSharp.Collections
open Microsoft.FSharp.Control

open System
open System.Text
open System.Threading
open System.Collections.Concurrent
open System.Collections.Generic

open Microsoft.FSharp.Compiler
open Microsoft.FSharp.Compiler.AbstractIL
open Microsoft.FSharp.Compiler.AbstractIL.IL
open Microsoft.FSharp.Compiler.AbstractIL.ILBinaryReader
open Microsoft.FSharp.Compiler.AbstractIL.Diagnostics
open Microsoft.FSharp.Compiler.AbstractIL.Internal
open Microsoft.FSharp.Compiler.AbstractIL.Internal.Library

open Microsoft.FSharp.Compiler.AccessibilityLogic
open Microsoft.FSharp.Compiler.Ast
open Microsoft.FSharp.Compiler.CompileOps
open Microsoft.FSharp.Compiler.CompileOptions
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


//-------------------------------------------------------------------------
// InteractiveChecker
//-------------------------------------------------------------------------

type internal TcResult = TcEnv * TopAttribs * TypedImplFile option * ModuleOrNamespaceType

type InteractiveChecker internal (tcConfig, tcGlobals, tcImports, tcInitialState, ctok, reactorOps, parseCache, checkCache) =
    let userOpName = "Unknown"

    static member Create(options: FSharpProjectOptions) =

        let getTcConfig () =
            let tcConfigB = TcConfigBuilder.Initial
            let sourceFiles = options.SourceFiles |> Array.toList
            let argv = options.OtherOptions |> Array.toList
            let _sourceFiles = ApplyCommandLineArgs(tcConfigB, sourceFiles, argv)
            TcConfig.Create(tcConfigB, validate=false)

        let ctok = CompilationThreadToken()
        let tcConfig = getTcConfig ()
        let tcConfigP = TcConfigProvider.Constant(tcConfig)

        let tcGlobals, tcImports =
            TcImports.BuildTcImports (ctok, tcConfigP)
            |> Cancellable.runWithoutCancellation

        let niceNameGen = NiceNameGenerator()
        let assemblyName = "Project"
        let tcInitialEnv = GetInitialTcEnv (assemblyName, rangeStartup, tcConfig, tcImports, tcGlobals)
        let tcInitialState = GetInitialTcState (rangeStartup, assemblyName, tcConfig, tcGlobals, tcImports, niceNameGen, tcInitialEnv)

        let reactorOps = 
            { new IReactorOperations with
                member __.EnqueueAndAwaitOpAsync (userOpName, opName, opArg, op) =
                    async.Return (Cancellable.runWithoutCancellation (op ctok))
                member __.EnqueueOp (userOpName, opName, opArg, op) = (op ctok) }

        // parse cache, keyed on file name and source hash
        let parseCache = ConcurrentDictionary<string * int, FSharpParseFileResults>(HashIdentity.Structural)
        // type check cache, keyed on file name
        let checkCache = ConcurrentDictionary<string, TcResult * (TcState * ModuleNamesDict)>(HashIdentity.Structural)

        InteractiveChecker (tcConfig, tcGlobals, tcImports, tcInitialState, ctok, reactorOps, parseCache, checkCache)

    member private x.MakeProjectResults (projectFileName: string, parseResults: FSharpParseFileResults[], tcState: TcState, errors: FSharpErrorInfo[],
                                         symbolUses: TcSymbolUses list, topAttrsOpt: TopAttribs option, tcImplFilesOpt: TypedImplFile list option) =
        let assemblyRef = mkSimpleAssemblyRef "stdin"
        let assemblyDataOpt = None
        let access = tcState.TcEnvFromImpls.AccessRights
        let dependencyFiles = parseResults |> Seq.map (fun x -> x.DependencyFiles) |> Array.concat
        let details = (tcGlobals, tcImports, tcState.Ccu, tcState.CcuSig, symbolUses, topAttrsOpt, assemblyDataOpt, assemblyRef, access, tcImplFilesOpt, dependencyFiles)
        let keepAssemblyContents = true
        FSharpCheckProjectResults (projectFileName, Some tcConfig, keepAssemblyContents, errors, Some details)

    member private x.ClearStaleCache (fileName: string, parsingOptions: FSharpParsingOptions) =
        let fileIndex = parsingOptions.SourceFiles |> Array.findIndex ((=) fileName)
        let filesAbove = parsingOptions.SourceFiles |> Array.take fileIndex
        // backup all cached typecheck entries above file
        let cachedAbove = filesAbove |> Array.choose (fun key ->
            match checkCache.TryGetValue(key) with
            | true, value -> Some (key, value)
            | false, _ -> None)
        // remove all parse cache entries with the same file name
        let staleParseKeys = parseCache.Keys |> Seq.filter (fun (n,_) -> n = fileName) |> Seq.toArray
        staleParseKeys |> Array.iter (fun key -> parseCache.TryRemove(key) |> ignore)
        checkCache.Clear(); // clear all typecheck cache
        // restore all cached typecheck entries above file
        cachedAbove |> Array.iter (fun (key, value) -> checkCache.TryAdd(key, value) |> ignore)

    member private x.ParseFile (fileName: string, sourceHash: int, source: Lazy<string>, parsingOptions: FSharpParsingOptions) =
        let parseCacheKey = fileName, sourceHash
        parseCache.GetOrAdd(parseCacheKey, fun _ ->
            x.ClearStaleCache(fileName, parsingOptions)
            let parseErrors, parseTreeOpt, anyErrors = Parser.parseFile (source.Value, fileName, parsingOptions, userOpName)

    member private x.CheckFile (projectFileName: string, parseResults: FSharpParseFileResults, tcState: TcState, moduleNamesDict: ModuleNamesDict) =
        match parseResults.ParseTree with
        | Some input ->
            let capturingErrorLogger = CompilationErrorLogger("TypeCheckFile", tcConfig.errorSeverityOptions)
            let errorLogger = GetErrorLoggerFilteringByScopedPragmas(false, GetScopedPragmasForInput(input), capturingErrorLogger)
            use _errorScope = new CompilationGlobalsScope (errorLogger, BuildPhase.TypeCheck)

            let sink = TcResultsSinkImpl(tcGlobals)
            let tcSink = TcResultsSink.WithSink sink
            let checkForErrors () = parseResults.ParseHadErrors || errorLogger.ErrorCount > 0
            let prefixPathOpt = None

            let input, moduleNamesDict = input |> DeduplicateParsedInputModuleName moduleNamesDict
            let (tcEnvAtEnd, topAttrs, implFile, ccuSigForFile), tcState =
                TypeCheckOneInputEventually (checkForErrors, tcConfig, tcImports, tcGlobals, prefixPathOpt, tcSink, tcState, input)
                |> Eventually.force ctok

            let fileName = parseResults.FileName
            checkCache.[fileName] <- ((tcEnvAtEnd, topAttrs, implFile, ccuSigForFile), (tcState, moduleNamesDict))

            let loadClosure = None
            let checkAlive () = true
            let textSnapshotInfo = None
            let keepAssemblyContents = true

            let tcErrors = ErrorHelpers.CreateErrorInfos (tcConfig.errorSeverityOptions, false, fileName, (capturingErrorLogger.GetErrors()))
            let errors = Array.append parseResults.Errors tcErrors

            let scope = TypeCheckInfo (tcConfig, tcGlobals, ccuSigForFile, tcState.Ccu, tcImports, tcEnvAtEnd.AccessRights,
                                    projectFileName, fileName, sink.GetResolutions(), sink.GetSymbolUses(), tcEnvAtEnd.NameEnv,
                                    loadClosure, reactorOps, checkAlive, textSnapshotInfo, implFile, sink.GetOpenDeclarations())
            FSharpCheckFileResults (fileName, errors, Some scope, parseResults.DependencyFiles, None, reactorOps, keepAssemblyContents)
            |> Some
        | None ->
            None

    member private x.TypeCheckClosedInputSet (ctok, checkForErrors, tcConfig, tcImports, tcGlobals, prefixPathOpt, tcState, inputs) =
        let fileNameOf = function
            | ParsedInput.SigFile (ParsedSigFileInput(fileName,_,_,_,_)) -> fileName
            | ParsedInput.ImplFile (ParsedImplFileInput(fileName,_,_,_,_,_,_)) -> fileName
        let cachedTypeCheck (tcState, moduleNamesDict) (input: ParsedInput) =
            let checkCacheKey = fileNameOf input
            let typeCheckOneInput _fileName =
                let input, moduleNamesDict = input |> DeduplicateParsedInputModuleName moduleNamesDict
                let tcResults, tcState =
                    use unwindEL = PushErrorLoggerPhaseUntilUnwind(fun oldLogger -> GetErrorLoggerFilteringByScopedPragmas(false, GetScopedPragmasForInput(input), oldLogger) )
                    use unwindBP = PushThreadBuildPhaseUntilUnwind BuildPhase.TypeCheck
                    TypeCheckOneInputEventually (checkForErrors, tcConfig, tcImports, tcGlobals, prefixPathOpt, TcResultsSink.NoSink, tcState, input)
                    |> Eventually.force ctok
                tcResults, (tcState, moduleNamesDict)
            checkCache.GetOrAdd(checkCacheKey, typeCheckOneInput)
        let results, (tcState, moduleNamesDict) =
            ((tcState, Map.empty), inputs) ||> List.mapFold cachedTypeCheck
        let (tcEnvAtEndOfLastFile, topAttrs, implFiles, _ccuSigsForFiles), tcState =
            TypeCheckMultipleInputsFinish(results, tcState)
        let tcState, declaredImpls = TypeCheckClosedInputSetFinish (implFiles, tcState)
        tcState, topAttrs, declaredImpls, tcEnvAtEndOfLastFile, moduleNamesDict

    /// Errors grouped by file, sorted by line, column
    member private x.ErrorsByFile (fileNames: string[], errorList: FSharpErrorInfo[] list) =
        let errorMap = errorList |> Array.concat |> Array.groupBy (fun x -> x.FileName) |> Map.ofArray
        let errors = fileNames |> Array.choose errorMap.TryFind
        errors |> Array.iter (Array.sortInPlaceBy (fun x -> x.StartLineAlternate, x.StartColumn))
        errors |> Array.concat

    /// Clears parse and typecheck caches.
    member x.ClearCache () =
        parseCache.Clear()
        checkCache.Clear()

    /// Parses and checks the whole project, good for compilers (Fable etc.)
    /// Does not retain name resolutions and symbol uses which are quite memory hungry (so no intellisense etc.).
    /// Already parsed files will be cached so subsequent compilations will be faster.
    member x.ParseAndCheckProject (projectFileName: string, fileNames: string[], sourceReader: string->int*Lazy<string>) =
        // parse files
        let parsingOptions = FSharpParsingOptions.FromTcConfig(tcConfig, fileNames, false)
        let parseResults = fileNames |> Array.map (fun fileName ->
            let sourceHash, source = sourceReader fileName
            x.ParseFile(fileName, sourceHash, source, parsingOptions))
        let parseHadErrors = parseResults |> Array.exists (fun p -> p.ParseHadErrors)
        let parsedInputs = parseResults |> Array.choose (fun p -> p.ParseTree) |> Array.toList

        // type check files
        use errorScope = new ErrorScope()
        let hasTypedErrors () = errorScope.Diagnostics |> List.exists (fun e -> e.Severity = FSharpErrorSeverity.Error)
        let checkForErrors () = parseHadErrors || hasTypedErrors ()
        let prefixPathOpt = None
        let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, _moduleNamesDict =
            x.TypeCheckClosedInputSet (ctok, checkForErrors, tcConfig, tcImports, tcGlobals, prefixPathOpt, tcInitialState, parsedInputs)

        // make project results
        let parseErrors = parseResults |> Array.collect (fun p -> p.Errors)
        let typedErrors = errorScope.Diagnostics |> List.toArray
        let errors = x.ErrorsByFile (fileNames, [ parseErrors; typedErrors ])
        let symbolUses = [] //TODO:
        let projectResults = x.MakeProjectResults (projectFileName, parseResults, tcState, errors, symbolUses, Some topAttrs, Some tcImplFiles)

        projectResults

    /// Parses and checks file in project, will compile and cache all the files up to this one
    /// (if not already done before), or fetch them from cache. Returns partial project results,
    /// up to and including the file requested. Returns parse and typecheck results containing
    /// name resolutions and symbol uses for the file requested only, so intellisense etc. works.
    member x.ParseAndCheckFileInProject (fileName: string, projectFileName: string, fileNames: string[], sources: string[]) =
        // get files before file
        let fileIndex = fileNames |> Array.findIndex ((=) fileName)
        let fileNamesBeforeFile = fileNames |> Array.take fileIndex
        let sourcesBeforeFile = sources |> Array.take fileIndex

        // parse files before file
        let parsingOptions = FSharpParsingOptions.FromTcConfig(tcConfig, fileNames, false)
        let parseFile (fileName, source) = x.ParseFile (fileName, hash source, lazy source, parsingOptions)
        let parseResults = Array.zip fileNamesBeforeFile sourcesBeforeFile |> Array.map parseFile
        let parseHadErrors = parseResults |> Array.exists (fun p -> p.ParseHadErrors)
        let parsedInputs = parseResults |> Array.choose (fun p -> p.ParseTree) |> Array.toList

        // type check files before file
        use errorScope = new ErrorScope()
        let hasTypedErrors () = errorScope.Diagnostics |> List.exists (fun e -> e.Severity = FSharpErrorSeverity.Error)
        let checkForErrors () = parseHadErrors || hasTypedErrors ()
        let prefixPathOpt = None
        let tcState, topAttrs, tcImplFiles, _tcEnvAtEnd, moduleNamesDict =
            x.TypeCheckClosedInputSet (ctok, checkForErrors, tcConfig, tcImports, tcGlobals, prefixPathOpt, tcInitialState, parsedInputs)

        // parse and type check file
        let parseFileResults = parseFile (fileName, sources.[fileIndex])
        let checkFileResults = x.CheckFile (projectFileName, parseFileResults, tcState, moduleNamesDict)
        let (_tcEnvAtEndFile, topAttrsFile, implFile, _ccuSigForFile), (tcState, _moduleNamesDict) =
            checkCache.[fileName]

        // collect errors
        let parseErrorsBefore = parseResults |> Array.collect (fun p -> p.Errors)
        let typedErrorsBefore = errorScope.Diagnostics |> List.toArray
        let newErrors = match checkFileResults with | Some res -> res.Errors | None -> [||]
        let errors = x.ErrorsByFile (fileNames, [ parseErrorsBefore; typedErrorsBefore; newErrors ])

        // make partial project results
        let parseResults = Array.append parseResults [| parseFileResults |]
        let tcImplFiles = List.append tcImplFiles (Option.toList implFile)
        let topAttrs = CombineTopAttrs topAttrsFile topAttrs
        let symbolUses = [] //TODO:
        let projectResults = x.MakeProjectResults (projectFileName, parseResults, tcState, errors, symbolUses, Some topAttrs, Some tcImplFiles)

        parseFileResults, checkFileResults, projectResults
