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

type InteractiveChecker internal (tcConfig, tcGlobals, tcImports, tcState, ctok, reactorOps) =

    static member Create(references: string[], readAllBytes: string -> byte[]) =

        let GetSignatureData ((filename:string), ilScopeRef, (ilModule:ILModuleDef option), (bytes:byte[])) = 
            TastPickle.unpickleObjWithDanglingCcus filename ilScopeRef ilModule TastPickle.unpickleCcuInfo bytes
        let GetOptimizationData ((filename:string), ilScopeRef, (ilModule:ILModuleDef option), (bytes:byte[])) = 
            TastPickle.unpickleObjWithDanglingCcus filename ilScopeRef ilModule Optimizer.u_CcuOptimizationInfo bytes

        let tcConfig = TcConfig (optimize = true)
        let tcImports = TcImports ()
        let ilGlobals = IL.EcmaMscorlibILGlobals

        let sigDataReaders ilModule =
            [ for resource in ilModule.Resources.AsList do
                if IsSignatureDataResource resource then 
                    let ccuName = GetSignatureDataResourceName resource
                    yield resource.GetBytes() ]

        let optDataReaders ilModule =
            [ for resource in ilModule.Resources.AsList do
                if IsOptimizationDataResource resource then
                    let ccuName = GetOptimizationDataResourceName resource
                    yield resource.GetBytes() ]

        let LoadMod ccuName =
            let fileName = ccuName + ".dll"
            let bytes = readAllBytes fileName
            let opts : ILReaderOptions =
                  { ilGlobals = ilGlobals
                    metadataOnly = MetadataOnlyFlag.Yes
                    reduceMemoryUsage = ReduceMemoryFlag.Yes
                    pdbDirPath = None
                    tryGetMetadataSnapshot = (fun _ -> None) }

            let reader = ILBinaryReader.OpenILModuleReaderFromBytes fileName bytes opts
            reader.ILModuleDef //reader.ILAssemblyRefs

        let memoize_mod = new MemoizationTable<_,_> (LoadMod, keyComparer=HashIdentity.Structural)

        let LoadSigData ccuName =
            let fileName = ccuName + ".dll" // ccuName + ".sigdata"
            let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
            let ilModule = memoize_mod.Apply ccuName
            match sigDataReaders ilModule with
            | [] -> None
            | bytes::_ -> Some (GetSignatureData (fileName, ilScopeRef, Some ilModule, bytes))

        let LoadOptData ccuName =
            let fileName = ccuName + ".dll" // ccuName + ".optdata"
            let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
            let ilModule = memoize_mod.Apply ccuName
            match optDataReaders ilModule with
            | [] -> None
            | bytes::_ -> Some (GetOptimizationData (fileName, ilScopeRef, Some ilModule, bytes))

        let memoize_sig = new MemoizationTable<_,_> (LoadSigData, keyComparer=HashIdentity.Structural)
        let memoize_opt = new MemoizationTable<_,_> (LoadOptData, keyComparer=HashIdentity.Structural)

        let GetCustomAttributesOfIlModule (ilModule:ILModuleDef) = 
            (match ilModule.Manifest with Some m -> m.CustomAttrs | None -> ilModule.CustomAttrs).AsList 

        let GetAutoOpenAttributes ilg ilModule = 
            ilModule |> GetCustomAttributesOfIlModule |> List.choose (TryFindAutoOpenAttr ilg)

        let GetInternalsVisibleToAttributes ilg ilModule = 
            ilModule |> GetCustomAttributesOfIlModule |> List.choose (TryFindInternalsVisibleToAttr ilg)

        let HasAnyFSharpSignatureDataAttribute ilModule = 
            let attrs = GetCustomAttributesOfIlModule ilModule
            List.exists IsSignatureDataVersionAttr attrs

        let mkCcuInfo ilg ilScopeRef ilModule ccu =
              { ILScopeRef = ilScopeRef
                FSharpViewOfMetadata = ccu
                AssemblyAutoOpenAttributes = GetAutoOpenAttributes ilg ilModule
                AssemblyInternalsVisibleToAttributes = GetInternalsVisibleToAttributes ilg ilModule
#if !NO_EXTENSIONTYPING
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
            let fileName = ilModule.Name
            let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
            let invalidateCcu = new Event<_>()
            let ccu = Import.ImportILAssembly(tcImports.GetImportMap,m,auxModuleLoader,ilScopeRef,tcConfig.implicitIncludeDir,Some fileName,ilModule,invalidateCcu.Publish)
            let ccuInfo = mkCcuInfo ilGlobals ilScopeRef ilModule ccu
            ccuInfo, None

        let GetCcuFS m ccuName =
            let sigdata = memoize_sig.Apply ccuName
            let ilModule = memoize_mod.Apply ccuName
            let fileName = ilModule.Name
            let ilScopeRef = ILScopeRef.Assembly (mkSimpleAssRef ccuName)
            let GetRawTypeForwarders ilModule =
                match ilModule.Manifest with 
                | Some manifest -> manifest.ExportedTypes
                | None -> mkILExportedTypes []
#if !NO_EXTENSIONTYPING
            let invalidateCcu = new Event<_>()
#endif
            let minfo : PickledCcuInfo = sigdata.Value.RawData //TODO: handle missing sigdata
            let codeDir = minfo.compileTimeWorkingDir
            let ccuData : CcuData = 
                  { ILScopeRef = ilScopeRef
                    Stamp = newStamp()
                    FileName = Some fileName 
                    QualifiedName = Some (ilScopeRef.QualifiedName)
                    SourceCodeDirectory = codeDir
                    IsFSharp = true
                    Contents = minfo.mspec
#if !NO_EXTENSIONTYPING
                    InvalidateEvent=invalidateCcu.Publish
                    IsProviderGenerated = false
                    ImportProvidedType = (fun ty -> Import.ImportProvidedType (tcImports.GetImportMap()) m ty)
#endif
                    UsesFSharp20PlusQuotations = minfo.usesQuotations
                    MemberSignatureEquality = (fun ty1 ty2 -> Tastops.typeEquivAux EraseAll (tcImports.GetTcGlobals()) ty1 ty2)
                    TryGetILModuleDef = (fun () -> Some ilModule)
                    TypeForwarders = Import.ImportILAssemblyTypeForwarders(tcImports.GetImportMap, m, GetRawTypeForwarders ilModule)
                    }

            let optdata = lazy (
                match memoize_opt.Apply ccuName with 
                | None -> None
                | Some data ->
                    let findCcuInfo name = tcImports.FindCcu (m, name)
                    Some (data.OptionalFixup findCcuInfo) )

            let ccu = CcuThunk.Create(ccuName, ccuData)
            let ccuInfo = mkCcuInfo ilGlobals ilScopeRef ilModule ccu
            let ccuOptInfo = { ccuInfo with FSharpOptimizationData = optdata }
            ccuOptInfo, sigdata

        let rec GetCcu m ccuName =
            let ilModule = memoize_mod.Apply ccuName
            if HasAnyFSharpSignatureDataAttribute ilModule then
                GetCcuFS m ccuName
            else
                GetCcuIL m ccuName

        let fixupCcuInfo refCcusUnfixed =
            let refCcus = refCcusUnfixed |> List.map fst
            let findCcuInfo name =
                refCcus
                |> List.tryFind (fun x -> x.FSharpViewOfMetadata.AssemblyName = name)
                |> Option.map (fun x -> x.FSharpViewOfMetadata)
            let fixup (data: TastPickle.PickledDataWithReferences<_>) =
                data.OptionalFixup findCcuInfo |> ignore
            refCcusUnfixed |> List.choose snd |> List.iter fixup
            refCcus

        let m = range.Zero
        let refCcusUnfixed = List.ofArray references |> List.map (GetCcu m)
        let refCcus = fixupCcuInfo refCcusUnfixed
        let sysCcus = refCcus |> List.filter (fun x -> x.FSharpViewOfMetadata.AssemblyName <> "FSharp.Core")
        let fslibCcu = refCcus |> List.find (fun x -> x.FSharpViewOfMetadata.AssemblyName = "FSharp.Core")

        let ccuInfos = [fslibCcu] @ sysCcus
        let ccuMap = ccuInfos |> List.map (fun ccuInfo -> ccuInfo.FSharpViewOfMetadata.AssemblyName, ccuInfo) |> Map.ofList

        // search over all imported CCUs for each cached type
        let ccuHasType (ccu: CcuThunk) (nsname: string list) (tname: string) =
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

        let tcGlobals = TcGlobals (
                            tcConfig.compilingFslib, ilGlobals, fslibCcu.FSharpViewOfMetadata,
                            tcConfig.implicitIncludeDir, tcConfig.mlCompatibility,
                            tcConfig.isInteractive, tryFindSysTypeCcu,
                            tcConfig.emitDebugInfoInQuotations, tcConfig.noDebugData)

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
        let ctok = CompilationThreadToken()

        let reactorOps = 
            { new IReactorOperations with
                member __.EnqueueAndAwaitOpAsync (userOpName, opName, opArg, op) =
                    async.Return (Cancellable.runWithoutCancellation (op ctok))
                member __.EnqueueOp (userOpName, opName, opArg, op) = (op ctok) }

        InteractiveChecker (tcConfig, tcGlobals, tcImports, tcState, ctok, reactorOps)

    member x.ParseScript (mainInputFileName, source) =
        let userOpName = "Unknown"
        let filename = mainInputFileName
        // Note: projectSourceFiles is only used to compute isLastCompiland, and is ignored if Build.IsScript(mainInputFileName) is true (which it is in this case).
        let parsingOptions = FSharpParsingOptions.FromTcConfig(tcConfig, [| filename |], false)
        let parseErrors, inputOpt, anyErrors = Parser.parseFile (source, filename, parsingOptions, userOpName)
        let dependencyFiles = [||] // interactions have no dependencies
        let parseResults = FSharpParseFileResults(parseErrors, inputOpt, parseHadErrors = anyErrors, dependencyFiles = dependencyFiles)
        parseResults

    member x.ParseAndCheckScript (mainInputFileName, source) =
        let parseResults = x.ParseScript (mainInputFileName, source)
        let loadClosure = None
        let backgroundErrors = [||]
        let tcResults =
            Parser.CheckOneFile(parseResults,
                                source,
                                mainInputFileName,
                                "project",
                                tcConfig,
                                tcGlobals,
                                tcImports,
                                tcState,
                                loadClosure,
                                backgroundErrors,
                                reactorOps,
                                (fun () -> true),
                                None,
                                "")

        match tcResults with 
        | tcErrors, Parser.TypeCheckAborted.No scope ->
            let errors = [|  yield! parseResults.Errors; yield! tcErrors |]
            let tcImplFiles = match scope.ImplementationFile with Some x -> Some [x] | None -> None
            let typeCheckResults = FSharpCheckFileResults (mainInputFileName, errors, Some scope, parseResults.DependencyFiles, None, reactorOps, true)   
            let projectResults = FSharpCheckProjectResults (mainInputFileName, Some tcConfig, true, errors, Some(tcGlobals, tcImports, scope.ThisCcu, scope.CcuSigForFile, [scope.ScopeSymbolUses], None, None, mkSimpleAssRef "stdin", tcState.TcEnvFromImpls.AccessRights, tcImplFiles, parseResults.DependencyFiles))
            parseResults, typeCheckResults, projectResults
        | _ -> 
            failwith "unexpected aborted"
