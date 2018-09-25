module App
open Microsoft.FSharp.Compiler
open Microsoft.FSharp.Compiler.SourceCodeServices

let use_net45_meta = false
let references = Metadata.references use_net45_meta
let metadataPath =
    if use_net45_meta
    then "/temp/repl/metadata/"  // dotnet 4.5 binaries
    else "/temp/repl/metadata2/" // dotnet core 2.0 binaries

#if !DOTNET_FILE_SYSTEM

let readFileSync: System.Func<string, byte[]> = Fable.Core.JsInterop.import "readFileSync" "fs"
let readTextSync: System.Func<string, string, string> = Fable.Core.JsInterop.import "readFileSync" "fs"

let readAllBytes = fun (fileName:string) -> readFileSync.Invoke (metadataPath + fileName)
let readAllText = fun (filePath:string) -> readTextSync.Invoke (filePath, "utf8")

#else // DOTNET_FILE_SYSTEM

let readAllBytes = fun (fileName:string) -> System.IO.File.ReadAllBytes (metadataPath + fileName)
let readAllText = fun (filePath:string) -> System.IO.File.ReadAllText (filePath, System.Text.Encoding.UTF8)

#endif


[<EntryPoint>]
let main argv =
    printfn "Parsing begins..."

    let checker = InteractiveChecker.Create(references, readAllBytes)

    let fileName = "test_script.fsx"
    let source = readAllText fileName

    // let parseResults = checker.ParseScript(fileName,source)
    let parseResults, typeCheckResults, projectResults = checker.ParseAndCheckScript(fileName, source)
    
    printfn "parseResults.ParseHadErrors: %A" parseResults.ParseHadErrors
    printfn "parseResults.Errors: %A" parseResults.Errors
    //printfn "parseResults.ParseTree: %A" parseResults.ParseTree
    
    printfn "typeCheckResults Errors: %A" typeCheckResults.Errors
    printfn "typeCheckResults Entities: %A" typeCheckResults.PartialAssemblySignature.Entities
    //printfn "typeCheckResults Attributes: %A" typeCheckResults.PartialAssemblySignature.Attributes

    printfn "projectResults Errors: %A" projectResults.Errors
    //printfn "projectResults Contents: %A" projectResults.AssemblyContents

    printfn "Typed AST (unoptimized):"
    projectResults.AssemblyContents.ImplementationFiles
    |> Seq.iter (fun file -> AstPrint.printFSharpDecls "" file.Declarations |> Seq.iter (printfn "%s"))

    printfn "Typed AST (optimized):"
    projectResults.GetOptimizedAssemblyContents().ImplementationFiles
    |> Seq.iter (fun file -> AstPrint.printFSharpDecls "" file.Declarations |> Seq.iter (printfn "%s"))

    let inputLines = source.Split('\n')

    async {
        // Get tool tip at the specified location
        let! tip = typeCheckResults.GetToolTipText(4, 7, inputLines.[3], ["foo"], FSharpTokenTag.IDENT)
        (sprintf "%A" tip).Replace("\n","") |> printfn "\n---> ToolTip Text = %A" // should be "FSharpToolTipText [...]"

        // Get declarations (autocomplete) for msg
        let partialName = { QualifyingIdents = []; PartialIdent = "msg"; EndColumn = 17; LastDotPos = None }
        let! decls = typeCheckResults.GetDeclarationListInfo(Some parseResults, 6, inputLines.[5], partialName, (fun _ -> []), fun _ -> false)
        [ for item in decls.Items -> item.Name ] |> printfn "\n---> msg AutoComplete = %A" // should be string methods

        // Get declarations (autocomplete) for canvas
        let partialName = { QualifyingIdents = []; PartialIdent = "canvas"; EndColumn = 10; LastDotPos = None }
        let! decls = typeCheckResults.GetDeclarationListInfo(Some parseResults, 8, inputLines.[7], partialName, (fun _ -> []), fun _ -> false)
        [ for item in decls.Items -> item.Name ] |> printfn "\n---> canvas AutoComplete = %A"
    } |> Async.StartImmediate

    0
