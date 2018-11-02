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
open Fable.Core

let readFileSync: System.Func<string, byte[]> = JsInterop.import "readFileSync" "fs"
let readTextSync: System.Func<string, string, string> = JsInterop.import "readFileSync" "fs"
let writeTextSync: System.Action<string, string> = JsInterop.import "writeFileSync" "fs"

let readAllBytes = fun (fileName:string) -> readFileSync.Invoke (metadataPath + fileName)
let readAllText = fun (filePath:string) -> readTextSync.Invoke (filePath, "utf8")
let writeAllText (filePath:string) (text:string) = writeTextSync.Invoke (filePath, text)

#else // DOTNET_FILE_SYSTEM
open System.IO

let readAllBytes = fun (fileName:string) -> File.ReadAllBytes (metadataPath + fileName)
let readAllText = fun (filePath:string) -> File.ReadAllText (filePath, System.Text.Encoding.UTF8)
let writeAllText (filePath:string) (text:string) = File.WriteAllText (filePath, text)

#endif


[<EntryPoint>]
let main argv =
    printfn "Parsing begins..."

    let defines = [||]
    let checker = InteractiveChecker.Create(references, readAllBytes, defines)

    let projectFileName = "project"
    let fileName = "test_script.fsx"
    let source = readAllText fileName

    //let parseResults, typeCheckResults, projectResults = checker.ParseAndCheckProject(projectFileName, [|fileName|], [|source|])
    let parseResults, typeCheckResults, projectResults = checker.ParseAndCheckScript(projectFileName, fileName, source)
    
    printfn "parseResults.ParseHadErrors: %A" parseResults.ParseHadErrors
    printfn "parseResults.Errors: %A" parseResults.Errors
    //printfn "parseResults.ParseTree: %A" parseResults.ParseTree
    
    printfn "typeCheckResults Errors: %A" typeCheckResults.Errors
    printfn "typeCheckResults Entities: %A" typeCheckResults.PartialAssemblySignature.Entities
    //printfn "typeCheckResults Attributes: %A" typeCheckResults.PartialAssemblySignature.Attributes

    printfn "projectResults Errors: %A" projectResults.Errors
    //printfn "projectResults Contents: %A" projectResults.AssemblyContents

    printfn "Typed AST (unoptimized):"
    let unoptimizedDecls = 
        projectResults.AssemblyContents.ImplementationFiles
        |> Seq.collect (fun file -> AstPrint.printFSharpDecls "" file.Declarations)
        |> String.concat "\n"
    unoptimizedDecls |> printfn "%s"
    //writeAllText (fileName + ".unoptimized.ast.txt") unoptimizedDecls

    printfn "Typed AST (optimized):"
    let optimizedDecls = 
        projectResults.GetOptimizedAssemblyContents().ImplementationFiles
        |> Seq.collect (fun file -> AstPrint.printFSharpDecls "" file.Declarations)
        |> String.concat "\n"
    optimizedDecls |> printfn "%s"
    //writeAllText (fileName + ".optimized.ast.txt") optimizedDecls

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
