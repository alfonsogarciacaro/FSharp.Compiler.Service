module App
open Microsoft.FSharp.Compiler.SourceCodeServices

#if DOTNETCORE || DOTNET40
[<EntryPoint>]
#endif
let main argv =
    ignore argv
    printfn "Parsing begins..."

    let source = """
let test() =
    let a = 1
    let b = 2
    a + b
printfn "answer: %A" (test())
"""

    let metadataPath = "/temp/metadata/"
#if DOTNETCORE
    let references =
      [ "mscorlib"
        "System.Collections"
        "System.Console"
        "System.Diagnostics.Debug"
        "System.Globalization"
        "System.IO"
        "System.Linq"
        "System.Linq.Expressions"
        "System.Net.Requests"
        "System.ObjectModel"
        "System.Reflection"
        "System.Reflection.Primitives"
        "System.Resources.ResourceManager"
        "System.Runtime"
        "System.Runtime.InteropServices"
        "System.Runtime.Numerics"
        "System.Threading"
        "System.Threading.Tasks"
        "System.Xml.XDocument"
    ]
#else
    let references = ["mscorlib";"System";"System.Core";"System.Data";"System.IO";"System.Xml";"System.Numerics"]
#endif

#if DOTNETCORE || DOTNET40
    let readAllBytes = fun (fileName:string) -> System.IO.File.ReadAllBytes (metadataPath + fileName)
#else
    let readFileSync: System.Func<string, byte[]> = Fable.Core.JsInterop.import "readFileSync" "fs"
    let readAllBytes = fun (fileName:string) -> readFileSync.Invoke (metadataPath + fileName)
#endif

    let fileName = "stdin.fsx"
    let checker = InteractiveChecker(references, readAllBytes)
    // let untypedResults = checker.ParseScript(fileName,source)
    let untypedResults, typeCheckResults, projectResults = checker.ParseAndCheckScript(fileName,source)
    
    printfn "untypedResults.ParseHadErrors: %A" untypedResults.ParseHadErrors
    printfn "untypedResults.Errors: %A" untypedResults.Errors
    //printfn "untypedResults.ParseTree: %A" untypedResults.ParseTree
    
    printfn "typeCheckResults Errors: %A" typeCheckResults.Errors
    printfn "typeCheckResults Entities: %A" typeCheckResults.PartialAssemblySignature.Entities
    //printfn "typeCheckResults Attributes: %A" typeCheckResults.PartialAssemblySignature.Attributes

    printfn "projectResults Errors: %A" projectResults.Errors
    printfn "projectResults Contents: %A" projectResults.AssemblyContents

    printfn "Typed AST:"
    projectResults.AssemblyContents.ImplementationFiles
    |> Seq.iter (fun file -> AstPrint.printFSharpDecls "" file.Declarations |> Seq.iter (printfn "%s"))

    0 // return an integer exit code
