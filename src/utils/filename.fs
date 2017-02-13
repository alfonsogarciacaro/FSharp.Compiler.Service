// Copyright (c) Microsoft Corporation.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

module internal Internal.Utilities.Filename

#if FABLE_COMPILER
open Internal.Utilities
#endif
open System.IO
open Microsoft.FSharp.Compiler.AbstractIL.Internal.Library 

exception IllegalFileNameChar of string * char

let checkPathForIllegalChars  =
#if FABLE_COMPILER
    let invalidChars = Seq.toArray "<>|\"\b\0\t" //TODO: add more
#else
    let invalidChars = Path.GetInvalidPathChars ()
#endif
    let chars = new System.Collections.Generic.HashSet<_>(invalidChars |> Array.toSeq)
    (fun (path:string) -> 
        for c in path do
            if chars.Contains c then raise(IllegalFileNameChar(path, c)))

// Case sensitive (original behaviour preserved).
let checkSuffix (x:string) (y:string) = x.EndsWith(y,System.StringComparison.Ordinal) 

let hasExtensionWithValidate (validate:bool) (s:string) = 
    if validate then (checkPathForIllegalChars s) |> ignore
    let sLen = s.Length
    (sLen >= 1 && s.[sLen - 1] = '.' && s <> ".." && s <> ".") 
#if FABLE_COMPILER
    //TODO: proper implementation
#else
    || Path.HasExtension(s)
#endif

let hasExtension (s:string) = hasExtensionWithValidate true s

let chopExtension (s:string) =
    checkPathForIllegalChars s
    if s = "." then "" else // for OCaml compatibility
    if not (hasExtensionWithValidate false s) then 
        raise (System.ArgumentException("chopExtension")) // message has to be precisely this, for OCaml compatibility, and no argument name can be set
#if FABLE_COMPILER
    s //TODO: proper implementation
#else
    Path.Combine (Path.GetDirectoryName s,Path.GetFileNameWithoutExtension(s))
#endif

let directoryName (s:string) = 
    checkPathForIllegalChars s
    if s = "" then "."
    else 
#if FABLE_COMPILER
        s //TODO: proper implementation
#else
        match Path.GetDirectoryName(s) with 
        | null -> if FileSystem.IsPathRootedShim(s) then s else "."
        | res -> if res = "" then "." else res
#endif

let fileNameOfPath s = 
    checkPathForIllegalChars s
#if FABLE_COMPILER
    s //TODO: proper implementation
#else
    Path.GetFileName(s)
#endif

let fileNameWithoutExtensionWithValidate (validate:bool) s = 
    if validate then checkPathForIllegalChars s |> ignore
#if FABLE_COMPILER
    s //TODO: proper implementation
#else
    Path.GetFileNameWithoutExtension(s)
#endif

let fileNameWithoutExtension s = fileNameWithoutExtensionWithValidate true s

let trimQuotes (s:string) =
    s.Trim( [|' '; '\"'|] )
