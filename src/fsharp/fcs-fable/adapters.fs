namespace Internal.Utilities

#nowarn "1182"

open System.Collections.Generic

//-------------------------------------------------------------------------
// shims for things not yet implemented in Fable
//------------------------------------------------------------------------

//TODO: implement proper Unicode char, decimal

module System =

    module Reflection =
        type AssemblyName(assemblyName: string) =
            member x.Name = assemblyName //TODO: proper implementation

    module Collections =
        module Generic =
            type System.Collections.Generic.Dictionary<'TKey, 'TValue> with
                member x.TryAdd (key:'TKey, value:'TValue) =
                    x.[key] <- value; true
                member x.GetOrAdd (key, valueFactory) =
                    match x.TryGetValue key with
                    | true, v -> v
                    | false, _ -> let v = valueFactory(key) in x.[key] <- v; v
        module Concurrent =
            type ConcurrentDictionary<'TKey, 'TValue> = System.Collections.Generic.Dictionary<'TKey, 'TValue>

    type StringComparer(comp: System.StringComparison) =
        static member Ordinal = StringComparer(System.StringComparison.Ordinal)
        static member OrdinalIgnoreCase = StringComparer(System.StringComparison.OrdinalIgnoreCase)
        interface IEqualityComparer<string> with
            member x.Equals(a,b) = System.String.Compare(a, b, comp) = 0
            member x.GetHashCode a = hash a
        interface IComparer<string> with
            member x.Compare(a,b) = System.String.Compare(a, b, comp)

    module Char =
        open System.Globalization

        let GetUnicodeCategory (c: char): UnicodeCategory =
            LanguagePrimitives.EnumOfValue (int categoryForLatin1.[int c]) //TODO: proper Unicode implementation
        let IsControl (c: char) =
            GetUnicodeCategory(c) = UnicodeCategory.Control
        let IsDigit (c: char) =
            GetUnicodeCategory(c) = UnicodeCategory.DecimalDigitNumber
        let IsLetter (c: char) =
            match GetUnicodeCategory(c) with
            | UnicodeCategory.UppercaseLetter
            | UnicodeCategory.LowercaseLetter
            | UnicodeCategory.TitlecaseLetter
            | UnicodeCategory.ModifierLetter
            | UnicodeCategory.OtherLetter -> true
            | _ -> false
        let IsLetterOrDigit (c: char) =
            IsLetter(c) || IsDigit(c)
        let IsWhiteSpace (c: char) =
            // There are characters which belong to UnicodeCategory.Control but are considered as white spaces.
            c = ' ' || (c >= '\x09' && c <= '\x0d') || c = '\xa0' || c = '\x85'
        let IsUpper (c: char) =
            GetUnicodeCategory(c) = UnicodeCategory.UppercaseLetter
        let IsLower (c: char) =
            GetUnicodeCategory(c) = UnicodeCategory.LowercaseLetter
        let IsPunctuation (c: char) =
            match GetUnicodeCategory(c) with
            | UnicodeCategory.ConnectorPunctuation
            | UnicodeCategory.DashPunctuation
            | UnicodeCategory.OpenPunctuation
            | UnicodeCategory.ClosePunctuation
            | UnicodeCategory.InitialQuotePunctuation
            | UnicodeCategory.FinalQuotePunctuation
            | UnicodeCategory.OtherPunctuation -> true
            | _ -> false
        let IsSurrogatePair (s,i) = false //TODO: Unicode implementation
        let ToUpper (c: char) = if IsLower(c) then char(int('A') + (int(c) - int('a'))) else c
        let ToLower (c: char) = if IsUpper(c) then char(int('a') + (int(c) - int('A'))) else c
        let ToUpperInvariant (c: char) = ToUpper(c)
        let ToLowerInvariant (c: char) = ToLower(c)

    module Convert =
        let ToChar (d) = char d

    module Decimal =
        let GetBits (d: decimal): int[] = [|0;0;0;0|] //TODO: proper implementation
        let FromBits (bits: int[]) = new decimal(0) //TODO: proper implementation

    module Environment =
        let NewLine = "\n" //TODO: proper implementation

    module Text =

        type StringBuilder(?s: string) =
            let buf = ResizeArray<string>()
            do if Option.isSome s then buf.Add(s.Value)
            new (capacity: int, ?maxCapacity: int) = StringBuilder()
            new (s: string, ?maxCapacity: int) = StringBuilder(s)
            member x.Append(s: string) = buf.Add(s); x
            override x.ToString() = System.String.Concat(buf)

        module Encoding =

            module Unicode = // TODO: surrogate pairs
                let GetBytes (s: string) =
                    let addUnicodeChar (buf: ResizeArray<byte>) (c: char) =
                        let i = int c
                        buf.Add (byte (i % 256))
                        buf.Add (byte (i / 256))
                    let buf = ResizeArray<byte>()
                    s.ToCharArray() |> Array.map (addUnicodeChar buf) |> ignore
                    buf.ToArray()

                let GetString (bytes: byte[], index: int, count: int) =
                    let sb = StringBuilder()
                    for i in 0 .. 2 .. count-1 do
                        let c = char ((int(bytes.[index+i+1]) <<< 8) ||| int(bytes.[index+i]))
                        sb.Append(string c) |> ignore
                    sb.ToString()

            module UTF8 = // TODO: surrogate pairs
                let GetBytes (s: string) =
                    let buf = ResizeArray<byte>()
                    let encodeUtf8 (c: char) =
                        let i = int c
                        if i < 0x80 then
                            buf.Add (byte(i))
                        else if i < 0x800 then
                            buf.Add (byte(0xC0 ||| (i >>> 6 &&& 0x1F)))
                            buf.Add (byte(0x80 ||| (i &&& 0x3F)))
                        else if i < 0x10000 then
                            buf.Add (byte(0xE0 ||| (i >>> 12 &&& 0xF)))
                            buf.Add (byte(0x80 ||| (i >>> 6 &&& 0x3F)))
                            buf.Add (byte(0x80 ||| (i &&& 0x3F)))
                    s.ToCharArray() |> Array.map encodeUtf8 |> ignore
                    buf.ToArray()

                let GetString (bytes: byte[], index: int, count: int) =
                    let decodeUtf8 pos =
                        let i1 = int(bytes.[pos])
                        if i1 &&& 0x80 = 0 then
                            (i1 &&& 0x7F), 1
                        else if i1 &&& 0xE0 = 0xC0 then
                            let i2 = int(bytes.[pos + 1]) in
                            ((i1 &&& 0x1F) <<< 6) ||| (i2 &&& 0x3F), 2
                        else if i1 &&& 0xF0 = 0xE0 then
                            let i2 = int(bytes.[pos + 1]) in
                            let i3 = int(bytes.[pos + 2]) in
                            ((i1 &&& 0x1F) <<< 12) ||| ((i2 &&& 0x3F) <<< 6) ||| (i3 &&& 0x3F), 3
                        else 0, 1 // invalid decoding
                    let sb = StringBuilder()
                    let mutable pos = index
                    let last = index + count
                    while pos < last do
                        let d, inc = decodeUtf8 pos
                        sb.Append(string (char d)) |> ignore
                        pos <- pos + inc
                    sb.ToString()


module Microsoft =
    module FSharp =

        module Collections =
            module HashIdentity = 
                let inline FromFunctions hash eq : IEqualityComparer<'T> = 
                    { new IEqualityComparer<'T> with 
                        member __.GetHashCode(x) = hash x
                        member __.Equals(x,y) = eq x y  }
                let inline Structural<'T when 'T : equality> : IEqualityComparer<'T> = 
                    FromFunctions LanguagePrimitives.GenericHash LanguagePrimitives.GenericEquality
                // let Reference<'T when 'T : not struct > : IEqualityComparer<'T> = 
                //     FromFunctions LanguagePrimitives.PhysicalHash LanguagePrimitives.PhysicalEquality

            module ComparisonIdentity = 
                let inline FromFunction comparer = 
                    { new IComparer<'T> with
                        member __.Compare(x,y) = comparer x y } 
                let inline Structural<'T when 'T : comparison> : IComparer<'T> = 
                    FromFunction LanguagePrimitives.GenericComparison

            module List =
                let indexed source = List.mapi (fun i x -> i,x) source

        module Core =
            module LanguagePrimitives =
                let FastGenericComparer<'T when 'T : comparison> =
                    Collections.ComparisonIdentity.Structural<'T>
                let PhysicalHash =
                    LanguagePrimitives.GenericHash //TODO: proper implementation

            module Operators =
                let (|Failure|_|) (exn: exn) = Some exn.Message
                    //if exn.GetType().FullName.EndsWith("Exception") then Some exn.Message else None
                let Failure message = new System.Exception(message)
                let nullArg x = raise(System.ArgumentNullException(x))
            
            module Printf =
                let bprintf (sb: System.Text.StringBuilder) =
                    let f (s:string) = sb.Append(s) |> ignore
                    Printf.kprintf f
                let fprintf (os: System.IO.TextWriter) =
                    let f (s:string) = System.Console.Write(s) //os.Write(s)
                    Printf.kprintf f

            //-------------------------------------------------------------------------
            // From reshapedreflection.fs
            //------------------------------------------------------------------------
            module XmlAdapters =
                let s_escapeChars = [| '<'; '>'; '\"'; '\''; '&' |]
                let getEscapeSequence c =
                    match c with
                    | '<'  -> "&lt;"
                    | '>'  -> "&gt;"
                    | '\"' -> "&quot;"
                    | '\'' -> "&apos;"
                    | '&'  -> "&amp;"
                    | _ as ch -> ch.ToString()
                let escape str = String.collect getEscapeSequence str

        //-------------------------------------------------------------------------
        // From sr.fs
        //------------------------------------------------------------------------
        module Compiler =
            module SR =
                let GetString(name:string) = SR.Resources.resources.[name]

            module internal DiagnosticMessage =
                type ResourceString<'T>(sfmt: string, fmt: string) =
                    member x.Format =
                        let ar = fmt.Split('%')
                                |> Array.filter (fun s -> String.length s > 0)
                                |> Array.map (fun s -> box("%"+s))
                        let tmp = System.String.Format(sfmt, ar)
                        let fmt = Printf.StringFormat<'T>(tmp)
                        sprintf fmt

                let postProcessString (s : string) =
                    s.Replace("\\n","\n").Replace("\\t","\t")
                let DeclareResourceString ((messageID: string),(fmt: string)) =
                    let messageString = SR.GetString(messageID) |> postProcessString
                    ResourceString<'T>(messageString, fmt)


//-------------------------------------------------------------------------
// From IncrementalBuild.fs
//------------------------------------------------------------------------
module ErrorScope =
    let Protect m f1 f2 = try f1() with e -> f2(e.Message)

//-------------------------------------------------------------------------
// From Reactor.fs
//------------------------------------------------------------------------
type internal IReactorOperations = 
    abstract EnqueueAndAwaitOpAsync : string * (unit -> 'T) -> Async<'T>
    abstract EnqueueOp: string * (unit -> unit) -> unit
