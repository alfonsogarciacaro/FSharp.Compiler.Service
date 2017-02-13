namespace System

module Globalization =

    type UnicodeCategory =
        | UppercaseLetter = 0
        | LowercaseLetter = 1
        | TitlecaseLetter = 2
        | ModifierLetter = 3
        | OtherLetter = 4
        | NonSpacingMark = 5
        | SpacingCombiningMark = 6
        | EnclosingMark = 7
        | DecimalDigitNumber = 8
        | LetterNumber = 9
        | OtherNumber = 10
        | SpaceSeparator = 11
        | LineSeparator = 12
        | ParagraphSeparator = 13
        | Control = 14
        | Format = 15
        | Surrogate = 16
        | PrivateUse = 17
        | ConnectorPunctuation = 18
        | DashPunctuation = 19
        | OpenPunctuation = 20
        | ClosePunctuation = 21
        | InitialQuotePunctuation = 22
        | FinalQuotePunctuation = 23
        | OtherPunctuation = 24
        | MathSymbol = 25
        | CurrencySymbol = 26
        | ModifierSymbol = 27
        | OtherSymbol = 28
        | OtherNotAssigned = 29

    // Unicode category values from Unicode U+0000 ~ U+00FF.
    let categoryForLatin1: byte[] = [|
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0000 - 0007
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0008 - 000F
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0010 - 0017
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0018 - 001F
        byte UnicodeCategory.SpaceSeparator; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.CurrencySymbol; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation;    // 0020 - 0027
        byte UnicodeCategory.OpenPunctuation; byte UnicodeCategory.ClosePunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.DashPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation;    // 0028 - 002F
        byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber;    // 0030 - 0037
        byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.DecimalDigitNumber; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.OtherPunctuation;    // 0038 - 003F
        byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter;    // 0040 - 0047
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter;    // 0048 - 004F
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter;    // 0050 - 0057
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.OpenPunctuation; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.ClosePunctuation; byte UnicodeCategory.ModifierSymbol; byte UnicodeCategory.ConnectorPunctuation;    // 0058 - 005F
        byte UnicodeCategory.ModifierSymbol; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 0060 - 0067
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 0068 - 006F
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 0070 - 0077
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.OpenPunctuation; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.ClosePunctuation; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.Control;    // 0078 - 007F
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0080 - 0087
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0088 - 008F
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0090 - 0097
        byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control; byte UnicodeCategory.Control;    // 0098 - 009F
        byte UnicodeCategory.SpaceSeparator; byte UnicodeCategory.OtherPunctuation; byte UnicodeCategory.CurrencySymbol; byte UnicodeCategory.CurrencySymbol; byte UnicodeCategory.CurrencySymbol; byte UnicodeCategory.CurrencySymbol; byte UnicodeCategory.OtherSymbol; byte UnicodeCategory.OtherSymbol;    // 00A0 - 00A7
        byte UnicodeCategory.ModifierSymbol; byte UnicodeCategory.OtherSymbol; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.InitialQuotePunctuation; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.DashPunctuation; byte UnicodeCategory.OtherSymbol; byte UnicodeCategory.ModifierSymbol;    // 00A8 - 00AF
        byte UnicodeCategory.OtherSymbol; byte UnicodeCategory.MathSymbol; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.ModifierSymbol; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.OtherSymbol; byte UnicodeCategory.OtherPunctuation;    // 00B0 - 00B7
        byte UnicodeCategory.ModifierSymbol; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.FinalQuotePunctuation; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.OtherNumber; byte UnicodeCategory.OtherPunctuation;    // 00B8 - 00BF
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter;    // 00C0 - 00C7
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter;    // 00C8 - 00CF
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.MathSymbol;    // 00D0 - 00D7
        byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.UppercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 00D8 - 00DF
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 00E0 - 00E7
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 00E8 - 00EF
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.MathSymbol;    // 00F0 - 00F7
        byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter; byte UnicodeCategory.LowercaseLetter;    // 00F8 - 00FF
    |]
