use std::str::from_utf8 as str_from_utf8;

/// A parser for CSS selectors.
///
/// https://www.w3.org/TR/selectors/
///
/// https://www.w3.org/tr/selectors/#parse-selector
///
/// > 19.1. parse a selector
/// > this section defines how to parse a selector from a string source. it returns either a complex selector list, or failure.
/// >
/// > let selector be the result of parsing source as a <selector-list>. if this returns failure, it’s an invalid selector; return failure.
/// > if selector is an invalid selector for any other reason (such as, for example, containing an undeclared namespace prefix), return failure.
/// > otherwise, return selector.
///
/// https://www.w3.org/TR/selectors/#typedef-selector-list
///
/// > 18. Grammar
/// >
/// > Selectors are parsed according to the following grammar:
/// >
/// > <selector-list> = <complex-selector-list>
/// >
/// > <complex-selector-list> = <complex-selector>#
/// >
/// > <compound-selector-list> = <compound-selector>#
/// >
/// > <simple-selector-list> = <simple-selector>#
/// >
/// > <relative-selector-list> = <relative-selector>#
/// >
/// >
/// > <complex-selector> = <compound-selector> [ <combinator>? <compound-selector> ]*
/// >
/// > <relative-selector> = <combinator>? <complex-selector>
/// >
/// > <compound-selector> = [ <type-selector>? <subclass-selector>*
/// >                         [ <pseudo-element-selector> <pseudo-class-selector>* ]* ]!
/// >
/// > <simple-selector> = <type-selector> | <subclass-selector>
/// >
/// >
/// > <combinator> = '>' | '+' | '~' | [ '|' '|' ]
/// >
/// > <type-selector> = <wq-name> | <ns-prefix>? '*'
/// >
/// > <ns-prefix> = [ <ident-token> | '*' ]? '|'
/// >
/// > <wq-name> = <ns-prefix>? <ident-token>
/// >
/// > <subclass-selector> = <id-selector> | <class-selector> |
/// >                       <attribute-selector> | <pseudo-class-selector>
/// >
/// > <id-selector> = <hash-token>
/// >
/// > <class-selector> = '.' <ident-token>
/// >
/// > <attribute-selector> = '[' <wq-name> ']' |
/// >                        '[' <wq-name> <attr-matcher> [ <string-token> | <ident-token> ] <attr-modifier>? ']'
/// >
/// > <attr-matcher> = [ '~' | '|' | '^' | '$' | '*' ]? '='
/// >
/// > <attr-modifier> = i | s
/// >
/// > <pseudo-class-selector> = ':' <ident-token> |
/// >                           ':' <function-token> <any-value> ')'
/// >
/// > <pseudo-element-selector> = ':' <pseudo-class-selector>
///
/// https://www.w3.org/TR/2022/WD-selectors-4-20221111/#parse-as-a-forgiving-selector-list
///
/// > 19.1. Parse A Selector
/// > This section defines how to parse a selector from a string source. It returns either a complex selector list, or failure.
/// > 1. Let selector be the result of parsing source as a <selector-list>. If this returns failure, it’s an invalid selector; return failure.
/// > 2. If selector is an invalid selector for any other reason (such as, for example, containing an undeclared namespace prefix), return failure.
/// > 3. Otherwise, return selector.
///
/// https://www.w3.org/TR/css-syntax-3/#css-parse-something-according-to-a-css-grammar
///
/// > 5.3.1. Parse something according to a CSS grammar
/// > To parse something according to a CSS grammar (aka simply parse) given an input and a CSS grammar production:
/// > 1. Normalize input, and set input to the result.
/// > 2. Parse a list of component values from input, and let result be the return value.
/// > 3. Attempt to match result against grammar. If this is successful, return the matched result; otherwise, return failure.
///
///
/// > To normalize into a token stream a given input:
/// > 1. If input is a list of CSS tokens, return input.
/// >
/// > 2. If input is a list of CSS component values, return input.
/// >
/// > Note: The only difference between a list of tokens and a list of component values is that some objects that "contain" things, like functions or blocks, are a single entity in the component-value list, but are multiple entities in a token list. This makes no difference to any of the algorithms in this specification.
/// >
/// > 3. If input is a string, then filter code points from input, tokenize the result, and return the final result.
/// >
/// > Assert: Only the preceding types should be passed as input.
///
/// https://www.w3.org/TR/css-syntax-3/#input-preprocessing
///
/// > To filter code points from a stream of (unfiltered) code points input:
/// > Replace any U+000D CARRIAGE RETURN (CR) code points, U+000C FORM FEED (FF) code points, or
/// > pairs of U+000D CARRIAGE RETURN (CR) followed by U+000A LINE FEED (LF) in input by a single
/// > U+000A LINE FEED (LF) code point.
/// > Replace any U+0000 NULL or surrogate code points in input with
/// > U+FFFD REPLACEMENT CHARACTER (�).
///
/// # Examples
///
/// ```
/// use parse_css_selectors_rs::Parser;
///
/// let parser = Parser::new("#foo-id");
/// for token in parser {
///     println!("{:?}", token);
/// }
/// ```

pub struct Parser {
    data: String,
}

type Codepoint = u32;

#[derive(Debug, Eq, PartialEq)]
enum HashTokenFlag {
    ID,
    Unrestricted,
}

#[derive(Debug, Eq, PartialEq)]
enum NumericTypeFlag {
    Integer,
    Number,
}

/// > The output of tokenization step is a stream of zero or more of the following tokens: <ident-token>, <function-token>, <at-keyword-token>, <hash-token>, <string-token>, <bad-string-token>, <url-token>, <bad-url-token>, <delim-token>, <number-token>, <percentage-token>, <dimension-token>, <whitespace-token>, <CDO-token>, <CDC-token>, <colon-token>, <semicolon-token>, <comma-token>, <[-token>, <]-token>, <(-token>, <)-token>, <{-token>, and <}-token>.
/// >
/// > <ident-token>, <function-token>, <at-keyword-token>, <hash-token>, <string-token>, and <url-token> have a value composed of zero or more code points. Additionally, hash tokens have a type flag set to either "id" or "unrestricted". The type flag defaults to "unrestricted" if not otherwise set.
/// > <delim-token> has a value composed of a single code point.
/// > <number-token>, <percentage-token>, and <dimension-token> have a numeric value. <number-token> and <dimension-token> additionally have a type flag set to either "integer" or "number". The type flag defaults to "integer" if not otherwise set. <dimension-token> additionally have a unit composed of one or more code points.
#[derive(Debug, PartialEq)]
enum Token<'a> {
    Ident(&'a str),
    Function(&'a [Codepoint]),
    AtKeyword(&'a [Codepoint]),
    Hash(&'a [Codepoint], HashTokenFlag),
    String(&'a [Codepoint]),
    BadString,
    URL(&'a [Codepoint]),
    BadURL,
    Delim(Codepoint),
    Number(f64, NumericTypeFlag),
    Percentage(f64),
    Dimension(f64, NumericTypeFlag, &'a [Codepoint]),
    Whitespace,
    CDO,
    CDC,
    Colon,
    Semicolon,
    Comma,
    SquareBracketOpen,
    SquareBracketClose,
    ParenOpen,
    ParenClose,
    CurlyBraceOpen,
    CurlyBraceClose,
}

type R<'a, T> = Result<(&'a [u8], T), ()>;

impl<'a> Parser {
    pub fn new(input: &'a str) -> Self {
        Self {
            // > If input is a string, then filter code points from input, tokenize the result, and return the final result.
            data: Self::normalize(input),
        }
    }

    /// > To filter code points from a stream of (unfiltered) code points input:
    /// > Replace any U+000D CARRIAGE RETURN (CR) code points, U+000C FORM FEED (FF) code points, or pairs of U+000D CARRIAGE RETURN (CR) followed by U+000A LINE FEED (LF) in input by a single U+000A LINE FEED (LF) code point.
    /// > Replace any U+0000 NULL or surrogate code points in input with U+FFFD REPLACEMENT CHARACTER (�).
    fn normalize(input: &str) -> String {
        let out = input
            .replace("\u{000D}\u{000A}", "\u{000A}")
            .replace("\u{000D}", "\u{000A}")
            .replace("\u{000C}", "\u{000A}")
            .replace("\u{0000}", "\u{FFFD}");
        out
    }
}

//impl Iterator for Parser {
//    type Item = Result<Selector, ()>;
//
//    fn next(&mut self) -> Option<Self::Item> {
//        if self.data.is_empty() {
//            return None;
//        }
//
//        match self.data {
//            _ => panic!("Unimplemented {:?}", self.data),
//        }
//    }
//}

//fn parse_comment(s: &[u8]) -> R<Token> {
//    let (s, _) = util::parse_bytes(s, b"<!--")?;
//    let mut i = 0;
//    while s.len() >= i + 3 {
//        if &s[i..i + 3] == b"-->" {
//            return Ok((
//                &s[i + 3..],
//                Token::Comment {
//                    text: str_from_utf8(&s[..i]).unwrap(),
//                },
//            ));
//        }
//        i += 1;
//    }
//    Err(())
//}

#[derive(Debug, PartialEq)]
enum Selector<'a> {
    Class(&'a str),
    ID(&'a str),
}

fn is_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_' || byte >= 0x80u8
}

fn is_ident(byte: u8) -> bool {
    is_ident_start(byte) || byte.is_ascii_digit() || byte == b'-'
}

fn parse_class(s: &[u8]) -> R<Selector> {
    if s.len() < 2 {
        return Err(());
    }

    if s[0] != b'.' {
        return Err(());
    }

    let (rest, ident) = parse_ident(&s[1..])?;
    match ident {
        Token::Ident(ident) => Ok((rest, Selector::Class(ident))),
        _ => Err(()),
    }
}

fn parse_id(s: &[u8]) -> R<Selector> {
    if s.len() < 2 {
        return Err(());
    }

    if s[0] != b'#' {
        return Err(());
    }

    let (rest, ident) = parse_ident(&s[1..])?;
    match ident {
        Token::Ident(ident) => Ok((rest, Selector::ID(ident))),
        _ => Err(()),
    }
}

fn parse_ident(s: &[u8]) -> R<Token> {
    if s.is_empty() {
        return Err(());
    }

    if !is_ident_start(s[0]) {
        return Err(());
    }

    let mut i = 1usize;
    while s.len() > i && is_ident(s[i]) {
        i += 1;
    }

    Ok((&s[i..], Token::Ident(str_from_utf8(&s[..i]).unwrap())))
}

mod util {
    use super::R;

    pub(super) fn parse_bytes<'a>(s: &'a [u8], bytes: &[u8]) -> R<'a, ()> {
        if s.starts_with(bytes) {
            Ok((&s[bytes.len()..], ()))
        } else {
            Err(())
        }
    }

    pub(super) fn parse_s(s: &[u8]) -> R<()> {
        let mut at = 0;
        while s.len() > at && matches!(s[at], b'\x20' | b'\x09' | b'\x0D' | b'\x0A') {
            at += 1;
        }
        if at > 0 {
            Ok((&s[at..], ()))
        } else {
            Err(())
        }
    }

    pub(super) fn parse_s_optional(s: &[u8]) -> R<()> {
        parse_s(s).or(Ok((s, ())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_ident() {
        assert!(parse_ident(b"-foo").is_err());

        let (rest, parsed) = parse_ident(b"_-foo123#xyz").unwrap();
        assert_eq!(rest, b"#xyz");
        assert_eq!(parsed, Token::Ident("_-foo123"));

        // The bytes in the Flag of England emoji.
        let flag_of_england = [
            240u8, 159, 143, 180, 243, 160, 129, 167, 243, 160, 129, 162, 243, 160, 129, 165, 243,
            160, 129, 174, 243, 160, 129, 167, 243, 160, 129, 191,
        ];
        let x = [&flag_of_england[..], b"foo123.xyz"].concat();

        let (rest, parsed) = parse_ident(x.as_slice()).unwrap();
        assert_eq!(rest, b".xyz");
        assert_eq!(parsed, Token::Ident("🏴󠁧󠁢󠁥󠁮󠁧󠁿foo123"));
    }

    #[test]
    fn test_parse_class() {
        assert!(parse_class(b"foo").is_err());
        assert!(parse_class(b".-foo").is_err());
        assert!(parse_class(b".1foo").is_err());

        let (rest, parsed) = parse_class(b"._-foo123.more").unwrap();
        assert_eq!(rest, b".more");
        assert_eq!(parsed, Selector::Class("_-foo123"));

        let (rest, parsed) = parse_class(b".CLASS abc").unwrap();
        assert_eq!(rest, b" abc");
        assert_eq!(parsed, Selector::Class("CLASS"));
    }

    #[test]
    fn test_parse_id() {
        assert!(parse_id(b"foo").is_err());
        assert!(parse_id(b"#-foo").is_err());
        assert!(parse_id(b"#1foo").is_err());

        let (rest, parsed) = parse_id(b"#_-foo123.more").unwrap();
        assert_eq!(rest, b".more");
        assert_eq!(parsed, Selector::ID("_-foo123"));

        let (rest, parsed) = parse_id(b"#ID abc").unwrap();
        assert_eq!(rest, b" abc");
        assert_eq!(parsed, Selector::ID("ID"));
    }
}
