/// A parser for CSS selectors.
///
/// https://www.w3.org/TR/selectors/
///
/// https://www.w3.org/tr/selectors/#parse-selector
///
/// > 19.1. parse a selector
/// >   this section defines how to parse a selector from a string source. it returns either a complex selector list, or failure.
/// >
/// >     let selector be the result of parsing source as a <selector-list>. if this returns failure, it’s an invalid selector; return failure.
/// >     if selector is an invalid selector for any other reason (such as, for example, containing an undeclared namespace prefix), return failure.
/// >     otherwise, return selector.
///
/// https://www.w3.org/TR/selectors/#typedef-selector-list
///
/// > 18. Grammar
/// >
/// > Selectors are parsed according to the following grammar:
/// >
/// > <selector-list> = <complex-selector-list>
/// > <complex-selector-list> = <complex-selector>#
/// > <compound-selector-list> = <compound-selector>#
/// > <simple-selector-list> = <simple-selector>#
/// > <relative-selector-list> = <relative-selector>#
/// >
/// > <complex-selector> = <compound-selector> [ <combinator>? <compound-selector> ]*
/// > <relative-selector> = <combinator>? <complex-selector>
/// > <compound-selector> = [ <type-selector>? <subclass-selector>*
/// >                         [ <pseudo-element-selector> <pseudo-class-selector>* ]* ]!
/// > <simple-selector> = <type-selector> | <subclass-selector>
/// >
/// > <combinator> = '>' | '+' | '~' | [ '|' '|' ]
/// > <type-selector> = <wq-name> | <ns-prefix>? '*'
/// > <ns-prefix> = [ <ident-token> | '*' ]? '|'
/// > <wq-name> = <ns-prefix>? <ident-token>
/// > <subclass-selector> = <id-selector> | <class-selector> |
/// >                       <attribute-selector> | <pseudo-class-selector>
/// >
/// > <id-selector> = <hash-token>
/// > <class-selector> = '.' <ident-token>
/// > <attribute-selector> = '[' <wq-name> ']' |
/// >                        '[' <wq-name> <attr-matcher> [ <string-token> | <ident-token> ] <attr-modifier>? ']'
/// > <attr-matcher> = [ '~' | '|' | '^' | '$' | '*' ]? '='
/// > <attr-modifier> = i | s
/// > <pseudo-class-selector> = ':' <ident-token> |
/// >                           ':' <function-token> <any-value> ')'
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
///
///
///

/// These tokens are mentioned in parsing selectors:

/// - <ident-token>
/// - <hash-token>
/// - <string-token>
/// - <function-token>
///
/// > https://www.w3.org/TR/css-syntax-3/#consume-token

pub struct Parser {
    data: String,
}

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
        input
            .replace("\u{000D}\u{000A}", "\u{000A}")
            .replace("\u{000D}", "\u{000A}")
            .replace("\u{000C}", "\u{000A}")
            .replace("\u{0000}", "\u{FFFD}")
    }
}

mod selector {
    use super::*;

    /// Selectors
    ///
    /// >   this section defines how to parse a selector from a string source. it returns either a complex selector list, or failure.
    /// > …
    /// > <complex-selector-list> = <complex-selector>#
    /// >
    /// > <complex-selector> = <compound-selector> [ <combinator>? <compound-selector> ]*
    /// > <compound-selector> = [ <type-selector>? <subclass-selector>*
    /// >                         [ <pseudo-element-selector> <pseudo-class-selector>* ]* ]!
    /// >
    /// > <combinator> = '>' | '+' | '~' | [ '|' '|' ]
    /// > <type-selector> = <wq-name> | <ns-prefix>? '*'
    /// > <ns-prefix> = [ <ident-token> | '*' ]? '|'
    /// > <wq-name> = <ns-prefix>? <ident-token>
    /// > <subclass-selector> = <id-selector> | <class-selector> |
    /// >                       <attribute-selector> | <pseudo-class-selector>
    /// >
    /// > <id-selector> = <hash-token>
    /// > <class-selector> = '.' <ident-token>
    /// > <attribute-selector> = '[' <wq-name> ']' |
    /// >                        '[' <wq-name> <attr-matcher> [ <string-token> | <ident-token> ] <attr-modifier>? ']'
    /// > <attr-matcher> = [ '~' | '|' | '^' | '$' | '*' ]? '='
    /// > <attr-modifier> = i | s
    /// > <pseudo-class-selector> = ':' <ident-token> |
    /// >                           ':' <function-token> <any-value> ')'
    #[derive(Debug, PartialEq)]
    enum Selector {
        Type(),
        Class(String),
        ID(String),
        Attribute(()),
        PseudoClass(()),
    }

    enum Combinator {
        Descendant,
        Child,
        NextSibling,
        SubsequentSibling,
    }

    struct CompoundSelector {
        type_selector: Option<Selector>,
        subclass_selectors: Vec<Selector>,
        pseudo_class_selector: Option<Selector>,
        // Pseudo-element selectors are not relevant for our purposes.
        // pseudo_element_selector: Option<Selector>,
    }

    struct ComplexSelector {
        selector: CompoundSelector,
        combined_selector: Option<(Combinator, CompoundSelector)>,
    }

    fn parse_class(s: &[u8]) -> R<Selector> {
        if s.len() < 2 {
            return Err(());
        }

        if s[0] != b'.' {
            return Err(());
        }

        let (rest, ident) = token::parse_ident(&s[1..])?;
        match ident {
            token::Token::Ident(ident) => Ok((rest, Selector::Class(ident))),
            _ => Err(()),
        }
    }

    fn parse_id(s: &[u8]) -> R<Selector> {
        let (rest, ident) = token::parse_hash_token(s)?;
        match ident {
            token::Token::Hash(ident, HashTokenFlag::ID) => Ok((rest, Selector::ID(ident))),
            _ => Err(()),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_parse_class() {
            assert!(parse_class(b"foo").is_err());
            assert!(parse_class(b".1foo").is_err());

            let (rest, parsed) = parse_class(b"._-foo123.more").unwrap();
            assert_eq!(rest, b".more");
            assert_eq!(parsed, Selector::Class("_-foo123".to_owned()));

            let (rest, parsed) = parse_class(b".CLASS abc").unwrap();
            assert_eq!(rest, b" abc");
            assert_eq!(parsed, Selector::Class("CLASS".to_owned()));
        }

        #[test]
        fn test_parse_id() {
            assert!(parse_id(b"foo").is_err());
            assert!(parse_id(b"#1foo").is_err());

            let (rest, parsed) = parse_id(b"#_-foo123.more").unwrap();
            assert_eq!(rest, b".more");
            assert_eq!(parsed, Selector::ID("_-foo123".to_owned()));

            let (rest, parsed) = parse_id(b"#ID abc").unwrap();
            assert_eq!(rest, b" abc");
            assert_eq!(parsed, Selector::ID("ID".to_owned()));

            let (rest, parsed) = parse_id(b"#\\31 23").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Selector::ID("123".to_owned()));
        }
    }
}

mod token {
    use super::*;

    /// > The output of tokenization step is a stream of zero or more of the following tokens: <ident-token>, <function-token>, <at-keyword-token>, <hash-token>, <string-token>, <bad-string-token>, <url-token>, <bad-url-token>, <delim-token>, <number-token>, <percentage-token>, <dimension-token>, <whitespace-token>, <CDO-token>, <CDC-token>, <colon-token>, <semicolon-token>, <comma-token>, <[-token>, <]-token>, <(-token>, <)-token>, <{-token>, and <}-token>.
    /// >
    /// > <ident-token>, <function-token>, <at-keyword-token>, <hash-token>, <string-token>, and <url-token> have a value composed of zero or more code points. Additionally, hash tokens have a type flag set to either "id" or "unrestricted". The type flag defaults to "unrestricted" if not otherwise set.
    /// > <delim-token> has a value composed of a single code point.
    /// > <number-token>, <percentage-token>, and <dimension-token> have a numeric value. <number-token> and <dimension-token> additionally have a type flag set to either "integer" or "number". The type flag defaults to "integer" if not otherwise set. <dimension-token> additionally have a unit composed of one or more code points.
    #[derive(Debug, PartialEq)]
    pub(super) enum Token<'a> {
        Ident(String),
        Function(&'a str),
        Hash(String, HashTokenFlag),
        String(&'a str),
        // The reset of these tokens are not relevant for CSS selectors.
        /*
        AtKeyword(&'a str),
        BadString,
        URL(&'a str),
        BadURL,
        Delim(u32),
        Number(f64, NumericTypeFlag),
        Percentage(f64),
        Dimension(f64, NumericTypeFlag, &'a str),
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
        */
    }

    fn is_non_ascii(cp: &Codepoint) -> bool {
        cp.value >= 0x80
    }

    fn is_ident_start(cp: &Codepoint) -> bool {
        matches!(cp.char, 'A'..='Z' | 'a'..='z' | '_' ) || cp.value > 0x80
    }

    fn is_ident(cp: &Codepoint) -> bool {
        is_ident_start(cp) || matches!(cp.char, '0'..='9' | '-')
    }

    /// > 4.3.8. Check if two code points are a valid escape
    /// > This section describes how to check if two code points are a valid escape. The algorithm described here can be called explicitly with two code points, or can be called with the input stream itself. In the latter case, the two code points in question are the current input code point and the next input code point, in that order.
    /// >
    /// > Note: This algorithm will not consume any additional code point.
    /// >
    /// > If the first code point is not U+005C REVERSE SOLIDUS (\), return false.
    /// >
    /// > Otherwise, if the second code point is a newline, return false.
    /// >
    /// > Otherwise, return true.
    ///
    /// https://www.w3.org/TR/css-syntax-3/#starts-with-a-valid-escape
    ///
    /// @todo this does not check whether the second codepoint is valid.
    fn next_two_are_valid_escape(s: &[u8]) -> bool {
        if s.len() < 2 {
            return false;
        }
        s[0] == b'\\' && s[1] != b'\n'
    }

    /// > 4.3.9. Check if three code points would start an ident sequence
    /// > This section describes how to check if three code points would start an ident sequence. The algorithm described here can be called explicitly with three code points, or can be called with the input stream itself. In the latter case, the three code points in question are the current input code point and the next two input code points, in that order.
    /// >
    /// > Note: This algorithm will not consume any additional code points.
    /// >
    /// > Look at the first code point:
    /// >
    /// > U+002D HYPHEN-MINUS
    /// >   If the second code point is an ident-start code point or a U+002D HYPHEN-MINUS, or the second and third code points are a valid escape, return true. Otherwise, return false.
    /// > ident-start code point
    /// >   Return true.
    /// > U+005C REVERSE SOLIDUS (\)
    /// >   If the first and second code points are a valid escape, return true. Otherwise, return false.
    /// > anything else
    /// >   Return false.
    ///
    /// https://www.w3.org/TR/css-syntax-3/#would-start-an-identifier
    fn check_if_three_code_points_would_start_an_ident_sequence(s: &[u8]) -> bool {
        if s.is_empty() {
            return false;
        }

        // > U+005C REVERSE SOLIDUS (\)
        if s[0] == b'\\' {
            return next_two_are_valid_escape(s);
        }

        // > U+002D HYPHEN-MINUS
        if s[0] == b'-' {
            let after_initial_hyphen_minus = &s[1..];

            // > If the second code point is… U+002D HYPHEN-MINUS… return true
            if after_initial_hyphen_minus[0] == b'-' {
                return true;
            }

            // > If the second and third code points are a valid escape, return true.
            if next_two_are_valid_escape(after_initial_hyphen_minus) {
                return true;
            }

            // > If the second code point is an ident-start code point… return true.
            if let Some((second_cp, _)) = Codepoint::take(after_initial_hyphen_minus) {
                return is_ident_start(&second_cp);
            }

            // > Otherwise, return false.
            return false;
        }

        // > ident-start code point
        // >   Return true.
        // > anything else
        // >   Return false.
        Codepoint::take(s)
            .map(|(cp, _)| is_ident_start(&cp))
            .unwrap_or(false)
    }

    /// > 4.3.7. Consume an escaped code point
    /// > This section describes how to consume an escaped code point. It assumes that the U+005C
    /// > REVERSE SOLIDUS (\) has already been consumed and that the next input code point has
    /// > already been verified to be part of a valid escape. It will return a code point.
    /// >
    /// > Consume the next input code point.
    /// >
    /// > hex digit
    /// >   Consume as many hex digits as possible, but no more than 5. Note that this means 1-6
    /// >   hex digits have been consumed in total. If the next input code point is whitespace,
    /// >   consume it as well. Interpret the hex digits as a hexadecimal number. If this number is
    /// >   zero, or is for a surrogate, or is greater than the maximum allowed code point, return
    /// >   U+FFFD REPLACEMENT CHARACTER (�). Otherwise, return the code point with that value.
    /// > EOF
    /// >   This is a parse error. Return U+FFFD REPLACEMENT CHARACTER (�).
    /// > anything else
    /// >   Return the current input code point.
    fn consume_escaped_codepoint(s: &[u8]) -> (char, &[u8]) {
        if s[0].is_ascii_hexdigit() {
            let mut hex_ends = 1;
            while s.len() > hex_ends && hex_ends < 6 && s[hex_ends].is_ascii_hexdigit() {
                hex_ends += 1;
            }
            let hex_string = unsafe { std::str::from_utf8_unchecked(&s[..hex_ends]) };
            let char_digit = u32::from_str_radix(hex_string, 16).unwrap();

            // > A surrogate is a leading surrogate or a trailing surrogate.
            // > A leading surrogate is a code point that is in the range U+D800 to U+DBFF, inclusive.
            // > A trailing surrogate is a code point that is in the range U+DC00 to U+DFFF, inclusive.
            // The surrogate ranges are adjacent, so the complete range is 0xD800..=0xDFFF,
            // inclusive.
            let char = if char_digit == 0
                || char_digit > UTF8_MAX_CODEPOINT_VALUE
                || matches!(char_digit, 0xD800..=0xDFFF)
            {
                '\u{FFFD}'
            } else {
                unsafe { char::from_u32_unchecked(char_digit) }
            };

            // If the next input code point is whitespace, consume it as well.
            if s.len() > hex_ends && matches!(s[hex_ends], b'\n' | b'\t' | b' ') {
                hex_ends += 1;
            }
            return (char, &s[hex_ends..]);
        }

        Codepoint::take(s)
            .map(|(cp, rest)| (cp.char, rest))
            .expect("codepoint should be guaranteed valid here")
    }

    /// > 4.3.11. Consume an ident sequence
    /// > This section describes how to consume an ident sequence from a stream of code points. It returns a string containing the largest name that can be formed from adjacent code points in the stream, starting from the first.
    /// >
    /// > Note: This algorithm does not do the verification of the first few code points that are necessary to ensure the returned code points would constitute an <ident-token>. If that is the intended use, ensure that the stream starts with an ident sequence before calling this algorithm.
    /// >
    /// > Let result initially be an empty string.
    /// >
    /// > Repeatedly consume the next input code point from the stream:
    /// >
    /// > ident code point
    /// > Append the code point to result.
    /// > the stream starts with a valid escape
    /// > Consume an escaped code point. Append the returned code point to result.
    /// > anything else
    /// > Reconsume the current input code point. Return result.
    /// https://www.w3.org/TR/css-syntax-3/#consume-name
    pub(super) fn parse_ident(s: &[u8]) -> R<Token> {
        if !check_if_three_code_points_would_start_an_ident_sequence(s) {
            return Err(());
        }

        let mut ident = String::new();

        let mut rest = s;
        loop {
            if next_two_are_valid_escape(rest) {
                let (char, next_rest) = consume_escaped_codepoint(&rest[1..]);
                ident.push(char);
                rest = next_rest;
                continue;
            } else if let Some((cp, next_rest)) = Codepoint::take(rest) {
                if is_ident(&cp) {
                    ident.push(cp.char);
                    rest = next_rest;
                    continue;
                }
            }
            break;
        }

        Ok((rest, Token::Ident(ident)))
    }

    /// Tokenization of hash tokens
    ///
    /// > U+0023 NUMBER SIGN (#)
    /// >   If the next input code point is an ident code point or the next two input code points are a valid escape, then:
    /// >     1. Create a <hash-token>.
    /// >     2. If the next 3 input code points would start an ident sequence, set the
    /// >        <hash-token>’s type flag to "id".
    /// >     3. Consume an ident sequence, and set the <hash-token>’s value to the
    ///          returned string.
    /// >     4. Return the <hash-token>.
    /// >   Otherwise, return a <delim-token> with its value set to the current input code point.
    ///
    /// This implementation is not interested in the <delim-token> that is not relevant for CSS
    /// selectors.
    pub(super) fn parse_hash_token(s: &[u8]) -> R<Token> {
        if s.len() < 2 || s[0] != b'#' {
            return Err(());
        }

        let rest = &s[1..];
        if check_if_three_code_points_would_start_an_ident_sequence(rest) {
            match parse_ident(rest)? {
                (rest, Token::Ident(ident)) => Ok((rest, Token::Hash(ident, HashTokenFlag::ID))),
                _ => unreachable!(),
            }
        } else {
            Err(())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_parse_ident() {
            let (rest, parsed) = parse_ident(b"_-foo123#xyz").unwrap();
            assert_eq!(rest, b"#xyz");
            assert_eq!(parsed, Token::Ident("_-foo123".to_owned()));

            // The bytes in the Flag of England emoji.
            let flag_of_england = [
                240u8, 159, 143, 180, 243, 160, 129, 167, 243, 160, 129, 162, 243, 160, 129, 165,
                243, 160, 129, 174, 243, 160, 129, 167, 243, 160, 129, 191,
            ];
            let x = [&flag_of_england[..], b"foo123.xyz"].concat();

            let (rest, parsed) = parse_ident(x.as_slice()).unwrap();
            assert_eq!(rest, b".xyz");
            assert_eq!(parsed, Token::Ident("🏴󠁧󠁢󠁥󠁮󠁧󠁿foo123".to_owned()));
        }

        #[test]
        fn test_parse_ident_escape() {
            let (rest, parsed) = parse_ident(b"\\xyz").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("xyz".to_owned()));

            let (rest, parsed) = parse_ident(b"\\ n").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident(" n".to_owned()));

            let (rest, parsed) = parse_ident("\\".as_bytes()).unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("".to_owned()));

            let (rest, parsed) = parse_ident("\\abcd".as_bytes()).unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("ꯍ".to_owned()));
        }

        #[test]
        fn test_escape_hex_digits_stop_at_whitespace() {
            let (rest, parsed) = parse_ident(b"\\31 23").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("123".to_owned()));

            let (rest, parsed) = parse_ident(b"\\31\t23").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("123".to_owned()));

            let (rest, parsed) = parse_ident(b"\\31\n23").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("123".to_owned()));

            let (rest, parsed) = parse_ident(b"\\9").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\t".to_owned()));
        }

        #[test]
        fn test_escape_hex_digits_out_of_range_is_replacement_character() {
            let (rest, parsed) = parse_ident(b"\\110000 ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));

            let (rest, parsed) = parse_ident(b"\\ffffff ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));
        }

        #[test]
        fn test_escape_hex_digits_surrogates_are_replacement_character() {
            // > A surrogate is a leading surrogate or a trailing surrogate.
            // > A leading surrogate is a code point that is in the range U+D800 to U+DBFF, inclusive.
            // > A trailing surrogate is a code point that is in the range U+DC00 to U+DFFF, inclusive.
            // The surrogate ranges are adjacent, so the complete range is 0xD800..=0xDFFF,
            // inclusive.
            let (rest, parsed) = parse_ident(b"\\d800 ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));

            let (rest, parsed) = parse_ident(b"\\dbff ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));

            let (rest, parsed) = parse_ident(b"\\dc00 ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));

            let (rest, parsed) = parse_ident(b"\\dfff ").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident("\u{FFFD}".to_owned()));
        }

        #[test]
        fn test_escape_hex_digits_max_six() {
            let (rest, parsed) = parse_ident(b"\\000061bc").unwrap();
            assert!(rest.is_empty());
            assert_eq!(parsed, Token::Ident(String::from("abc")));
        }
    }
}

impl From<UTF8Error> for () {
    fn from(_: UTF8Error) {}
}

#[derive(Debug)]
enum UTF8Error {
    InvalidInitialByte,
    MissingBytes,
    InvalidContinuationByte,
    CodepointOutOfRange,
}

const UTF8_2_BYTE_BITMASK: u8 = 0b0001_1111;
const UTF8_3_BYTE_BITMASK: u8 = 0b0000_1111;
const UTF8_4_BYTE_BITMASK: u8 = 0b0000_0111;
const UTF8_MAX_CODEPOINT_VALUE: u32 = 0x10FFFF;

#[derive(Debug, PartialEq)]
struct Codepoint {
    char: char,
    value: u32,
    bytelength: usize,
}

impl Codepoint {
    fn from_bytes(s: &[u8]) -> Result<Option<Self>, UTF8Error> {
        if s.is_empty() {
            return Ok(None);
        }

        let (bytelength, mut value) = if s[0] & 0b1000_0000 == 0 {
            (1, s[0] as u32)
        } else if s[0] & 0b1110_0000 == 0b1100_0000 {
            (2, (s[0] & UTF8_2_BYTE_BITMASK) as u32)
        } else if s[0] & 0b1111_0000 == 0b1110_0000 {
            (3, (s[0] & UTF8_3_BYTE_BITMASK) as u32)
        } else if s[0] & 0b1111_1000 == 0b1111_0000 {
            (4, (s[0] & UTF8_4_BYTE_BITMASK) as u32)
        } else {
            return Err(UTF8Error::InvalidInitialByte);
        };

        if s.len() < bytelength {
            return Err(UTF8Error::MissingBytes);
        }

        for byte in &s[1..bytelength] {
            if (byte & 0b1100_0000) == 0b1000_0000 {
                value = (value << 6) | (byte & 0b0011_1111) as u32;
            } else {
                return Err(UTF8Error::InvalidContinuationByte);
            }
        }

        if value > UTF8_MAX_CODEPOINT_VALUE {
            return Err(UTF8Error::CodepointOutOfRange);
        }

        // Unsafe! Because we already did the utf8 checking above!
        let char = unsafe { std::char::from_u32_unchecked(value) };

        Ok(Some(Self {
            value,
            char,
            bytelength,
        }))
    }

    ///@todo should this propagate the error?
    fn take(bytes: &[u8]) -> Option<(Self, &[u8])> {
        if let Ok(Some(cp)) = Self::from_bytes(bytes) {
            let l = cp.bytelength;
            Some((cp, &bytes[l..]))
        } else {
            None
        }
    }
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
    fn test_codepoint_1byte() {
        let codepoint = Codepoint::from_bytes(b"abc").unwrap().unwrap();
        assert_eq!(codepoint.char, 'a');
        assert_eq!(codepoint.value, 'a' as u32);
        assert_eq!(codepoint.bytelength, 1);
    }

    #[test]
    fn test_codepoint_2byte() {
        let c = '¬';
        let s: String = String::from(c);
        assert_eq!(s.as_bytes().len(), 2);
        let codepoint = Codepoint::from_bytes(s.as_bytes()).unwrap().unwrap();
        assert_eq!(codepoint.char, c);
        assert_eq!(codepoint.value, c as u32);
        assert_eq!(codepoint.bytelength, 2);
    }

    #[test]
    fn test_codepoint_3byte() {
        let c = '∑';
        let s: String = String::from(c);
        assert_eq!(s.as_bytes().len(), 3);
        let codepoint = Codepoint::from_bytes(s.as_bytes()).unwrap().unwrap();
        assert_eq!(codepoint.char, c);
        assert_eq!(codepoint.value, c as u32);
        assert_eq!(codepoint.bytelength, 3);
    }

    #[test]
    fn test_codepoint_4byte() {
        let c = '🦸';
        let s: String = String::from(c);
        assert_eq!(s.as_bytes().len(), 4);
        let codepoint = Codepoint::from_bytes(s.as_bytes()).unwrap().unwrap();
        assert_eq!(codepoint.char, c);
        assert_eq!(codepoint.value, c as u32);
        assert_eq!(codepoint.bytelength, 4);
    }

    #[test]
    fn test_codepoints_flag_of_england() {
        let bytestring = [
            240, 159, 143, 180, 243, 160, 129, 167, 243, 160, 129, 162, 243, 160, 129, 165, 243,
            160, 129, 174, 243, 160, 129, 167, 243, 160, 129, 191,
        ];

        let mut codepoints = Vec::new();
        let mut s = &bytestring[..];
        while let Ok(Some(cp)) = Codepoint::from_bytes(s) {
            codepoints.push(cp.value);
            s = &s[cp.bytelength..];
        }

        assert_eq!(
            codepoints,
            vec![
                0x1F3F4, // U+1F3F4 WAVING BLACK FLAG
                0xE0067, // U+E0067 TAG LATIN SMALL LETTER G
                0xE0062, // U+E0062 TAG LATIN SMALL LETTER B
                0xE0065, // U+E0065 TAG LATIN SMALL LETTER E
                0xE006E, // U+E006E TAG LATIN SMALL LETTER N
                0xE0067, // U+E0067 TAG LATIN SMALL LETTER G
                0xE007F, // U+E007F CANCEL TAG
            ]
        );
    }

    #[test]
    fn test_codepoints_woman_superhero_dark_skin_tone() {
        let bytestring = [
            240, 159, 166, 184, 240, 159, 143, 191, 226, 128, 141, 226, 153, 128, 239, 184, 143,
        ];

        let mut codepoints = Vec::new();
        let mut s = &bytestring[..];
        while let Ok(Some(cp)) = Codepoint::from_bytes(s) {
            codepoints.push(cp.value);
            s = &s[cp.bytelength..];
        }

        assert_eq!(
            codepoints,
            vec![
                0x1F9B8, // Superhero
                0x1F3FF, // EMOJI MODIFIER FITZPATRICK TYPE-6 (dark skin tone)
                0x0200D, // ZERO WIDTH JOINER (ZWJ)
                0x02640, // FEMALE SIGN
                0x0FE0F, // VARIATION SELECTOR-16 (emoji variation)
            ]
        );
    }

    #[test]
    fn test_codepoints_woman_astronaut_light_skin_tone() {
        let bytestring = [
            240, 159, 145, 169, 240, 159, 143, 187, 226, 128, 141, 240, 159, 154, 128,
        ];

        let mut codepoints = Vec::new();
        let mut s = &bytestring[..];
        while let Ok(Some(cp)) = Codepoint::from_bytes(s) {
            codepoints.push(cp.value);
            s = &s[cp.bytelength..];
        }

        assert_eq!(
            codepoints,
            vec![
                0x1F469, // Woman
                0x1F3FB, // EMOJI MODIFIER FITZPATRICK TYPE-1-2 (light skin tone)
                0x0200D, // ZERO WIDTH JOINER (ZWJ)
                0x1F680, // Rocket
            ]
        );
    }
}
