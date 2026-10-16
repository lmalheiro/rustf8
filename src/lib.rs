#![doc = include_str!("../README.md")]
#![forbid(unsafe_code)]

use std::char::from_u32;
use thiserror::Error;

// Length of the longest sequence the decoder reads (obsolete 6 bytes sequences, reported as errors)
const MAX_SEQUENCE_LENGTH: usize = 6;

enum CachedValue {
    None,
    Byte(u8),
    // Bytes already read of a character interrupted by an I/O error, the next call to next() carries on from them.
    Partial([u8; MAX_SEQUENCE_LENGTH], usize),
    Eof,
}

///
/// A `Utf8Iterator` wraps a UTF-8 decoder around an iterator for `Read`, converting a `u8` iterator into a `char` iterator.
///
/// See the [crate documentation](crate) for examples, errors, panics and safety notes.
///
pub struct Utf8Iterator<R>
where
    R: Iterator,
{
    inner: R,
    _cache: CachedValue,
    _unget: Option<char>,
}

impl<R> Utf8Iterator<R>
where
    R: Iterator<Item = Result<u8, std::io::Error>>,
{
    /// Builds a new UTF-8 iterator using the provided iterator for a `Read`.
    /// This iterator will not reinitialize once it reaches the end of the sequence.
    /// Also, the decoding will start at the current position of the underlying iterator.
    pub fn new(inner: R) -> Self {
        Utf8Iterator {
            inner,
            _cache: CachedValue::None,
            _unget: None,
        }
    }
    /// Returns a character to the iterator. That will be the item returned by the subsequent call to `next()`.
    /// Calling `unget()` twice before calling `next()` will panic.
    ///
    /// # Example
    /// ```
    /// use rustf8::*;
    /// use std::io::prelude::*;
    /// use std::io::Cursor;
    /// let input: Vec<u8> = vec![
    ///     0xce, 0xba, 0xe1, 0xbd, 0xb9, 0xcf, 0x83, 0xce, 0xbc, 0xce, 0xb5,
    /// ];
    /// let stream = Cursor::new(input);
    /// let iter = stream.bytes();
    /// let mut chiter = Utf8Iterator::new(iter);
    /// assert_eq!('κ', chiter.next().unwrap().unwrap());
    /// chiter.unget('ε');
    /// assert_eq!('ε', chiter.next().unwrap().unwrap());
    /// assert_eq!('ό', chiter.next().unwrap().unwrap());
    /// assert_eq!('σ', chiter.next().unwrap().unwrap());
    /// assert_eq!('μ', chiter.next().unwrap().unwrap());
    /// assert_eq!('ε', chiter.next().unwrap().unwrap());
    /// chiter.unget('κ');
    /// assert_eq!('κ', chiter.next().unwrap().unwrap());
    /// assert!(chiter.next().is_none());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if trying to use `unget()` twice before calling `next()`.
    /// Use `try_unget()` to get an error instead.
    ///
    #[track_caller]
    pub fn unget(&mut self, ch: char) {
        if self.try_unget(ch).is_err() {
            panic!("Cannot return character before consuming the previous cached value.")
        }
    }
    /// Returns a character to the iterator, like `unget()`, but never panics.
    ///
    /// # Errors
    ///
    /// If a character returned before has not been consumed by `next()` yet, the iterator is left
    /// unchanged and the rejected character is handed back as `Err(ch)`.
    ///
    /// # Example
    /// ```
    /// use rustf8::*;
    /// use std::io::prelude::*;
    /// use std::io::Cursor;
    /// let mut chiter = Utf8Iterator::new(Cursor::new("κό").bytes());
    /// assert_eq!('κ', chiter.next().unwrap().unwrap());
    /// assert_eq!(Ok(()), chiter.try_unget('κ'));
    /// assert_eq!(Err('ε'), chiter.try_unget('ε'));
    /// assert_eq!('κ', chiter.next().unwrap().unwrap());
    /// assert_eq!('ό', chiter.next().unwrap().unwrap());
    /// ```
    pub fn try_unget(&mut self, ch: char) -> Result<(), char> {
        match self._unget {
            None => {
                self._unget = Some(ch);
                Ok(())
            }
            Some(_) => Err(ch),
        }
    }
    fn take_unget(&mut self) -> Option<char> {
        self._unget.take()
    }

    fn uncache_or_next(&mut self) -> Option<R::Item> {
        let result = match self.cache() {
            // Bumped into an unexpected byte during the previous call to next(),
            // therefore it cached that byte, returned the sequence until that point and now it
            // needs to carry on from the byte that was unexpected.
            CachedValue::Byte(b) => Some(Ok(*b)),
            // If in the previous call to next() it exited because the stream had ended, it means that it returned
            // the character (probably as an invalid sequence) and now it has to indicate the end of the stream.
            CachedValue::Eof => None,
            // next() takes a partial character before reading any byte.
            CachedValue::Partial(..) => unreachable!("partial character not taken by next()"),
            // Nothing cached previously, read from the underlying iterator
            CachedValue::None => 'ignore_interruption: loop {
                if let Some(item) = self.inner.next() {
                    match item {
                        Ok(b) => break Some(Ok(b)),
                        Err(e) => {
                            if e.kind() == std::io::ErrorKind::Interrupted {
                                continue 'ignore_interruption;
                            } else {
                                break Some(Err(e));
                            }
                        }
                    };
                } else {
                    break None;
                }
            },
        };
        *self.cache_mut() = CachedValue::None;
        result
    }
    fn cache(&self) -> &CachedValue {
        &self._cache
    }
    fn cache_mut(&mut self) -> &mut CachedValue {
        &mut self._cache
    }
}

///
/// The `Utf8Iterator` will identify UTF-8 decoding errors returning the enum `Utf8IteratorError`.
///
/// The error will also contain a `Box<[u8]>` with the malformed sequence.
///
/// # Example
///
/// A small tokenizer, which puts back with `unget()` the character that ends a token and handles every kind of error.
///
/// ```
/// # use rustf8::*;
/// # use rustf8::Utf8IteratorError::*;
/// # use std::fmt::Debug;
/// # use std::io::prelude::*;
/// # use std::io::Bytes;
/// # use std::io::Cursor;
/// # enum Token {
/// #     None,
/// #     Identifier(String),
/// #     Integer(String),
/// #     OpenList,
/// #     CloseList,
/// #     Symbol(String),
/// #     Invalid(String),
/// # }
/// # enum State {
/// #     Begin,
/// #     DecodingIdentifier,
/// #     DecodingInteger,
/// #     FinishedToken,
/// #     Finalized,
/// # }
/// # impl PartialEq for Token {
/// #     fn eq(&self, other: &Self) -> bool {
/// #         use Token::*;
/// #         match (self, other) {
/// #             (None, None) => true,
/// #             (OpenList, OpenList) => true,
/// #             (CloseList, CloseList) => true,
/// #             (Identifier(a), Identifier(b)) => a == b,
/// #             (Integer(a), Integer(b)) => a == b,
/// #             (Symbol(a), Symbol(b)) => a == b,
/// #             (Invalid(a), Invalid(b)) => a == b,
/// #             (_, _) => false,
/// #         }
/// #     }
/// # }
/// # impl Clone for Token {
/// #     fn clone(&self) -> Self {
/// #         use Token::*;
/// #         match self {
/// #             None => None,
/// #             OpenList => OpenList,
/// #             CloseList => CloseList,
/// #             Identifier(a) => Identifier(a.to_string()),
/// #             Integer(a) => Integer(a.to_string()),
/// #             Symbol(a) => Symbol(a.to_string()),
/// #             Invalid(a) => Invalid(a.to_string()),
/// #         }
/// #     }
/// # }
/// # impl Debug for Token {
/// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
/// #         use Token::*;
/// #         match self {
/// #             None => f.debug_struct("None").finish(),
/// #             OpenList => f.debug_struct("OpenList").finish(),
/// #             CloseList => f.debug_struct("CloseList").finish(),
/// #             Identifier(a) => f.debug_struct("Identifier").field("string", a).finish(),
/// #             Integer(a) => f.debug_struct("Integer").field("string", a).finish(),
/// #             Symbol(a) => f.debug_struct("Symbol").field("string", a).finish(),
/// #             Invalid(a) => f.debug_struct("Invalid").field("string", a).finish(),
/// #         }
/// #     }
/// # }
/// # fn state_machine(
/// #     chiter: &mut Utf8Iterator<Bytes<Cursor<&str>>>,
/// #     ch: char,
/// #     state: &(State, Token),
/// # ) -> (State, Token) {
/// #     match state {
/// #         (State::FinishedToken, _) | (State::Begin, _) => {
/// #             if ch == '(' {
/// #                 (State::FinishedToken, Token::OpenList)
/// #             } else if ch == ')' {
/// #                 (State::FinishedToken, Token::CloseList)
/// #             } else if ch.is_whitespace() {
/// #                 (State::Begin, Token::None)
/// #             } else if ch.is_alphabetic() || ch == '_' {
/// #                 (State::DecodingIdentifier, Token::Identifier(ch.to_string()))
/// #             } else if ch.is_ascii_digit() {
/// #                 (State::DecodingInteger, Token::Integer(ch.to_string()))
/// #             } else if ch.is_ascii_punctuation() {
/// #                 (State::FinishedToken, Token::Symbol(ch.to_string()))
/// #             } else {
/// #                 (State::FinishedToken, Token::Invalid(ch.to_string()))
/// #             }
/// #         }
/// #         (State::DecodingIdentifier, Token::Identifier(id)) => {
/// #             if ch.is_whitespace() {
/// #                 (State::FinishedToken, Token::Identifier(id.to_string()))
/// #             } else if ch.is_alphanumeric() || ch == '_' {
/// #                 (State::DecodingIdentifier, Token::Identifier(id.to_string() + &ch.to_string()))
/// #             } else {
/// #                 chiter.unget(ch);
/// #                 (State::FinishedToken, Token::Identifier(id.to_string()))
/// #             }
/// #         }
/// #         (State::DecodingInteger, Token::Integer(num)) => {
/// #             if ch.is_whitespace() {
/// #                 (State::FinishedToken, Token::Integer(num.to_string()))
/// #             } else if ch.is_ascii_digit() {
/// #                 (State::DecodingInteger, Token::Integer(num.to_string() + &ch.to_string()))
/// #             } else {
/// #                 chiter.unget(ch);
/// #                 (State::FinishedToken, Token::Integer(num.to_string()))
/// #             }
/// #         }
/// #         (_, _) => panic!("Inconsistent state!"),
/// #     }
/// # }
/// fn next_token(
///     chiter: &mut Utf8Iterator<Bytes<Cursor<&str>>>,
///     state: &mut (State, Token),
/// ) -> Option<Token> {
///     loop {
///         let r = chiter.next();
///         match r {
///             Some(item) => match item {
///                 Ok(ch) => {
///                     *state = state_machine(chiter, ch, state);
///                     if let State::FinishedToken = state.0 {
///                         return Some(state.1.clone());
///                     }
///                 }
///                 Err(e) => match e {
///                     InvalidSequenceError(bytes) => {
///                         panic!("Detected an invalid UTF-8 sequence! {:?}", bytes)
///                     }
///                     LongSequenceError(bytes) => {
///                         panic!("UTF-8 sequence with more than 4 bytes! {:?}", bytes)
///                     }
///                     InvalidCharError(bytes) => panic!(
///                         "UTF-8 sequence resulted in an invalid character! {:?}",
///                         bytes
///                     ),
///                     IoError(ioe, bytes) => panic!(
///                         "I/O error {:?} while decoding the sequence {:?} !",
///                         ioe, bytes
///                     ),
///                 },
///             },
///             None => {
///                 // At the end of the input, return the token still being built, if any.
///                 return match state.0 {
///                     State::DecodingIdentifier | State::DecodingInteger => {
///                         state.0 = State::Finalized;
///                         Some(state.1.clone())
///                     }
///                     _ => None,
///                 };
///             }
///         }
///     }
/// }
/// # fn tokenize(input: &str) -> Vec<Token> {
/// #     let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
/// #     let mut state = (State::Begin, Token::None);
/// #     std::iter::from_fn(|| next_token(&mut chiter, &mut state)).collect()
/// # }
/// # use Token::{CloseList, OpenList};
/// # let id = |s: &str| Token::Identifier(s.to_string());
/// # let int = |s: &str| Token::Integer(s.to_string());
/// # let sym = |s: &str| Token::Symbol(s.to_string());
/// # assert_eq!(
/// #     tokenize("(defun κόσμε (x y) (+ x y))"),
/// #     [OpenList, id("defun"), id("κόσμε"), OpenList, id("x"), id("y"), CloseList,
/// #      OpenList, sym("+"), id("x"), id("y"), CloseList, CloseList]
/// # );
/// # // integers, a token ended by the end of the input, and characters that fit no token
/// # assert_eq!(tokenize("(+ 12 3)"), [OpenList, sym("+"), int("12"), int("3"), CloseList]);
/// # assert_eq!(tokenize("x 42"), [id("x"), int("42")]);
/// # assert_eq!(tokenize("( "), [OpenList]);
/// # assert_eq!(tokenize("a € b"), [id("a"), Token::Invalid("€".to_string()), id("b")]);
/// ```

#[derive(Error, Debug)]
pub enum Utf8IteratorError {
    ///
    /// Returns the IO error coming from the underlying iterator wrapped by `Utf8Iterator`, with the bytes already read
    /// of the character being decoded. Those bytes are kept: the next call to `next()` carries on decoding the same
    /// character, so a temporary error such as `WouldBlock` or `TimedOut` does not lose any data.
    ///
    /// The error `std::io::ErrorKind::Interrupted` is _consumed_ by the iterator and is not returned.
    ///
    /// The `std::io::Error` is also available through `std::error::Error::source()`.
    ///
    #[error("IO Error from the wrapped iterator while decoding sequence: {1:?}")]
    IoError(#[source] std::io::Error, Box<[u8]>),

    /// The decoder found a malformed sequence.
    #[error("The decoder found a malformed sequence while decoding sequence: {0:?}")]
    InvalidSequenceError(Box<[u8]>),

    ///
    /// The sequence is well formed, but it is too long (more than 4 bytes).
    ///
    #[error("The sequence is well formed, but it is too long (more than 4 bytes). Sequence: {0:?}")]
    LongSequenceError(Box<[u8]>),

    ///
    /// Found a well formed UTF-8 sequence, nevertheless the value does not represent a valid character.
    ///
    #[error("Found a well formed UTF-8 sequence, nevertheless the value does not represent a valid character. Sequence: {0:?}")]
    InvalidCharError(Box<[u8]>),
}

use crate::Utf8IteratorError::*;

impl<R> Iterator for Utf8Iterator<R>
where
    R: Iterator<Item = Result<u8, std::io::Error>>,
{
    type Item = Result<char, Utf8IteratorError>;

    /// Decodes the next UTF-8 sequence and returns the corresponding character.
    fn next(&mut self) -> Option<Self::Item> {
        // The number of leading ones of the first byte is the length of the UTF-8 sequence,
        // and the bits after the first zero are the first bits of the value.
        fn length_and_first_bits(first_byte: u8) -> (usize, u32) {
            match first_byte.leading_ones() {
                0 => (1, u32::from(first_byte)),
                // 5 and 6 bytes sequences are read too, to be reported as a single error.
                n @ 2..=6 => (n as usize, u32::from(first_byte & (0x7f >> n))),
                // continuation byte (one leading one), 0xfe or 0xff
                _ => (0, 0),
            }
        }

        // abbreviates the clutter when returning errors, which are the only case where the sequence is copied to the heap
        macro_rules! err {
            ($err:ident, $seq:expr) => {
                Some(Err($err(Box::<[u8]>::from($seq))))
            };
            ($err:ident, $nested:ident, $seq:expr) => {
                Some(Err($err($nested, Box::<[u8]>::from($seq))))
            };
        }

        if let Some(ch) = self.take_unget() {
            // If client code has returned a char, send it back now.
            return Some(Ok(ch));
        }
        // Even the longest (invalid) sequence fits in this buffer, so decoding does not allocate.
        let (mut seq, mut len) = match self.cache() {
            CachedValue::Partial(seq, len) => {
                // An IO error interrupted this character in the previous call, carry on from the bytes already read.
                let partial = (*seq, *len);
                *self.cache_mut() = CachedValue::None;
                partial
            }
            _ => match self.uncache_or_next() {
                // ASCII, the most common case, is a complete character on its own.
                Some(Ok(first_byte)) if first_byte.is_ascii() => return Some(Ok(char::from(first_byte))),
                Some(Ok(first_byte)) => {
                    let mut seq = [0u8; MAX_SEQUENCE_LENGTH];
                    seq[0] = first_byte;
                    (seq, 1)
                }
                Some(Err(e)) => return err![IoError, e, []], // IO Error, not in the middle of a character
                None => {
                    // Stream ended before the character decoding started.
                    *self.cache_mut() = CachedValue::Eof;
                    return None;
                }
            },
        };
        let (nbytes, first_bits) = length_and_first_bits(seq[0]);
        if nbytes == 0 {
            // It seems that the first byte is a continuation or other unexpected value
            return err![InvalidSequenceError, [seq[0]]];
        }
        // The value of the bytes already read, more than the first one only when resuming a character.
        let mut value = seq[1..len]
            .iter()
            .fold(first_bits, |value, byte| (value << 6) | u32::from(byte & 0x3Fu8));
        while len < nbytes {
            match self.uncache_or_next() {
                Some(Ok(next_byte)) if next_byte & 0xC0u8 == 0x80u8 => {
                    // continuation byte
                    seq[len] = next_byte;
                    len += 1;
                    value = (value << 6) | u32::from(next_byte & 0x3Fu8);
                }
                Some(Ok(next_byte)) => {
                    *self.cache_mut() = CachedValue::Byte(next_byte);
                    return err![InvalidSequenceError, &seq[..len]];
                }
                Some(Err(e)) => {
                    // IO Error while decoding one character. The bytes read so far are kept, so the next call
                    // resumes this character.
                    *self.cache_mut() = CachedValue::Partial(seq, len);
                    return err![IoError, e, &seq[..len]];
                }
                None => {
                    // stream ended while decoding one character
                    *self.cache_mut() = CachedValue::Eof;
                    return err![InvalidSequenceError, &seq[..len]];
                }
            }
        }
        let seq = &seq[..len];
        if nbytes > 4 {
            // Invalid sequences.
            // 5 and 6 bytes sequences are no longer valid UTF-8 since RFC 3629.
            return err![LongSequenceError, seq];
        }
        match from_u32(value) {
            // from_u32 rejects UTF-16 surrogates and values above U+10FFFF, and the length check rejects
            // overlong sequences, which encode a value with more bytes than needed.
            // Noncharacters such as U+FFFE and U+FFFF are valid scalar values (Unicode Corrigendum #9),
            // so they are decoded like any other character.
            Some(ch) if ch.len_utf8() == nbytes => Some(Ok(ch)),
            _ => err![InvalidCharError, seq],
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        // Each item consumes between 1 and 6 bytes and interrupted reads produce no item at all, so the only
        // items guaranteed are an ungot character, a cached byte and a character interrupted by an IO error.
        let ungot = usize::from(self._unget.is_some());
        let (cached, upper) = match self.cache() {
            CachedValue::Eof => (0, Some(0)),
            CachedValue::Byte(_) | CachedValue::Partial(..) => {
                (1, self.inner.size_hint().1.and_then(|n| n.checked_add(1)))
            }
            CachedValue::None => (0, self.inner.size_hint().1),
        };
        (ungot + cached, upper.and_then(|n| n.checked_add(ungot)))
    }
}

#[cfg(test)]
mod tests {

    //
    // Original by Markus Kuhn, adapted for HTML by Martin Dürst.
    //
    // UTF-8 decoder capability and stress test
    // ----------------------------------------
    // https://www.w3.org/2001/06/utf-8-wrong/UTF-8-test.html
    //
    use super::*;
    use std::io::prelude::*;
    use std::io::BufReader;
    use std::io::Cursor;
    use tempfile::tempfile;

    macro_rules! match_char_and_sequence {
        ($ch:expr; $($x:expr),*) => {
            let input: Vec<u8> = vec![ $($x),* ];
            let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
            assert_eq!($ch, chiter.next().unwrap().unwrap());
            assert!(chiter.next().is_none());
        };
    }

    macro_rules! match_err_and_sequence {
        ($err:ident; $($x:expr),*) => {
            let input: Vec<u8> = vec![ $($x),* ];
            let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
            let value = chiter.next().unwrap();
            if let Err($err(bytes)) = value {
                assert_eq!(vec![ $($x),* ].into_boxed_slice(), bytes)
            } else {
                panic!("Expecting:{:?}, found: {:?}", stringify!(Err(Utf8IteratorError { $err: [$($x),*]})), value);
            }
            assert!(chiter.next().is_none());
        };
        ($chiter:ident; $err:ident; $($x:expr),*) => {
            let value = $chiter.next().unwrap();
            if let Err($err(bytes)) = value {
                assert_eq!(vec![ $($x),* ].into_boxed_slice(), bytes)
            } else {
                panic!("Expecting:{:?}, found: {:?}", stringify!(Err(Utf8IteratorError { $err: [$($x),*]})), value);
            }
        };
        ($err:ident; $($x:expr),*; $($y:expr),*) => {
            let input: Vec<u8> = vec![ $($x),* ];
            let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
            let value = chiter.next().unwrap();
            if let Err($err(bytes)) = value {
                assert_eq!(vec![ $($y),* ].into_boxed_slice(), bytes)
            } else {
                panic!("Expecting:{:?}, found: {:?}", stringify!(Err(Utf8IteratorError { $err: [$($y),*]})), value);
            }
            assert!(chiter.next().is_none());
        };
    }

    #[test]
    fn _1_some_correct_utf_8_text() {
        let input: Vec<u8> = vec![
            0xce, 0xba, 0xe1, 0xbd, 0xb9, 0xcf, 0x83, 0xce, 0xbc, 0xce, 0xb5,
        ];
        let stream = Cursor::new(input);
        let iter = stream.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        assert_eq!('κ', chiter.next().unwrap().unwrap());
        assert_eq!('ό', chiter.next().unwrap().unwrap());
        assert_eq!('σ', chiter.next().unwrap().unwrap());
        assert_eq!('μ', chiter.next().unwrap().unwrap());
        assert_eq!('ε', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }

    #[test]
    fn _2_1_first_possible_sequence_of_a_certain_length() {
        match_char_and_sequence!['\u{80}'; 0xc2, 0x80 ];
        match_char_and_sequence!['\u{800}'; 0xe0, 0xa0, 0x80 ];
        match_char_and_sequence!['\u{10000}'; 0xf0, 0x90, 0x80, 0x80 ];

        // U+200000: 5 bytes. Unicode escape must be at most 10FFFF in Rust.
        match_err_and_sequence![LongSequenceError; 0b11111000, 0b10000000, 0b10000000, 0b10000000, 0b10000000];

        // U+4000000: 6 bytes. Unicode escape must be at most 10FFFF in Rust.
        match_err_and_sequence![LongSequenceError; 0b11111100, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000 ];
    }

    #[test]
    fn _2_2_last_possible_sequence_of_a_certain_length() {
        // 2.2.1  1 byte  (U-0000007F):        ""
        match_char_and_sequence!['\u{7f}'; 0b_0111_1111];

        // 2.2.2  2 bytes (U-000007FF):        " 0xdf, 0xbf,"
        match_char_and_sequence!['\u{7FF}'; 0b_1101_1111, 0b_1011_1111];

        // 2.2.3  3 bytes (U-0000FFFF):        " 0xef, 0xbf, 0xbf,"
        match_char_and_sequence!['\u{FFFF}'; 0b_1110_1111, 0b_1011_1111, 0b_1011_1111];

        // 2.2.4  4 bytes (U-001FFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidCharError; 0b_1111_0111, 0b1011_1111, 0b1011_1111, 0b1011_1111];

        // Last valid char for Rust: \u{10FFFF}
        match_char_and_sequence!['\u{10FFFF}'; 0b_1111_0100, 0b1000_1111, 0b1011_1111, 0b1011_1111];

        // 2.2.5  5 bytes (U-03FFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![LongSequenceError; 0b_1111_1011, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111];

        // 2.2.6  6 bytes (U-7FFFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![LongSequenceError; 0b_1111_1101, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111 ];
    }

    #[test]
    fn _2_3_other_boundary_conditions() {
        match_char_and_sequence!['\u{00D7FF}'; 0xed, 0x9f, 0xbf ];
        match_char_and_sequence!['\u{00E000}'; 0xee, 0x80, 0x80 ];
        match_char_and_sequence!['\u{00FFFD}'; 0xef, 0xbf, 0xbd ];
        match_char_and_sequence!['\u{10FFFF}'; 0xf4, 0x8f, 0xbf, 0xbf ];
        // U+110000: Unicode escape must be at most 10FFFF in Rust.
        match_err_and_sequence![InvalidCharError; 0xf4u8, 0x90u8, 0x80u8, 0x80u8 ];
    }

    #[test]
    fn _3_1_unexpected_continuation_bytes() {
        match_err_and_sequence![InvalidSequenceError; 0x80 ];
        match_err_and_sequence![InvalidSequenceError; 0xbf ];
        match_char_and_sequence!['\u{80}'; 0xc2, 0x80 ]; // 0b110_00010, 0b10_000000: correctly encoded \u{80}
        assert_eq!('\u{80}', from_u32(0x80).unwrap()); // from_u32 accepts 0x80 as valid and interprets it as \u{80}. Should it?

        // Should return one error per invalid continuation byte.
        let seq: Vec<u8> = vec![0x80, 0xbf, 0x81, 0xb0, 0x80, 0xbf];
        let cmp: Vec<u8> = vec![0x80, 0xbf, 0x81, 0xb0, 0x80, 0xbf];
        let stream = Cursor::new(seq);
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        for expected in cmp {
            match_err_and_sequence!(chiter; InvalidSequenceError; expected);
        }
        assert!(chiter.next().is_none());

        //3.1.9  Sequence of all 64 possible continuation bytes (0x80-0xbf):
        let mut seq: Vec<u8> = vec![];
        for i in 0u8..64u8 {
            seq.push(i | 0b_1000_0000u8)
        }
        let cmp: Vec<u8> = seq.clone();
        let stream = Cursor::new(seq);
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        for expected in cmp {
            match_err_and_sequence!(chiter; InvalidSequenceError; expected);
        }
        assert!(chiter.next().is_none());
    }

    #[test]
    fn _3_2_lonely_start_characters() {
        macro_rules! test_lonely_start {
            ($range:expr) => {
                let mut seq: Vec<u8> = vec![];
                for i in $range {
                    seq.push(i);
                    seq.push(0x20);
                }
                let cmp: Vec<u8> = seq.clone();
                let len = seq.len();
                let stream = Cursor::new(seq);
                let buffered = BufReader::new(stream);
                let iter = buffered.bytes();
                let mut chiter = Utf8Iterator::new(iter);
                for i in 0..len / 2 {
                    match_err_and_sequence!(chiter; InvalidSequenceError; cmp[i * 2]);
                    assert_eq!(' ', chiter.next().unwrap().unwrap());
                }
                assert!(chiter.next().is_none());
            };
        }
        // 3.2.1  All 32 first bytes of 2-byte sequences (0xc0-0xdf),
        //        each followed by a space character:
        test_lonely_start![0xC0u8..=0xdfu8];

        // 3.2.2  All 16 first bytes of 3-byte sequences (0xe0-0xef),
        //        each followed by a space character:
        test_lonely_start![0xe0u8..=0xefu8];

        // 3.2.3  All 8 first bytes of 4-byte sequences (0xf0-0xf7),
        //        each followed by a space character:
        test_lonely_start![0xf0u8..=0xf7u8];

        // 3.2.4  All 4 first bytes of 5-byte sequences (0xf8-0xfb),
        //        each followed by a space character:
        test_lonely_start![0xf8u8..=0xfbu8];

        // 3.2.5  All 2 first bytes of 6-byte sequences (0xfc-0xfd),
        //        each followed by a space character:
        test_lonely_start![0xfcu8..=0xfdu8];
    }

    #[test]
    fn _3_3_sequences_with_last_continuation_byte_missing() {
        // All bytes of an incomplete sequence should be signalled as a single
        // malformed sequence, i.e., you should see only a single replacement
        // characters in each of the next 10 tests. (Characters as in section 2)

        // 3.3.1  2-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1100_0000 ];
        // 3.3.2  3-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1110_0000, 0b1000_0000 ];
        // 3.3.3  4-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_0000, 0b1000_0000 , 0b1000_0000 ];
        // 3.3.4  5-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_1000, 0b1000_0000 , 0b1000_0000 , 0b1000_0000 ];
        // 3.3.5  6-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_1100, 0b1000_0000 , 0b1000_0000 , 0b1000_0000 , 0b1000_0000 ];

        // 3.3.6  2-byte sequence with last byte missing (U-000007FF): " 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1100_1111 ];
        // 3.3.7  3-byte sequence with last byte missing (U-0000FFFF): " 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1110_0111, 0b1011_1111 ];
        // 3.3.8  4-byte sequence with last byte missing (U-001FFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_0111, 0b1011_1111 , 0b1011_1111 ];
        // 3.3.9  5-byte sequence with last byte missing (U-03FFFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_1011, 0b1011_1111 , 0b1011_1111 , 0b1011_1111 ];
        // 3.3.10 6-byte sequence with last byte missing (U-7FFFFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequenceError; 0b1111_1101, 0b1011_1111 , 0b1011_1111 , 0b1011_1111 , 0b1011_1111 ];
    }

    #[test]
    fn _3_4_concatenation_of_incomplete_sequences() {
        // All the 10 sequences of 3.3 concatenated, you should see 10 malformed sequences being signalled:
        let input: Vec<u8> = vec![
            // 2 byte sequence with a missing trailing byte
            0b1100_0000,
            // 3 byte sequence with a missing trailing byte
            0b1110_0000,
            0b1000_0000,
            // 4 byte sequence with a missing trailing byte
            0b1111_0000,
            0b1000_0000,
            0b1000_0000,
            // 5 byte sequence with a missing trailing byte
            0b1111_1000,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000,
            // 6 byte sequence with a missing trailing byte
            0b1111_1100,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000,
            // 2 byte sequence with a missing trailing byte
            0b1100_1111,
            // 3 byte sequence with a missing trailing byte
            0b1110_0111,
            0b1011_1111,
            // 4 byte sequence with a missing trailing byte
            0b1111_0111,
            0b1011_1111,
            0b1011_1111,
            // 5 byte sequence with a missing trailing byte
            0b1111_1011,
            0b1011_1111,
            0b1011_1111,
            0b1011_1111,
            // 6 byte sequence with a missing trailing byte
            0b1111_1101,
            0b1011_1111,
            0b1011_1111,
            0b1011_1111,
            0b1011_1111,
        ];

        let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());

        // 2 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1100_0000];
        // 3 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1110_0000, 0b1000_0000];
        // 4 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1111_0000, 0b1000_0000, 0b1000_0000];
        // 5 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1111_1000, 0b1000_0000, 0b1000_0000, 0b1000_0000];
        // 6 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError;
            0b1111_1100,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000
        ];
        // 2 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1100_1111];
        // 3 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1110_0111, 0b1011_1111];
        // 4 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1111_0111, 0b1011_1111, 0b1011_1111];
        // 5 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1111_1011, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // 6 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError;
            0b1111_1101,
            0b1011_1111,
            0b1011_1111,
            0b1011_1111,
            0b1011_1111
        ];

        assert!(chiter.next().is_none());
    }

    #[test]
    fn _4_1_examples_of_an_overlong_ascii_character() {
        // With a safe UTF-8 decoder, all of the following five overlong
        // representations of the ASCII character slash ("/") should be rejected
        // like a malformed UTF-8 sequence, for instance by substituting it with
        // a replacement character. If you see a slash below, you do not have a
        // safe UTF-8 decoder!

        // 4.1.1 U+002F = c0 af
        match_err_and_sequence!(InvalidCharError; 0xc0, 0xaf);
        // 4.1.2 U+002F = e0 80 af
        match_err_and_sequence!(InvalidCharError; 0xe0, 0x80, 0xaf);
        // 4.1.3 U+002F = f0 80 80 af
        match_err_and_sequence!(InvalidCharError; 0xf0, 0x80, 0x80, 0xaf);
        // 4.1.4 U+002F = f8 80 80 80 af
        match_err_and_sequence!(LongSequenceError; 0xf8, 0x80, 0x80, 0x80, 0xaf);
        // 4.1.5 U+002F = fc 80 80 80 80 af
        match_err_and_sequence!(LongSequenceError; 0xfc, 0x80, 0x80, 0x80, 0x80, 0xaf);
    }
    #[test]
    fn _4_2_maximum_overlong_sequences() {
        // Below you see the highest Unicode value that is still resulting in an
        // overlong sequence if represented with the given number of bytes. This
        // is a boundary test for safe UTF-8 decoders. All five characters should
        // be rejected like malformed UTF-8 sequences.

        // 4.2.1  U-0000007F = c1 bf
        match_err_and_sequence!(InvalidCharError; 0xc1, 0xbf);
        // 4.2.2  U-000007FF = e0 9f bf
        match_err_and_sequence!(InvalidCharError; 0xe0, 0x9f, 0xbf);
        // 4.2.3  U-0000FFFF = f0 8f bf bf
        match_err_and_sequence!(InvalidCharError; 0xf0, 0x8f, 0xbf, 0xbf);
        // 4.2.4  U-001FFFFF = f8 87 bf bf bf
        match_err_and_sequence!(LongSequenceError; 0xf8, 0x87, 0xbf, 0xbf, 0xbf);
        // 4.2.5  U-03FFFFFF = fc 83 bf bf bf bf
        match_err_and_sequence!(LongSequenceError; 0xfc, 0x83, 0xbf, 0xbf, 0xbf, 0xbf);
    }

    #[test]
    fn _4_3_overlong_representation_of_the_nul_character() {
        // The following five sequences should also be rejected like malformed
        // UTF-8 sequences and should not be treated like the ASCII NUL
        // character.

        // 4.3.1  U+0000 = c0 80
        match_err_and_sequence!(InvalidCharError; 0xc0, 0x80);
        // 4.3.2  U+0000 = e0 80 80
        match_err_and_sequence!(InvalidCharError; 0xe0, 0x80, 0x80);
        // 4.3.3  U+0000 = f0 80 80 80
        match_err_and_sequence!(InvalidCharError; 0xf0, 0x80, 0x80, 0x80);
        // 4.3.4  U+0000 = f8 80 80 80 80
        match_err_and_sequence!(LongSequenceError; 0xf8, 0x80, 0x80, 0x80, 0x80);
        // 4.3.5  U+0000 = fc 80 80 80 80 80
        match_err_and_sequence!(LongSequenceError; 0xfc, 0x80, 0x80, 0x80, 0x80, 0x80);
    }

    #[test]
    fn _5_illegal_code_positions() {
        // The UTF-16 surrogates in 5.1 and 5.2 should be rejected like malformed
        // sequences, because they never represent valid ISO 10646 characters and
        // a UTF-8 decoder that accepts them might introduce security problems
        // comparable to overlong UTF-8 sequences. The noncharacters in 5.3 are
        // valid characters, see the note there.

        // 5.1 Single UTF-16 surrogates
        // 5.1.1  U+D800 = ed a0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xa0, 0x80);
        // 5.1.2  U+DB7F = ed ad bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xad, 0xbf);
        // 5.1.3  U+DB80 = ed ae 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xae, 0x80);
        // 5.1.4  U+DBFF = ed af bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xaf, 0xbf);
        // 5.1.5  U+DC00 = ed b0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xb0, 0x80);
        // 5.1.6  U+DF80 = ed be 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbe, 0x80);
        // 5.1.7  U+DFFF = ed bf bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbf, 0xbf);

        // 5.2 Paired UTF-16 surrogates
        // Leading, also called high, surrogates are from D800 to DBFF, and trailing, or low, surrogates are from DC00 to DFFF.
        //
        //5.2.1  U+D800 U+DC00 = ed a0 80 ed b0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xa0, 0x80);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xb0, 0x80);
        //5.2.2  U+D800 U+DFFF = ed a0 80 ed bf bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xa0, 0x80);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbf, 0xbf);
        //5.2.3  U+DB7F U+DC00 = ed ad bf ed b0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xad, 0xbf);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xb0, 0x80);
        //5.2.4  U+DB7F U+DFFF = ed ad bf ed bf bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xad, 0xbf);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbf, 0xbf);
        //5.2.5  U+DB80 U+DC00 = ed ae 80 ed b0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xae, 0x80);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xb0, 0x80);
        //5.2.6  U+DB80 U+DFFF = ed ae 80 ed bf bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xae, 0x80);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbf, 0xbf);
        //5.2.7  U+DBFF U+DC00 = ed af bf ed b0 80
        match_err_and_sequence!(InvalidCharError; 0xed, 0xaf, 0xbf);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xb0, 0x80);
        //5.2.8  U+DBFF U+DFFF = ed af bf ed bf bf
        match_err_and_sequence!(InvalidCharError; 0xed, 0xaf, 0xbf);
        match_err_and_sequence!(InvalidCharError; 0xed, 0xbf, 0xbf);

        // 5.3 Noncharacter code positions
        // Older versions of the Unicode Standard said noncharacters "should never be interchanged".
        // Unicode Corrigendum #9 dropped that restriction: they are valid scalar values and a UTF-8
        // decoder must pass them through. Applications that give them internal meaning must check for them.
        //5.3.1  U+FFFE = ef bf be
        match_char_and_sequence!['\u{FFFE}'; 0xef, 0xbf, 0xbe];
        //5.3.2  U+FFFF = ef bf bf
        match_char_and_sequence!['\u{FFFF}'; 0xef, 0xbf, 0xbf];
        //5.3.3  U+FDD0 .. U+FDEF
        match_char_and_sequence!['\u{FDD0}'; 0xef, 0xb7, 0x90];
        match_char_and_sequence!['\u{FDEF}'; 0xef, 0xb7, 0xaf];
        //5.3.4  U+nFFFE U+nFFFF (for n = 1..10)
        match_char_and_sequence!['\u{1FFFE}'; 0xf0, 0x9f, 0xbf, 0xbe];
        match_char_and_sequence!['\u{10FFFE}'; 0xf4, 0x8f, 0xbf, 0xbe];
    }

    #[test]
    fn read_from_cursor() {
        let stream = Cursor::new("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ");
        let mut chiter = Utf8Iterator::new(stream.bytes());

        assert_eq!('来', chiter.next().unwrap().unwrap());
        assert_eq!('提', chiter.next().unwrap().unwrap());
        assert_eq!('供', chiter.next().unwrap().unwrap());
        assert_eq!('和', chiter.next().unwrap().unwrap());
        assert_eq!('改', chiter.next().unwrap().unwrap());
        assert_eq!('进', chiter.next().unwrap().unwrap());
        assert_eq!('网', chiter.next().unwrap().unwrap());
        assert_eq!('站', chiter.next().unwrap().unwrap());
        assert_eq!('体', chiter.next().unwrap().unwrap());
        assert_eq!('验', chiter.next().unwrap().unwrap());
        assert_eq!('e', chiter.next().unwrap().unwrap());
        assert_eq!('r', chiter.next().unwrap().unwrap());
        assert_eq!('s', chiter.next().unwrap().unwrap());
        assert_eq!('é', chiter.next().unwrap().unwrap());
        assert_eq!('®', chiter.next().unwrap().unwrap());
        assert_eq!('þ', chiter.next().unwrap().unwrap());
        assert_eq!('ü', chiter.next().unwrap().unwrap());
        assert_eq!('ú', chiter.next().unwrap().unwrap());
        assert_eq!('ä', chiter.next().unwrap().unwrap());
        assert_eq!('å', chiter.next().unwrap().unwrap());
        assert_eq!('á', chiter.next().unwrap().unwrap());
        assert_eq!('ß', chiter.next().unwrap().unwrap());
        assert_eq!('ð', chiter.next().unwrap().unwrap());
        assert_eq!('f', chiter.next().unwrap().unwrap());
        assert_eq!('g', chiter.next().unwrap().unwrap());
        assert_eq!('h', chiter.next().unwrap().unwrap());
        assert_eq!('j', chiter.next().unwrap().unwrap());
        assert_eq!('œ', chiter.next().unwrap().unwrap());
        assert_eq!('ø', chiter.next().unwrap().unwrap());
        assert_eq!('µ', chiter.next().unwrap().unwrap());
        assert_eq!('ñ', chiter.next().unwrap().unwrap());
        assert_eq!('b', chiter.next().unwrap().unwrap());
        assert_eq!('v', chiter.next().unwrap().unwrap());
        assert_eq!('©', chiter.next().unwrap().unwrap());
        assert_eq!('x', chiter.next().unwrap().unwrap());
        assert_eq!('æ', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }

    #[test]
    fn read_from_file() {
        let mut file = tempfile().unwrap();
        file.write_all("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ".as_bytes())
            .unwrap();
        file.flush().unwrap();
        file.seek(std::io::SeekFrom::Start(0)).unwrap();
        let mut chiter = Utf8Iterator::new(BufReader::new(file).bytes());

        assert_eq!('来', chiter.next().unwrap().unwrap());
        assert_eq!('提', chiter.next().unwrap().unwrap());
        assert_eq!('供', chiter.next().unwrap().unwrap());
        assert_eq!('和', chiter.next().unwrap().unwrap());
        assert_eq!('改', chiter.next().unwrap().unwrap());
        assert_eq!('进', chiter.next().unwrap().unwrap());
        assert_eq!('网', chiter.next().unwrap().unwrap());
        assert_eq!('站', chiter.next().unwrap().unwrap());
        assert_eq!('体', chiter.next().unwrap().unwrap());
        assert_eq!('验', chiter.next().unwrap().unwrap());
        assert_eq!('e', chiter.next().unwrap().unwrap());
        assert_eq!('r', chiter.next().unwrap().unwrap());
        assert_eq!('s', chiter.next().unwrap().unwrap());
        assert_eq!('é', chiter.next().unwrap().unwrap());
        assert_eq!('®', chiter.next().unwrap().unwrap());
        assert_eq!('þ', chiter.next().unwrap().unwrap());
        assert_eq!('ü', chiter.next().unwrap().unwrap());
        assert_eq!('ú', chiter.next().unwrap().unwrap());
        assert_eq!('ä', chiter.next().unwrap().unwrap());
        assert_eq!('å', chiter.next().unwrap().unwrap());
        assert_eq!('á', chiter.next().unwrap().unwrap());
        assert_eq!('ß', chiter.next().unwrap().unwrap());
        assert_eq!('ð', chiter.next().unwrap().unwrap());
        assert_eq!('f', chiter.next().unwrap().unwrap());
        assert_eq!('g', chiter.next().unwrap().unwrap());
        assert_eq!('h', chiter.next().unwrap().unwrap());
        assert_eq!('j', chiter.next().unwrap().unwrap());
        assert_eq!('œ', chiter.next().unwrap().unwrap());
        assert_eq!('ø', chiter.next().unwrap().unwrap());
        assert_eq!('µ', chiter.next().unwrap().unwrap());
        assert_eq!('ñ', chiter.next().unwrap().unwrap());
        assert_eq!('b', chiter.next().unwrap().unwrap());
        assert_eq!('v', chiter.next().unwrap().unwrap());
        assert_eq!('©', chiter.next().unwrap().unwrap());
        assert_eq!('x', chiter.next().unwrap().unwrap());
        assert_eq!('æ', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }

    #[test]
    fn read_file_with_errors() {
        let mut file = tempfile().unwrap();
        let input: Vec<u8> = vec![
            // "κόσμε"
            0xce,
            0xba,
            0xe1,
            0xbd,
            0xb9,
            0xcf,
            0x83,
            0xce,
            0xbc,
            0xce,
            0xb5,
            // 4 byte sequence with a missing trailing byte
            0b1111_0000,
            0b1000_0000,
            0b1000_0000,
            // "κόσμε"
            0xce,
            0xba,
            0xe1,
            0xbd,
            0xb9,
            0xcf,
            0x83,
            0xce,
            0xbc,
            0xce,
            0xb5,
            // Unexpected sequence bytes
            0x80,
            0xbf,
            // "κόσμε"
            0xce,
            0xba,
            0xe1,
            0xbd,
            0xb9,
            0xcf,
            0x83,
            0xce,
            0xbc,
            0xce,
            0xb5,
            // Over long ASCII
            0xf0,
            0x80,
            0x80,
            0xaf,
            // UTF-16 Surrogate
            0xed,
            0xa0,
            0x80,
            // "κόσμε"
            0xce,
            0xba,
            0xe1,
            0xbd,
            0xb9,
            0xcf,
            0x83,
            0xce,
            0xbc,
            0xce,
            0xb5,
        ];
        file.write_all(input.as_slice()).unwrap();
        file.flush().unwrap();
        file.seek(std::io::SeekFrom::Start(0)).unwrap();
        let mut chiter = Utf8Iterator::new(BufReader::new(file).bytes());

        macro_rules! match_kosme {
            ($iter:ident) => {
                assert_eq!('κ', $iter.next().unwrap().unwrap());
                assert_eq!('ό', $iter.next().unwrap().unwrap());
                assert_eq!('σ', $iter.next().unwrap().unwrap());
                assert_eq!('μ', $iter.next().unwrap().unwrap());
                assert_eq!('ε', $iter.next().unwrap().unwrap());
            };
        }

        // "κόσμε"
        match_kosme!(chiter);
        // 4 byte sequence with a missing trailing byte
        match_err_and_sequence![chiter; InvalidSequenceError; 0b1111_0000, 0b1000_0000, 0b1000_0000];
        // "κόσμε"
        match_kosme!(chiter);
        // Unexpected sequence bytes
        match_err_and_sequence!(chiter; InvalidSequenceError; 0x80);
        // Unexpected sequence bytes
        match_err_and_sequence!(chiter; InvalidSequenceError; 0xbf);
        // "κόσμε"
        match_kosme!(chiter);
        // Over long ASCII
        match_err_and_sequence!(chiter; InvalidCharError; 0xf0, 0x80, 0x80, 0xaf);
        // UTF-16 Surrogate
        match_err_and_sequence!(chiter; InvalidCharError; 0xed, 0xa0, 0x80);
        // "κόσμε"
        match_kosme!(chiter);

        assert!(chiter.next().is_none());
    }

    #[test]
    #[should_panic]
    fn unget_panic() {
        let input: Vec<u8> = vec![
            0xce, 0xba, 0xe1, 0xbd, 0xb9, 0xcf, 0x83, 0xce, 0xbc, 0xce, 0xb5,
        ];
        let stream = Cursor::new(input);
        let iter = stream.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        assert_eq!('κ', chiter.next().unwrap().unwrap());
        chiter.unget('ε');
        chiter.unget('κ');

    }

    #[test]
    fn size_hint_bounds() {
        // 4 bytes, a single character
        let input: Vec<std::io::Result<u8>> = vec![Ok(0xf0), Ok(0x9f), Ok(0x98), Ok(0x80)];
        let mut chiter = Utf8Iterator::new(input.into_iter());
        assert_eq!((0, Some(4)), chiter.size_hint());
        chiter.unget('x');
        assert_eq!((1, Some(5)), chiter.size_hint());
        assert_eq!(2, chiter.count());

        // the byte cached after a malformed sequence is always one more item
        let input: Vec<std::io::Result<u8>> = vec![Ok(0xce), Ok(0x20)];
        let mut chiter = Utf8Iterator::new(input.into_iter());
        assert!(chiter.next().unwrap().is_err());
        assert_eq!((1, Some(1)), chiter.size_hint());
        assert_eq!(' ', chiter.next().unwrap().unwrap());
        assert_eq!((0, Some(0)), chiter.size_hint());
        assert!(chiter.next().is_none());
        assert_eq!((0, Some(0)), chiter.size_hint());
    }

    #[test]
    fn io_error_keeps_source_and_sequence() {
        use std::error::Error;
        let input: Vec<std::io::Result<u8>> = vec![
            Ok(0xce),
            Err(std::io::Error::other("device unplugged")),
            Ok(0x41),
        ];
        let mut chiter = Utf8Iterator::new(input.into_iter());
        let err = chiter.next().unwrap().unwrap_err();
        assert_eq!("device unplugged", err.source().unwrap().to_string());
        assert!(err.to_string().ends_with("[206]"));
        match err {
            IoError(_, bytes) => assert_eq!([0xce].as_slice(), &*bytes),
            _ => panic!("Expecting an IoError, found: {:?}", err),
        }
        // decoding carries on with the bytes read before the error, and 0x41 is not a continuation byte
        match_err_and_sequence!(chiter; InvalidSequenceError; 0xce);
        assert_eq!('A', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }

    #[test]
    fn io_error_in_the_middle_of_a_character_is_resumable() {
        for kind in [std::io::ErrorKind::WouldBlock, std::io::ErrorKind::TimedOut] {
            // 'κ' = ce ba, interrupted by a temporary error
            let input: Vec<std::io::Result<u8>> = vec![Ok(0xce), Err(kind.into()), Ok(0xba)];
            let mut chiter = Utf8Iterator::new(input.into_iter());
            match chiter.next().unwrap() {
                Err(IoError(e, bytes)) => {
                    assert_eq!(kind, e.kind());
                    assert_eq!([0xce].as_slice(), &*bytes);
                }
                other => panic!("Expecting an IoError, found: {:?}", other),
            }
            // the interrupted character is one more item
            assert_eq!((1, Some(2)), chiter.size_hint());
            assert_eq!('κ', chiter.next().unwrap().unwrap());
            assert!(chiter.next().is_none());
        }

        // a stream that ends after the error reports the incomplete sequence
        let input: Vec<std::io::Result<u8>> =
            vec![Ok(0xe1), Ok(0xbd), Err(std::io::ErrorKind::WouldBlock.into())];
        let mut chiter = Utf8Iterator::new(input.into_iter());
        assert!(matches!(chiter.next(), Some(Err(IoError(_, _)))));
        match_err_and_sequence!(chiter; InvalidSequenceError; 0xe1, 0xbd);
        assert!(chiter.next().is_none());
    }

    #[test]
    fn interrupted_reads_are_skipped() {
        let input: Vec<std::io::Result<u8>> = vec![
            Err(std::io::ErrorKind::Interrupted.into()),
            Ok(0xce),
            Err(std::io::ErrorKind::Interrupted.into()),
            Ok(0xba),
        ];
        let mut chiter = Utf8Iterator::new(input.into_iter());
        assert_eq!('κ', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }
}
