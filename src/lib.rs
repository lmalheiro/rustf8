use std::char::from_u32;
use std::ops::RangeInclusive;

// Range of codes reserverd for UTF-16 surrogates aren't valid UTF-8
const LOW_UTF_16_SURROGATE: u32 = 0xD800;
const HIGH_UTF_16_SURROGATE: u32 = 0xDFFF;

enum CachedValue {
    None,
    Byte(u8),
    Eof,
}

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
    pub fn new(inner: R) -> Self {
        Utf8Iterator {
            inner,
            _cache: CachedValue::None,
            _unget: None,
        }
    }
    pub fn unget(&mut self, ch: char) {
        match self._unget {
            None => self._unget = Some(ch),
            Some(_) => {
                panic!("Cannot return character before consuming the previous cached value.")
            }
        }
    }
    fn get_unget(&mut self) -> Option<char> {
        self._unget.take()
    }
    fn get_next(&mut self) -> Option<R::Item> {
        match self._cache {
            CachedValue::None => self.inner.next(),
            CachedValue::Byte(b) => {
                self._cache = CachedValue::None;
                Some(Ok(b))
            }
            CachedValue::Eof => None,
        }
    }
    fn set_next(&mut self, chd: CachedValue) {
        self._cache = chd
    }
    fn get_cache(&self) -> &CachedValue {
        &self._cache
    }
}

pub enum Utf8IteratorError {
    IoError(std::io::Error, Box<[u8]>),
    InvalidSequence(Box<[u8]>),
    LongSequence(Box<[u8]>),
    InvalidChar(Box<[u8]>),
}

impl std::fmt::Debug for Utf8IteratorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IoError(err, bytes) => f
                .debug_struct("Utf8IteratorError")
                .field("IoError", err)
                .field("sequence", bytes)
                .finish(),
            InvalidSequence(bytes) => f
                .debug_struct("Utf8IteratorError")
                .field("InvalidSequence", bytes)
                .finish(),
            LongSequence(bytes) => f
                .debug_struct("Utf8IteratorError")
                .field("LongSequence", bytes)
                .finish(),
            InvalidChar(bytes) => f
                .debug_struct("Utf8IteratorError")
                .field("InvalidChar", bytes)
                .finish(),
        }
    }
}

use crate::Utf8IteratorError::*;

impl<R> Iterator for Utf8Iterator<R>
where
    R: Iterator<Item = Result<u8, std::io::Error>>,
{
    type Item = Result<char, Utf8IteratorError>;
    fn next(&mut self) -> Option<Self::Item> {
        // identify the length of the UTF-8 sequece, then extracts the first bits and returns the valid range of code points too.
        fn length_first_bits_and_valid_range(first_byte: u8) -> (usize, u32, RangeInclusive<u32>) {
            // Uses a mask to isolate the bits indicating the sequence length.
            // Extracts the first bits belonging the UTF-8 sequence using the negated mask.
            macro_rules! mktest {
                ($nbits:literal, $mask:literal, $range:expr) => {
                    if first_byte & $mask == ($mask << 1) {
                        return ($nbits, u32::from(first_byte & !$mask), $range);
                    }
                };
            }

            // 1 byte sequence
            if first_byte & 0b_1000_0000_u8 == 0 {
                return (1, u32::from(first_byte), 0x00..=0xf7);
            }
            mktest!(2, 0b_1110_0000_u8, 0x0080..=0x07ff); // 2 bytes sequence
            mktest!(3, 0b_1111_0000_u8, 0x0800..=0xffff); // 3 bytes sequence
            mktest!(4, 0b_1111_1000_u8, 0x10000..=0x10ffff); // 4 bytes sequence
            mktest!(5, 0b_1111_1100_u8, 0..=0); // 5 bytes sequence, invalid
            mktest!(6, 0b_1111_1110_u8, 0..=0); // 6 bytes sequence, invalid
            return (0, 0u32, 0..=0); // continuation byte or other unexpected char
        }

        // abbrevates the clutter when returning errors
        macro_rules! err {
            ($err:ident, $slice:ident) => {
                Some(Err($err($slice.into_boxed_slice())))
            };
            ($err:ident, $nested:ident, $slice:ident) => {
                Some(Err($err($nested, $slice.into_boxed_slice())))
            };
            ($err:ident, $nested:ident, $slice:expr) => {
                Some(Err($err($nested, $slice.into_boxed_slice())))
            };
        }

        macro_rules! is_not_in_surrogate_range {
            ($value:ident) => {
                $value <= LOW_UTF_16_SURROGATE || HIGH_UTF_16_SURROGATE <= $value
            };
        }

        macro_rules! is_not_byte_order_mark {
            ($value:ident) => {
                $value != 0xfffe
            };
        }
        macro_rules! is_not_char {
            ($value:ident) => {
                $value != 0xffff
            };
        }

        if let Some(ch) = self.get_unget() {
            // If client code has returned a char, send it back now.
            return Some(Ok(ch));
        } else if let CachedValue::Eof = self.get_cache() {
            // If in the previous call we exited because the stream had ended, it means that we returned
            // the character (probably as an invalid sequence) and now we have to indicate the end of the stream.
            return None;
        } else if let Some(has_input) = self.get_next() {
            match has_input {
                Err(e) => return err![IoError, e, Vec::<u8>::new()], // IO Error, not in the middle of a character
                Ok(first_byte) => {
                    let mut seq = Vec::<u8>::new();
                    seq.push(first_byte);
                    let (nbytes, mut builder, range) =
                        length_first_bits_and_valid_range(first_byte);
                    if nbytes >= 1 {
                        'read_seq: while seq.len() < nbytes {
                            if let Some(has_input) = self.get_next() {
                                match has_input {
                                    Err(e) => {
                                        match e.kind() {
                                            std::io::ErrorKind::Interrupted => continue 'read_seq, // interruped by OS
                                            _ => return err![IoError, e, seq], // IO Error while decoding one character
                                        }
                                    }
                                    Ok(next_byte) => {
                                        if next_byte & 0xC0u8 == 0x80u8 {
                                            // continuation byte
                                            seq.push(next_byte);
                                            builder =
                                                (builder << 6) | u32::from(next_byte & 0x3Fu8);
                                        } else {
                                            self.set_next(CachedValue::Byte(next_byte));
                                            return err![InvalidSequence, seq];
                                        }
                                    }
                                }
                            } else {
                                // stream ended while decoding one character
                                self.set_next(CachedValue::Eof);
                                return err![InvalidSequence, seq];
                            }
                        }
                        if nbytes < 5 {
                            if range.contains(&builder)
                                && is_not_in_surrogate_range!(builder)
                                && is_not_byte_order_mark!(builder)
                                && is_not_char!(builder)
                            {
                                if let Some(ch) = from_u32(builder) {
                                    // normal, sane, character according to Rust.
                                    return Some(Ok(ch));
                                } else {
                                    return err![InvalidChar, seq];
                                }
                            } else {
                                return err![InvalidChar, seq];
                            }
                        } else {
                            // Invalid sequences.
                            // 5 and 6 bytes unicode will overflow the builder variable.
                            return err![LongSequence, seq];
                        }
                    } else {
                        // It seems that the first byte is a continuation or other unexpected value
                        return err![InvalidSequence, seq];
                    }
                }
            }
        } else {
            // Stream ended before the character decoding started.
            self.set_next(CachedValue::Eof);
            return None;
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
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
    use std::fs::File;
    use std::io::prelude::*;
    use std::io::BufReader;
    use std::io::Cursor;

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

    macro_rules! match_incomplete {
        ($chiter:ident; $($seq:expr),*) => {
            let value = $chiter.next().unwrap();
        if let Err(InvalidSequence(bytes)) = value {
            assert_eq!(vec![ $($seq),* ].into_boxed_slice(), bytes)
        } else {
            panic!(value);
        }
        };
    }

    #[test]
    fn _2_1_first_possible_sequence_of_a_certain_length() {
        match_char_and_sequence!['\u{80}'; 0xc2, 0x80 ];
        match_char_and_sequence!['\u{800}'; 0xe0, 0xa0, 0x80 ];
        match_char_and_sequence!['\u{10000}'; 0xf0, 0x90, 0x80, 0x80 ];

        // I understand that we can't store 5 and 6 bytes Unicode in Rust characters, so it seems reasonable to return a replacement char.
        // U+200000: 5 bytes. Unicode escape must be at most 10FFFF in Rust.
        //match_char_and_sequence![REPLACEMENT_CHARACTER; 0b11111000, 0b10000000, 0b10000000, 0b10000000, 0b10000000 ];

        match_err_and_sequence![LongSequence; 0b11111000, 0b10000000, 0b10000000, 0b10000000, 0b10000000];

        // I understand that we can't store 5 and 6 bytes Unicode in Rust characters, so it seems reasonable to return a replacement char.
        // U+4000000: 6 bytes. Unicode escape must be at most 10FFFF in Rust.
        match_err_and_sequence![LongSequence; 0b11111100, 0b10000000, 0b10000000, 0b10000000, 0b10000000, 0b10000000 ];
    }

    #[test]
    fn _2_2_last_possible_sequence_of_a_certain_length() {
        // 2.2.1  1 byte  (U-0000007F):        ""
        match_char_and_sequence!['\u{7f}'; 0b_0111_1111];
        // 2.2.2  2 bytes (U-000007FF):        " 0xdf, 0xbf,"
        match_char_and_sequence!['\u{7FF}'; 0b_1101_1111, 0b_1011_1111];
        // 2.2.3  3 bytes (U-0000FFFF):        " 0xef, 0xbf, 0xbf,"
        // U+FFFF is not a character: match_char_and_sequence!['\u{FFFF}'; 0b_1110_1111, 0b_1011_1111, 0b_1011_1111];
        // 2.2.4  4 bytes (U-001FFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        // I understand that it is an invalid char for Rust
        match_err_and_sequence![InvalidChar; 0b_1111_0111, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // Last valid char for Rust: \u{10FFFF}
        match_char_and_sequence!['\u{10FFFF}'; 0b_1111_0100, 0b1000_1111, 0b1011_1111, 0b1011_1111];
        // 2.2.5  5 bytes (U-03FFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        // Can't represent that using Rust's char
        match_err_and_sequence![LongSequence; 0b_1111_1011, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // 2.2.6  6 bytes (U-7FFFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        // Can't represent that using Rust's char
        match_err_and_sequence![LongSequence; 0b_1111_1101, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111 ];
    }

    #[test]
    fn _2_3_other_boundary_conditions() {
        match_char_and_sequence!['\u{00D7FF}'; 0xed, 0x9f, 0xbf ];
        match_char_and_sequence!['\u{00E000}'; 0xee, 0x80, 0x80 ];
        match_char_and_sequence!['\u{00FFFD}'; 0xef, 0xbf, 0xbd ];
        match_char_and_sequence!['\u{10FFFF}'; 0xf4, 0x8f, 0xbf, 0xbf ];
        // U+110000: Unicode escape must be at most 10FFFF in Rust.
        match_err_and_sequence![InvalidChar; 0xf4u8, 0x90u8, 0x80u8, 0x80u8 ];
    }

    #[test]
    fn _3_1_unexpected_continuation_bytes() {
        match_err_and_sequence![InvalidSequence; 0x80 ];
        match_err_and_sequence![InvalidSequence; 0xbf ];
        match_char_and_sequence!['\u{80}'; 0b110_0_0010, 0b10_00_0000 ]; // correctly encoded \u{80}
        assert_eq!('\u{80}', from_u32(0x80).unwrap()); // from_u32 accepts 0x80 as valid and interprets it as \u{80}. Should it?

        // Should return one error per invalid continuation byte.
        let seq: Vec<u8> = vec![0x80, 0xbf, 0x81, 0xb0, 0x80, 0xbf];
        let cmp: Vec<u8> = vec![0x80, 0xbf, 0x81, 0xb0, 0x80, 0xbf];
        let len = seq.len();
        let stream = Cursor::new(seq);
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        for i in 0..len {
            if let Err(InvalidSequence(bytes)) = chiter.next().unwrap() {
                assert_eq!(cmp[i], bytes[0]);
            }
        }
        assert!(chiter.next().is_none());

        //3.1.9  Sequence of all 64 possible continuation bytes (0x80-0xbf):
        let mut seq: Vec<u8> = vec![];
        for i in 0u8..64u8 {
            seq.push(i | 0b_1000_0000u8)
        }
        let cmp: Vec<u8> = seq.clone();
        let len = seq.len();
        let stream = Cursor::new(seq);
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        for i in 0..len {
            if let Err(InvalidSequence(bytes)) = chiter.next().unwrap() {
                assert_eq!(cmp[i], bytes[0]);
            }
        }
        assert!(chiter.next().is_none());
    }

    #[test]
    fn _3_2_lonely_start_characters() {
        macro_rules! test_lonely_start {
            ($range:expr) => {
                let mut seq: Vec<u8> = vec![];
                //eprintln!("---------------- {} -------------------", stringify![$range]);
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
                    if let Err(InvalidSequence(bytes)) = chiter.next().unwrap() {
                        assert_eq!(&cmp[i * 2..i * 2 + 1], bytes.as_ref());
                        //eprintln!("{:02x}", cmp[i*2]);
                    }
                    if let Ok(ch) = chiter.next().unwrap() {
                        assert_eq!(ch, ' ');
                    }
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
        match_err_and_sequence![InvalidSequence; 0b1100_0000 ];
        // 3.3.2  3-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1110_0000, 0b1000_0000 ];
        // 3.3.3  4-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_0000, 0b1000_0000 , 0b1000_0000 ];
        // 3.3.4  5-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_1000, 0b1000_0000 , 0b1000_0000 , 0b1000_0000 ];
        // 3.3.5  6-byte sequence with last byte missing (U+0000):     " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_1100, 0b1000_0000 , 0b1000_0000 , 0b1000_0000 , 0b1000_0000 ];

        // 3.3.6  2-byte sequence with last byte missing (U-000007FF): " 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1100_1111 ];
        // 3.3.7  3-byte sequence with last byte missing (U-0000FFFF): " 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1110_0111, 0b1011_1111 ];
        // 3.3.8  4-byte sequence with last byte missing (U-001FFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_0111, 0b1011_1111 , 0b1011_1111 ];
        // 3.3.9  5-byte sequence with last byte missing (U-03FFFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_1011, 0b1011_1111 , 0b1011_1111 , 0b1011_1111 ];
        // 3.3.10 6-byte sequence with last byte missing (U-7FFFFFFF): " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidSequence; 0b1111_1101, 0b1011_1111 , 0b1011_1111 , 0b1011_1111 , 0b1011_1111 ];
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
        match_incomplete![ chiter; 0b1100_0000];
        // 3 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1110_0000, 0b1000_0000];
        // 4 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1111_0000, 0b1000_0000, 0b1000_0000];
        // 5 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1111_1000, 0b1000_0000, 0b1000_0000, 0b1000_0000];
        // 6 byte sequence with a missing trailing byte
        match_incomplete![ chiter;
            0b1111_1100,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000,
            0b1000_0000
        ];
        // 2 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1100_1111];
        // 3 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1110_0111, 0b1011_1111];
        // 4 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1111_0111, 0b1011_1111, 0b1011_1111];
        // 5 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1111_1011, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // 6 byte sequence with a missing trailing byte
        match_incomplete![ chiter;
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
        match_err_and_sequence!(InvalidChar; 0xc0, 0xaf);
        // 4.1.2 U+002F = e0 80 af
        match_err_and_sequence!(InvalidChar; 0xe0, 0x80, 0xaf);
        // 4.1.3 U+002F = f0 80 80 af
        match_err_and_sequence!(InvalidChar; 0xf0, 0x80, 0x80, 0xaf);
        // 4.1.4 U+002F = f8 80 80 80 af
        match_err_and_sequence!(LongSequence; 0xf8, 0x80, 0x80, 0x80, 0xaf);
        // 4.1.5 U+002F = fc 80 80 80 80 af
        match_err_and_sequence!(LongSequence; 0xfc, 0x80, 0x80, 0x80, 0x80, 0xaf);
    }
    #[test]
    fn _4_2_maximum_overlong_sequences() {
        // Below you see the highest Unicode value that is still resulting in an
        // overlong sequence if represented with the given number of bytes. This
        // is a boundary test for safe UTF-8 decoders. All five characters should
        // be rejected like malformed UTF-8 sequences.

        // 4.2.1  U-0000007F = c1 bf
        match_err_and_sequence!(InvalidChar; 0xc1, 0xbf);
        // 4.2.2  U-000007FF = e0 9f bf
        match_err_and_sequence!(InvalidChar; 0xe0, 0x9f, 0xbf);
        // 4.2.3  U-0000FFFF = f0 8f bf bf
        match_err_and_sequence!(InvalidChar; 0xf0, 0x8f, 0xbf, 0xbf);
        // 4.2.4  U-001FFFFF = f8 87 bf bf bf
        match_err_and_sequence!(LongSequence; 0xf8, 0x87, 0xbf, 0xbf, 0xbf);
        // 4.2.5  U-03FFFFFF = fc 83 bf bf bf bf
        match_err_and_sequence!(LongSequence; 0xfc, 0x83, 0xbf, 0xbf, 0xbf, 0xbf);
    }

    #[test]
    fn _4_3_overlong_representation_of_the_nul_character() {
        // The following five sequences should also be rejected like malformed
        // UTF-8 sequences and should not be treated like the ASCII NUL
        // character.

        // 4.3.1  U+0000 = c0 80
        match_err_and_sequence!(InvalidChar; 0xc0, 0x80);
        // 4.3.2  U+0000 = e0 80 80
        match_err_and_sequence!(InvalidChar; 0xe0, 0x80, 0x80);
        // 4.3.3  U+0000 = f0 80 80 80
        match_err_and_sequence!(InvalidChar; 0xf0, 0x80, 0x80, 0x80);
        // 4.3.4  U+0000 = f8 80 80 80 80
        match_err_and_sequence!(LongSequence; 0xf8, 0x80, 0x80, 0x80, 0x80);
        // 4.3.5  U+0000 = fc 80 80 80 80 80
        match_err_and_sequence!(LongSequence; 0xfc, 0x80, 0x80, 0x80, 0x80, 0x80);
    }

    #[test]
    fn _5_illegal_code_positions() {
        // The following UTF-8 sequences should be rejected like malformed
        // sequences, because they never represent valid ISO 10646 characters and
        // a UTF-8 decoder that accepts them might introduce security problems
        //comparable to overlong UTF-8 sequences.

        // 5.1 Single UTF-16 surrogates
        // 5.1.1  U+D800 = ed a0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xa0, 0x80);
        // 5.1.2  U+DB7F = ed ad bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xad, 0xbf);
        // 5.1.3  U+DB80 = ed ae 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xae, 0x80);
        // 5.1.4  U+DBFF = ed af bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xaf, 0xbf);
        // 5.1.5  U+DC00 = ed b0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xb0, 0x80);
        // 5.1.6  U+DF80 = ed be 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xbe, 0x80);
        // 5.1.7  U+DFFF = ed bf bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xbf, 0xbf);

        // 5.2 Paired UTF-16 surrogates
        // Leading, also called high, surrogates are from D800 to DBFF, and trailing, or low, surrogates are from DC00 to DFFF.
        //
        //5.2.1  U+D800 U+DC00 = ed a0 80 ed b0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xa0, 0x80);
        match_err_and_sequence!(InvalidChar; 0xed, 0xb0, 0x80);
        //5.2.2  U+D800 U+DFFF = ed a0 80 ed bf bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xa0, 0x80);
        match_err_and_sequence!(InvalidChar; 0xed, 0xbf, 0xbf);
        //5.2.3  U+DB7F U+DC00 = ed ad bf ed b0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xad, 0xbf);
        match_err_and_sequence!(InvalidChar; 0xed, 0xb0, 0x80);
        //5.2.4  U+DB7F U+DFFF = ed ad bf ed bf bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xad, 0xbf);
        match_err_and_sequence!(InvalidChar; 0xed, 0xbf, 0xbf);
        //5.2.5  U+DB80 U+DC00 = ed ae 80 ed b0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xae, 0x80);
        match_err_and_sequence!(InvalidChar; 0xed, 0xb0, 0x80);
        //5.2.6  U+DB80 U+DFFF = ed ae 80 ed bf bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xae, 0x80);
        match_err_and_sequence!(InvalidChar; 0xed, 0xbf, 0xbf);
        //5.2.7  U+DBFF U+DC00 = ed af bf ed b0 80
        match_err_and_sequence!(InvalidChar; 0xed, 0xaf, 0xbf);
        match_err_and_sequence!(InvalidChar; 0xed, 0xb0, 0x80);
        //5.2.8  U+DBFF U+DFFF = ed af bf ed bf bf
        match_err_and_sequence!(InvalidChar; 0xed, 0xaf, 0xbf);
        match_err_and_sequence!(InvalidChar; 0xed, 0xbf, 0xbf);

        // 5.3 Other illegal code positions
        //5.3.1  U+FFFE = ef bf be
        match_err_and_sequence!(InvalidChar; 0xef, 0xbf, 0xbe);
        //5.3.2  U+FFFF = ef bf bf
        match_err_and_sequence!(InvalidChar; 0xef, 0xbf, 0xbf);
    }

    #[test]
    fn read_from_cursor() {
        let stream = Cursor::new("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ");
        //let stream = File::open("log.txt").unwrap();
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);

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
        const FILENAME: &str = "test.txt";
        let mut file = File::create(FILENAME).unwrap();
        file.write_all("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ".as_bytes())
            .unwrap();
        file.flush().unwrap();
        drop(file);

        let stream = File::open(FILENAME).unwrap();
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);

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

        std::fs::remove_file(FILENAME).unwrap();
    }

    #[test]
    fn _read_file_with_errors() {
        const FILENAME: &str = "test.txt";
        let mut file = File::create(FILENAME).unwrap();
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
        drop(file);

        let stream = File::open(FILENAME).unwrap();
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        macro_rules! match_kosme {
            ($iter:ident) => {
                assert_eq!('κ', chiter.next().unwrap().unwrap());
                assert_eq!('ό', chiter.next().unwrap().unwrap());
                assert_eq!('σ', chiter.next().unwrap().unwrap());
                assert_eq!('μ', chiter.next().unwrap().unwrap());
                assert_eq!('ε', chiter.next().unwrap().unwrap());
            };
        }

        // "κόσμε"
        match_kosme!(chiter);
        // 4 byte sequence with a missing trailing byte
        match_incomplete![ chiter; 0b1111_0000, 0b1000_0000, 0b1000_0000];
        // "κόσμε"
        match_kosme!(chiter);
        // Unexpected sequence bytes
        match_err_and_sequence!(chiter; InvalidSequence; 0x80);
        // Unexpected sequence bytes
        match_err_and_sequence!(chiter; InvalidSequence; 0xbf);
        // "κόσμε"
        match_kosme!(iter);
        // Over long ASCII
        match_err_and_sequence!(chiter; InvalidChar; 0xf0, 0x80, 0x80, 0xaf);
        // UTF-16 Surrogate
        match_err_and_sequence!(chiter; InvalidChar; 0xed, 0xa0, 0x80);
        // "κόσμε"
        match_kosme!(chiter);

        assert!(chiter.next().is_none());
    }

    #[test]
    fn _unget_test() {
        let input: Vec<u8> = vec![
            0xce, 0xba, 0xe1, 0xbd, 0xb9, 0xcf, 0x83, 0xce, 0xbc, 0xce, 0xb5,
        ];
        let stream = Cursor::new(input);
        let iter = stream.bytes();
        let mut chiter = Utf8Iterator::new(iter);
        assert_eq!('κ', chiter.next().unwrap().unwrap());
        chiter.unget('ε');
        assert_eq!('ε', chiter.next().unwrap().unwrap());
        assert_eq!('ό', chiter.next().unwrap().unwrap());
        assert_eq!('σ', chiter.next().unwrap().unwrap());
        assert_eq!('μ', chiter.next().unwrap().unwrap());
        assert_eq!('ε', chiter.next().unwrap().unwrap());
        chiter.unget('κ');
        assert_eq!('κ', chiter.next().unwrap().unwrap());
        assert!(chiter.next().is_none());
    }
}
