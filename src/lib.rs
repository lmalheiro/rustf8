//
// U+FFFD -> 11101111 10111111 10111101 -> vec![ 0, 0b_11101111_u8, 0b_10111111_u8, 0b_10111101_u8 ] -> REPLACEMENT_CHARACTER
//

use std::char::from_u32;

pub struct Utf8Iterator<R>
where
    R: Iterator,
{
    inner: R,
    finished: bool,
}

impl<R> Utf8Iterator<R>
where
    R: Iterator,
{
    pub fn new(inner: R) -> Self {
        Utf8Iterator {
            inner,
            finished: false,
        }
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
        // identify the length of the UTF-8 sequece and extract the first bits
        fn length_and_first_bits(first_byte: u8) -> (u8, u32) {
            // Uses a mask to isolate the bits indicating the sequence length.
            // Extracts the first bits from the UTF-8 using the negated mask.
            macro_rules! mktest {
                ($nbits:literal, $mask:literal) => {
                    if first_byte & $mask == ($mask << 1) {
                        return ($nbits, u32::from(first_byte & !$mask));
                    }
                };
            }

            // 1 byte sequence
            if first_byte & 0b_1000_0000_u8 == 0 {
                return (1, u32::from(first_byte));
            }
            mktest!(2, 0b_1110_0000_u8); // 2 bytes sequence
            mktest!(3, 0b_1111_0000_u8); // 3 bytes sequence
            mktest!(4, 0b_1111_1000_u8); // 4 bytes sequence
            mktest!(5, 0b_1111_1100_u8); // 5 bytes sequence
            mktest!(6, 0b_1111_1110_u8); // 6 bytes sequence
            return (0, 0u32); // continuation byte or other unexpected char
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

        // If in the previous call we exited because the stream has ended, it means that we returned
        // the character, probably as an invalid sequence, and now we will indicate the stream ended.
        if self.finished {
            return None;
        } else if let Some(has_input) = self.inner.next() {
            match has_input {
                Err(e) => return err![IoError, e, Vec::<u8>::new()],
                Ok(first_byte) => {
                    let mut seq = Vec::<u8>::new();
                    seq.push(first_byte);
                    let (nbytes, mut builder) = length_and_first_bits(first_byte);
                    if nbytes >= 1 {
                        for _ in 1..nbytes {
                            if let Some(has_input) = self.inner.next() {
                                match has_input {
                                    Err(e) => return err![IoError, e, seq],
                                    Ok(next_byte) => {
                                        seq.push(next_byte);
                                        if next_byte & 0xC0u8 == 0x80u8 {
                                            builder =
                                                (builder << 6) | u32::from(next_byte & 0x3Fu8);
                                        } else {
                                            return err![InvalidSequence, seq];
                                        }
                                    }
                                }
                            } else {
                                self.finished = true;
                                return err![InvalidSequence, seq];
                            }
                        }
                        if nbytes < 5 {
                            if let Some(ch) = from_u32(builder) {
                                return Some(Ok(ch));
                            } else {
                                return err![InvalidChar, seq];
                            }
                        } else {
                            // 5 and 6 bytes unicode will overflow the builder variable.
                            // Also, they can't be stored in Rust characters (AFAIK).
                            return err![LongSequence, seq];
                        }
                    } else {
                        // It seems the first byte is a continuation or other unexpected value
                        return err![InvalidSequence, seq];
                    }
                }
            }
        } else {
            self.finished = true;
            return None;
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod tests {

    // http://unicode.scarfboy.com/
    //
    // https://www.w3.org/2001/06/utf-8-wrong/UTF-8-test.html
    // Original by Markus Kuhn, adapted for HTML by Martin Dürst.
    //
    // UTF-8 decoder capability and stress test                                      |
    // ----------------------------------------                                      |
    //                                                                               |
    // Markus Kuhn <mkuhn@acm.org> - 2000-09-02                                      |
    //                                                                               |
    // This test text examines, how UTF-8 decoders handle various types of           |
    // corrupted or otherwise interesting UTF-8 sequences.                           |
    //                                                                               |
    // According to ISO 10646-1, sections R.7 and 2.3c, a device receiving           |
    // UTF-8 shall interpret a "malformed sequence in the same way that it           |
    // interprets a character that is outside the adopted subset". This means        |
    // usually that the malformed UTF-8 sequence is replaced by a replacement        |
    // character (U+FFFD), which looks a bit like an inverted question mark,         |
    // or a similar symbol. It might be a good idea to visually distinguish a        |
    // malformed UTF-8 sequence from a correctly encoded Unicode character           |
    // that is just not available in the current font but otherwise fully            |
    // legal. For both cases, a clearly recognisable symbol should be used.          |
    // Just ignoring malformed sequences or unavailable characters will make         |
    // debugging more difficult and can lead to user confusion.                      |
    //                                                                               |
    // Test sequences:                                                               |
    //                                                                               |
    // Check, whether a malformed UTF-8 sequence is (1) represented at all,          |
    // (2) represented by exactly one replacement character (or equivalent           |
    // signal), and (3) the following quotation mark after an illegal UTF-8          |
    // sequence is correctly displayed, i.e. proper resynchronization takes          |
    // place. This file says "THE END" in the last line, so if you don't see         |
    // that, your decoder crashed somehow before, which is also not nice.            |
    //                                                                               |
    // All lines in this file are exactly 79 characters long (plus the line          |
    // feed). In addition, all lines end with "|", except for the two test           |
    // lines 2.1.1 and 2.2.1, which contain non-printable ASCII controls             |
    // U+0000 and U+007F. If you display this file with a fixed-width font,          |
    // these "|" characters should all line up in column 79 (right margin).          |
    // This allows you to test quickly, whether your UTF-8 decoder finds the         |
    // correct number of characters in every line.                                   |
    //                                                                               |
    // Here come the tests:                                                          |
    //                                                                               |
    // 1  Some correct UTF-8 text                                                    |
    //                                                                               |
    // You should see the Greek word 'kosme':       "κόσμε"                          |
    //                                                                               |
    // 2  Boundary condition test cases                                              |
    //                                                                               |
    // You should see a correctly encoded character each time (which is not          |
    // necessarily an existing character).                                           |
    //                                                                               |
    // 2.1  First possible sequence of a certain length                              |
    //                                                                               |
    // 2.1.1  1 byte  (U-00000000):        ""
    // 2.1.2  2 bytes (U-00000080):        ""                                       |
    // 2.1.3  3 bytes (U-00000800):        "ࠀ"                                       |
    // 2.1.4  4 bytes (U-00010000):        "𐀀"                                       |
    // 2.1.5  5 bytes (U-00200000):        "�����"                                       |
    // 2.1.6  6 bytes (U-04000000):        "������"                                       |
    //                                                                               |
    // 2.2  Last possible sequence of a certain length                               |
    //                                                                               |
    // 2.2.1  1 byte  (U-0000007F):        ""
    // 2.2.2  2 bytes (U-000007FF):        "߿"                                       |
    // 2.2.3  3 bytes (U-0000FFFF):        "￿"                                       |
    // 2.2.4  4 bytes (U-001FFFFF):        "����"                                       |
    // 2.2.5  5 bytes (U-03FFFFFF):        "�����"                                       |
    // 2.2.6  6 bytes (U-7FFFFFFF):        "������"                                       |
    //                                                                               |
    // 2.3  Other boundary conditions                                                |
    //                                                                               |
    // 2.3.1  U-0000D7FF = ed 9f bf = "퟿"                                            |
    // 2.3.2  U-0000E000 = ee 80 80 = ""                                            |
    // 2.3.3  U-0000FFFD = ef bf bd = "�"                                            |
    // 2.3.4  U-0010FFFF = f4 8f bf bf = "􏿿"                                         |
    // 2.3.5  U-00110000 = f4 90 80 80 = "����"                                         |
    //                                                                               |
    // 3  Malformed sequences                                                        |
    //                                                                               |
    // 3.1  Unexpected continuation bytes                                            |
    //                                                                               |
    // Each unexpected continuation byte should be separately signalled as a         |
    // malformed sequence of its own.                                                |
    //                                                                               |
    // 3.1.1  First continuation byte 0x80: "�"                                      |
    // 3.1.2  Last  continuation byte 0xbf: "�"                                      |
    //                                                                               |
    // 3.1.3  2 continuation bytes: "��"                                             |
    // 3.1.4  3 continuation bytes: "���"                                            |
    // 3.1.5  4 continuation bytes: "����"                                           |
    // 3.1.6  5 continuation bytes: "�����"                                          |
    // 3.1.7  6 continuation bytes: "������"                                         |
    // 3.1.8  7 continuation bytes: "�������"                                        |
    //                                                                               |
    // 3.1.9  Sequence of all 64 possible continuation bytes (0x80-0xbf):            |
    //                                                                               |
    //    "����������������                                                          |
    //     ����������������                                                          |
    //     ����������������                                                          |
    //     ����������������"                                                         |
    //                                                                               |
    // 3.2  Lonely start characters                                                  |
    //                                                                               |
    // 3.2.1  All 32 first bytes of 2-byte sequences (0xc0-0xdf),                    |
    //        each followed by a space character:                                    |
    //                                                                               |
    //    "� � � � � � � � � � � � � � � �                                           |
    //     � � � � � � � � � � � � � � � � "                                         |
    //                                                                               |
    // 3.2.2  All 16 first bytes of 3-byte sequences (0xe0-0xef),                    |
    //        each followed by a space character:                                    |
    //                                                                               |
    //    "� � � � � � � � � � � � � � � � "                                         |
    //                                                                               |
    // 3.2.3  All 8 first bytes of 4-byte sequences (0xf0-0xf7),                     |
    //        each followed by a space character:                                    |
    //                                                                               |
    //    "� � � � � � � � "                                                         |
    //                                                                               |
    // 3.2.4  All 4 first bytes of 5-byte sequences (0xf8-0xfb),                     |
    //        each followed by a space character:                                    |
    //                                                                               |
    //    "� � � � "                                                                 |
    //                                                                               |
    // 3.2.5  All 2 first bytes of 6-byte sequences (0xfc-0xfd),                     |
    //        each followed by a space character:                                    |
    //                                                                               |
    //    "� � "                                                                     |
    //                                                                               |
    // 3.3  Sequences with last continuation byte missing                            |
    //                                                                               |
    // All bytes of an incomplete sequence should be signalled as a single           |
    // malformed sequence, i.e., you should see only a single replacement            |
    // characters in each of the next 10 tests. (Characters as in section 2)         |
    //                                                                               |
    // 3.3.1  2-byte sequence with last byte missing (U+0000):     "�"               |
    // 3.3.2  3-byte sequence with last byte missing (U+0000):     "��"               |
    // 3.3.3  4-byte sequence with last byte missing (U+0000):     "���"               |
    // 3.3.4  5-byte sequence with last byte missing (U+0000):     "����"               |
    // 3.3.5  6-byte sequence with last byte missing (U+0000):     "�����"               |
    // 3.3.6  2-byte sequence with last byte missing (U-000007FF): "�"               |
    // 3.3.7  3-byte sequence with last byte missing (U-0000FFFF): "�"               |
    // 3.3.8  4-byte sequence with last byte missing (U-001FFFFF): "���"               |
    // 3.3.9  5-byte sequence with last byte missing (U-03FFFFFF): "����"               |
    // 3.3.10 6-byte sequence with last byte missing (U-7FFFFFFF): "�����"               |
    //                                                                               |
    // 3.4  Concatenation of incomplete sequences                                    |
    //                                                                               |
    // All the 10 sequences of 3.3 concatenated, you should see 10 malformed         |
    // sequences being signalled:                                                    |
    //                                                                               |
    //    "�����������������������������"                                                               |
    //                                                                               |
    // 3.5  Impossible bytes                                                         |
    //                                                                               |
    // The following two bytes cannot appear in a correct UTF-8 string               |
    //                                                                               |
    // 3.5.1  fe = "�"                                                               |
    // 3.5.2  ff = "�"                                                               |
    // 3.5.3  fe fe ff ff = "����"                                                   |
    //                                                                               |
    // 4  Overlong sequences                                                         |
    //                                                                               |
    // The following sequences are not malformed according to the letter of          |
    // the Unicode 2.0 standard. However, they are longer then necessary and         |
    // a correct UTF-8 encoder is not allowed to produce them. A "safe UTF-8         |
    // decoder" should reject them just like malformed sequences for two             |
    // reasons: (1) It helps to debug applications if overlong sequences are         |
    // not treated as valid representations of characters, because this helps        |
    // to spot problems more quickly. (2) Overlong sequences provide                 |
    // alternative representations of characters, that could maliciously be          |
    // used to bypass filters that check only for ASCII characters. For              |
    // instance, a 2-byte encoded line feed (LF) would not be caught by a            |
    // line counter that counts only 0x0a bytes, but it would still be               |
    // processed as a line feed by an unsafe UTF-8 decoder later in the              |
    // pipeline. From a security point of view, ASCII compatibility of UTF-8         |
    // sequences means also, that ASCII characters are *only* allowed to be          |
    // represented by ASCII bytes in the range 0x00-0x7f. To ensure this             |
    // aspect of ASCII compatibility, use only "safe UTF-8 decoders" that            |
    // reject overlong UTF-8 sequences for which a shorter encoding exists.          |
    //                                                                               |
    // 4.1  Examples of an overlong ASCII character                                  |
    //                                                                               |
    // With a safe UTF-8 decoder, all of the following five overlong                 |
    // representations of the ASCII character slash ("/") should be rejected         |
    // like a malformed UTF-8 sequence, for instance by substituting it with         |
    // a replacement character. If you see a slash below, you do not have a          |
    // safe UTF-8 decoder!                                                           |
    //                                                                               |
    // 4.1.1 U+002F = c0 af             = "��"                                        |
    // 4.1.2 U+002F = e0 80 af          = "���"                                        |
    // 4.1.3 U+002F = f0 80 80 af       = "����"                                        |
    // 4.1.4 U+002F = f8 80 80 80 af    = "�����"                                        |
    // 4.1.5 U+002F = fc 80 80 80 80 af = "������"                                        |
    //                                                                               |
    // 4.2  Maximum overlong sequences                                               |
    //                                                                               |
    // Below you see the highest Unicode value that is still resulting in an         |
    // overlong sequence if represented with the given number of bytes. This         |
    // is a boundary test for safe UTF-8 decoders. All five characters should        |
    // be rejected like malformed UTF-8 sequences.                                   |
    //                                                                               |
    // 4.2.1  U-0000007F = c1 bf             = "��"                                   |
    // 4.2.2  U-000007FF = e0 9f bf          = "���"                                   |
    // 4.2.3  U-0000FFFF = f0 8f bf bf       = "����"                                   |
    // 4.2.4  U-001FFFFF = f8 87 bf bf bf    = "�����"                                   |
    // 4.2.5  U-03FFFFFF = fc 83 bf bf bf bf = "������"                                   |
    //                                                                               |
    // 4.3  Overlong representation of the NUL character                             |
    //                                                                               |
    // The following five sequences should also be rejected like malformed           |
    // UTF-8 sequences and should not be treated like the ASCII NUL                  |
    // character.                                                                    |
    //                                                                               |
    // 4.3.1  U+0000 = c0 80             = "��"                                       |
    // 4.3.2  U+0000 = e0 80 80          = "���"                                       |
    // 4.3.3  U+0000 = f0 80 80 80       = "����"                                       |
    // 4.3.4  U+0000 = f8 80 80 80 80    = "�����"                                       |
    // 4.3.5  U+0000 = fc 80 80 80 80 80 = "������"                                       |
    //                                                                               |
    // 5  Illegal code positions                                                     |
    //                                                                               |
    // The following UTF-8 sequences should be rejected like malformed               |
    // sequences, because they never represent valid ISO 10646 characters and        |
    // a UTF-8 decoder that accepts them might introduce security problems           |
    // comparable to overlong UTF-8 sequences.                                       |
    //                                                                               |
    // 5.1 Single UTF-16 surrogates                                                  |
    //                                                                               |
    // 5.1.1  U+D800 = ed a0 80 = "���"                                                |
    // 5.1.2  U+DB7F = ed ad bf = "���"                                                |
    // 5.1.3  U+DB80 = ed ae 80 = "���"                                                |
    // 5.1.4  U+DBFF = ed af bf = "���"                                                |
    // 5.1.5  U+DC00 = ed b0 80 = "���"                                                |
    // 5.1.6  U+DF80 = ed be 80 = "���"                                                |
    // 5.1.7  U+DFFF = ed bf bf = "���"                                                |
    //                                                                               |
    // 5.2 Paired UTF-16 surrogates                                                  |
    //                                                                               |
    // 5.2.1  U+D800 U+DC00 = ed a0 80 ed b0 80 = "������"                               |
    // 5.2.2  U+D800 U+DFFF = ed a0 80 ed bf bf = "������"                               |
    // 5.2.3  U+DB7F U+DC00 = ed ad bf ed b0 80 = "������"                               |
    // 5.2.4  U+DB7F U+DFFF = ed ad bf ed bf bf = "������"                               |
    // 5.2.5  U+DB80 U+DC00 = ed ae 80 ed b0 80 = "������"                               |
    // 5.2.6  U+DB80 U+DFFF = ed ae 80 ed bf bf = "������"                               |
    // 5.2.7  U+DBFF U+DC00 = ed af bf ed b0 80 = "������"                               |
    // 5.2.8  U+DBFF U+DFFF = ed af bf ed bf bf = "������"                               |
    //                                                                               |
    // 5.3 Other illegal code positions                                              |
    //                                                                               |
    // 5.3.1  U+FFFE = ef bf be = "￾"                                                |
    // 5.3.2  U+FFFF = ef bf bf = "￿"                                                |
    //                                                                               |
    // THE END                                                                       |

    use super::*;
    use std::char::REPLACEMENT_CHARACTER;
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
        ($ch:ident; $($x:expr),*) => {
            let input: Vec<u8> = vec![ $($x),* ];
            let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
            let value = chiter.next().unwrap();
            if let Err($ch(bytes)) = value {
                assert_eq!(vec![ $($x),* ].into_boxed_slice(), bytes)
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

        // let input: Vec<u8> = vec![0b11111000, 0b10000000, 0b10000000, 0b10000000, 0b10000000];
        // let mut chiter = Utf8Iterator::new(Cursor::new(input).bytes());
        // let value = chiter.next().unwrap();
        // if let Err(LongSequence(bytes)) = value {
        //     assert_eq!(
        //         vec![0b11111000, 0b10000000, 0b10000000, 0b10000000, 0b10000000].into_boxed_slice(),
        //         bytes
        //     )
        // } else {
        //     panic!(value);
        // }

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
        match_char_and_sequence!['\u{FFFF}'; 0b_1110_1111, 0b_1011_1111, 0b_1011_1111];
        // 2.2.4  4 bytes (U-001FFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![InvalidChar; 0b_1111_0111, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // \u{10FFFF}
        match_char_and_sequence!['\u{10FFFF}'; 0b_1111_0100, 0b1000_1111, 0b1011_1111, 0b1011_1111];
        // 2.2.5  5 bytes (U-03FFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
        match_err_and_sequence![LongSequence; 0b_1111_1011, 0b1011_1111, 0b1011_1111, 0b1011_1111, 0b1011_1111];
        // 2.2.6  6 bytes (U-7FFFFFFF):        " 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd, 0xef, 0xbf, 0xbd,"
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
        match_char_and_sequence!['\u{80}'; 0b110_0_0010, 0b10_00_0000 ]; // correctly encoded \u{80}
        assert_eq!('\u{80}', from_u32(0x80).unwrap()); // from_u32 accepts 0x80 as valid and interprets it as \u{80}. Should it?
    }

    #[test]
    fn it_works_1() {
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
    fn it_works_2() {
        let mut file = File::create("test.txt").unwrap();
        file.write_all("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ".as_bytes())
            .unwrap();
        file.flush().unwrap();
        drop(file);

        let stream = File::open("test.txt").unwrap();
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
    #[ignore]
    fn it_fails_1() {
        let mut file = File::create("fails_1.txt").unwrap();
        let mut a = Vec::from("来提供和改进网站体验ersé®þüúäåáßðfghjœøµñbv©xæ".as_bytes());
        let mut b = vec![0xC0u8, 0x00u8];
        let mut c = vec![];
        c.append(&mut b);
        c.append(&mut a);
        file.write_all(c.as_slice()).unwrap();
        file.flush().unwrap();
        drop(file);

        let stream = File::open("fails_1.txt").unwrap();
        let buffered = BufReader::new(stream);
        let iter = buffered.bytes();
        let mut chiter = Utf8Iterator::new(iter);

        assert_eq!(REPLACEMENT_CHARACTER, chiter.next().unwrap().unwrap());
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
}
