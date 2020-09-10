//
// https://www.w3.org/2001/06/utf-8-wrong/UTF-8-test.html
// U+FFFD -> 11101111 10111111 10111101 -> vec![ 0, 0b_11101111_u8, 0b_10111111_u8, 0b_10111101_u8 ]
//

use std::char::REPLACEMENT_CHARACTER;

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

impl<R> Iterator for Utf8Iterator<R>
where
    R: Iterator<Item = Result<u8, std::io::Error>>,
{
    type Item = Result<char, std::io::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        fn size_and_first_bits(first_byte: u8) -> (u8, u32) {
            let test = |bits: u8| first_byte & bits == (bits << 1);
            let rtn = |nbits: u8, bits: u8| (nbits, u32::from(first_byte & bits));

            if first_byte & 0b_1000_0000_u8 == 0 {
                (1, u32::from(first_byte))
            } else if test(0b_1110_0000_u8) {
                rtn(2, 0b_0001_1111_u8)
            } else if test(0b_1111_0000_u8) {
                rtn(3, 0b_0000_1111_u8)
            } else if test(0b_1111_1000_u8) {
                rtn(4, 0b_0000_0111_u8)
            } else if test(0b_1111_1100_u8) {
                rtn(5, 0b_0000_0011_u8)
            } else if test(0b_1111_1110_u8) {
                rtn(6, 0b_0000_0001_u8)
            } else {
                (0, 0u32)
            }
        }

        if self.finished {
            None
        } else if let Some(has_input) = self.inner.next() {
            match has_input {
                Err(e) => return Some(Err(e)),
                Ok(first_byte) => {
                    let (nbytes, mut builder) = size_and_first_bits(first_byte);
                    if nbytes >= 1 && nbytes <= 4 {
                        for _ in 1..nbytes {
                            if let Some(has_input) = self.inner.next() {
                                match has_input {
                                    Err(e) => return Some(Err(e)),
                                    Ok(next_byte) => {
                                        if next_byte & 0b_1100_0000_u8 == 0b_1000_0000_u8 {
                                            builder = (builder << 6) | u32::from(next_byte & 0b_0011_1111_u8);
                                        } else {
                                            return Some(Ok(REPLACEMENT_CHARACTER));
                                        }
                                    }
                                }
                            } else {
                                self.finished = true;
                                return Some(Ok(REPLACEMENT_CHARACTER));
                            }
                        }
                        Some(Ok(
                            std::char::from_u32(builder).unwrap_or(REPLACEMENT_CHARACTER)
                        ))
                    } else {
                        Some(Ok(REPLACEMENT_CHARACTER))
                    }
                }
            }
        } else {
            self.finished = true;
            None
        }
        //None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::prelude::*;
    use std::io::BufReader;
    use std::io::Cursor;

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
}
