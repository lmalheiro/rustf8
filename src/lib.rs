//
// https://www.w3.org/2001/06/utf-8-wrong/UTF-8-test.html
// U+FFFD -> 11101111 10111111 10111101 -> vec![ 0, 0b_11101111_u8, 0b_10111111_u8, 0b_10111101_u8 ]
//

use std::char::REPLACEMENT_CHARACTER;

pub struct Utf8Iterator<R>
where
    R: Iterator<Item = u8>,
{
    inner: R,
    finished: bool,
}

impl<R> Utf8Iterator<R>
where
    R: Iterator<Item = u8>,
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
    R: Iterator<Item = u8>,
{
    type Item = char;
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            None
        } else if let Some(next_byte) = self.inner.next() {
            let (nbytes, mut builder) = if next_byte & 0b_1000_0000_u8 == 0 {
                (1, u32::from(next_byte))
            } else if next_byte & 0b_1110_0000_u8 == 0b_1100_0000_u8 {
                (2, u32::from(next_byte & 0b_0001_1111_u8))
            } else if next_byte & 0b_1111_0000_u8 == 0b_1110_0000_u8 {
                (3, u32::from(next_byte & 0b_0000_1111_u8))
            } else if next_byte & 0b_1111_1000_u8 == 0b_1111_0000_u8 {
                (4, u32::from(next_byte & 0b_0000_0111_u8))
            } else if next_byte & 0b_1111_1100_u8 == 0b_1111_1000_u8 {
                (5, u32::from(next_byte & 0b_0000_0011_u8))
            } else if next_byte & 0b_1111_1110_u8 == 0b_1111_1100_u8 {
                (6, u32::from(next_byte & 0b_0000_0001_u8))
            } else {
                (-1, 0u32)
            };
            if (1..4).contains(&nbytes) {
                //let mut builder = u32::from(next_byte);
                let mut aux = builder;
                for _ in 1..nbytes {
                    if let Some(next_byte) = self.inner.next() {
                        if next_byte & 0b_1100_0000_u8 == 0b_1000_0000_u8 {
                            builder = (builder << 6) | u32::from(next_byte & 0b_0011_1111_u8);
                            aux = (aux << 6) | u32::from(next_byte & 0b_0011_1111_u8);
                        } else {
                            builder = u32::from(REPLACEMENT_CHARACTER);
                            break;
                        }
                    } else {
                        self.finished = true;
                        builder = u32::from(REPLACEMENT_CHARACTER);
                        break;
                    }
                }
                //println!("aux: {:08X}", aux);
                Some(std::char::from_u32(builder).unwrap_or(REPLACEMENT_CHARACTER))
            } else {
                Some(REPLACEMENT_CHARACTER)
            }
        } else {
            self.finished = true;
            None
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use std::io::prelude::*;
    use std::io::BufReader;
    use std::io::Cursor;
    use super::*;

    #[test]
    #[ignore]
    fn it_works() {
        let stream = Cursor::new("charaactersé®þüúäåáßðfghjœøµñbv©xæ");
        //let stream = File::open("log.txt").unwrap();
        let mut buffered = BufReader::new(stream);
        let mut text = String::new();
        buffered.read_line(&mut text).unwrap();
        assert_eq!("charaactersé®þüúäåáßðfghjœøµñbv©xæ", text.as_str());
    }

    #[test]
    fn it_works_1() {
        // let text = "charaactersé®þüúäåáßðfghjœøµñbv©xæ";
        let text = "NVIDIA 网站使用é®þüúäåáßðfghjœøµñbv©xæ";
        let mut utf8iter = Utf8Iterator::new(text.bytes());
        while let Some(ch) = utf8iter.next() {
            eprintln!("Byte value: {}", ch);
        }
        // let mut u8iter = text.bytes();
        // while let Some(ch) = u8iter.next() {
        //     eprintln!("Byte value: {:08b}", ch);
        // }
        
    }

    #[test]
    #[ignore]
    fn it_works_2() {
        let stream = Cursor::new("charaactersé®þüúäåáßðfghjœøµñbv©xæ");
        //let stream = File::open("log.txt").unwrap();
        let buffered = BufReader::new(stream);
        let mut iter = buffered.bytes();
        loop {
            if let Some(item) = iter.next() {
                let b1 = item.unwrap();

                let v = if b1 > 0b_0000_0000_u8 && b1 < 0b_0111_1111_u8 {
                    vec![0, 0, 0, b1]
                } else if b1 > 0b_1100_0000_u8 && b1 < 0b_1101_1111_u8 {
                    let b2 = iter.next().unwrap().unwrap();
                    vec![0, 0, b1, b2]
                } else if b1 > 0b_1110_0000_u8 && b1 < 0b_1110_1111_u8 {
                    let b2 = iter.next().unwrap().unwrap();
                    let b3 = iter.next().unwrap().unwrap();
                    vec![0, b1, b2, b3]
                } else if b1 > 0b_1111_0000_u8 && b1 < 0b_1111_0111_u8 {
                    let b2 = iter.next().unwrap().unwrap();
                    let b3 = iter.next().unwrap().unwrap();
                    let b4 = iter.next().unwrap().unwrap();
                    vec![b1, b2, b3, b4]
                } else {
                    vec![0, 0b_11101111_u8, 0b_10111111_u8, 0b_10111101_u8]
                };
                eprintln!("Byte value: {:?} {}", v, std::str::from_utf8(&v).unwrap());
            } else {
                break;
            }
        }
        // let x: char = 'é';
        // let mut chars = "é".chars();
    }
}
