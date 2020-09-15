# Utf8Iterator

 A `Utf8Iterator` wraps a UTF-8 decoder around an iterator for `Read`.

 Essentially, the `Utf8Iterator` converts a `u8` iterator into a `char` iterator. The underling interator can be an
 interator for a `BufRead` or a `Cursor`, for example.
 It is meant to iterate around an I/O. Therefore, it is expecting the inner iterator to be of type `Iterator<Item = Result<u8, std::io::Error>>`.

 The `next()` method will return an `Option`, where `None` indicates the end of the sequence and a value
 will be of type `Result` containing a `char` or an error, which will describe an UTF-8 decoding error or an IO error from the underling iterator.
 Decoding errors will contain the malformed sequences.

 ## Examples
 
 ### Basic usage:
 ```
    use rustf8::*;
    use std::io::prelude::*;
    use std::io::Cursor;
    fn some_correct_utf_8_text() {
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
 ```
### Error handling:
 ```
   fn next_token (chiter: &mut Utf8Iterator<Bytes<Cursor<&str>>>, state: &mut (State, Token)) 
     -> Option<Token> {
       loop {
           let r = chiter.next();
           match r {
               Some(item) => match item {
                   Ok(ch) => {
                       *state = state_machine(chiter, ch, &state);
                       if let State::FinishedToken = state.0 {
                           return Some(state.1.clone());
                       }
                   }
                   Err(e) => match e {
                       InvalidSequence(bytes) => {
                           panic!("Detected an invalid UTF-8 sequence! {:?}", bytes)
                       }
                       LongSequence(bytes) => {
                           panic!("UTF-8 sequence with more tha 4 bytes! {:?}", bytes)
                       }
                       InvalidChar(bytes) => panic!(
                           "UTF-8 sequence resulted in an invalid character! {:?}",
                           bytes
                       ),
                       IoError(ioe, bytes) => panic!(
                           "I/O error {:?} while decoding de sequence {:?} !",
                           ioe, bytes
                       ),
                   },
               },
               None => {
                   if let State::Finalized = state.0 {
                       return None;
                   } else {
                       state.0 = State::Finalized;
                       return Some(state.1.clone());
                   }
               }
           }
       }
   };

 ```

 ## Errors

 The `Utf8Iteraror` will identify UTF-8 decoding errors returning the enum `Utf8IteratorError`.
 The error will also contain a `Box<u8>` containing the malformed sequence.
 Subsequent calls to `next()` are allowed and will decode valid characters from the point beyond the malformed sequence.

 The IO error `std::io::ErrorKind::Interruped` coming from the underling iterator will be transparently _consumed_ by the `next()` method.
 Therefore there will be no need to treat such error.

 ## Panics

 Panics if trying to use `unget()` twice before calling `next()`.

 ## Safety

 This crate does not use `usafe {}`.

 Once decoded, the values are converted using `char::from_u32()`, which should prevent invalid characters anyway.
