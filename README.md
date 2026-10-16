# Utf8Iterator

A `Utf8Iterator` wraps a UTF-8 decoder around an iterator for `Read`.

Essentially, the `Utf8Iterator` converts a `u8` iterator into a `char` iterator. The underlying iterator can be an
iterator for a `BufRead` or a `Cursor`, for example.
It is meant to iterate around an I/O. Therefore, it is expecting the inner iterator to be of type `Iterator<Item = Result<u8, std::io::Error>>`.

The `next()` method will return an `Option`, where `None` indicates the end of the sequence and a value
will be of type `Result` containing a `char` or an error, which will describe an UTF-8 decoding error or an IO error from the underlying iterator.
Decoding errors will contain the malformed sequences.

### Disclaimer

I wrote this crate as part of a learning project, not because there weren't alternatives or to write something better.
There are already Rust crates to decode UTF-8. This crate may only make some sense if your hardware is so low in memory
that would pay off to decode directly from the IO buffer (something unlikely to happen these days, right?) or you really need to
decode a single character at a time.

## Examples

### Basic usage:

```rust
use rustf8::*;
use std::io::prelude::*;
use std::io::Cursor;

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
```

### Error handling:

An excerpt of a small tokenizer. The complete example, which is tested, is in the documentation of `Utf8IteratorError`.

```rust,ignore
fn next_token(
    chiter: &mut Utf8Iterator<Bytes<Cursor<&str>>>,
    state: &mut (State, Token),
) -> Option<Token> {
    loop {
        let r = chiter.next();
        match r {
            Some(item) => match item {
                Ok(ch) => {
                    *state = state_machine(chiter, ch, state);
                    if let State::FinishedToken = state.0 {
                        return Some(state.1.clone());
                    }
                }
                Err(e) => match e {
                    InvalidSequenceError(bytes) => {
                        panic!("Detected an invalid UTF-8 sequence! {:?}", bytes)
                    }
                    LongSequenceError(bytes) => {
                        panic!("UTF-8 sequence with more than 4 bytes! {:?}", bytes)
                    }
                    InvalidCharError(bytes) => panic!(
                        "UTF-8 sequence resulted in an invalid character! {:?}",
                        bytes
                    ),
                    IoError(ioe, bytes) => panic!(
                        "I/O error {:?} while decoding the sequence {:?} !",
                        ioe, bytes
                    ),
                },
            },
            None => {
                // At the end of the input, return the token still being built, if any.
                return match state.0 {
                    State::DecodingIdentifier | State::DecodingInteger => {
                        state.0 = State::Finalized;
                        Some(state.1.clone())
                    }
                    _ => None,
                };
            }
        }
    }
}
```

## Errors

The `Utf8Iterator` will identify UTF-8 decoding errors returning the enum `Utf8IteratorError`.
The error will also contain a `Box<[u8]>` with the malformed sequence.
Subsequent calls to `next()` are allowed and will decode valid characters from the point beyond the malformed sequence.

The IO error `std::io::ErrorKind::Interrupted` coming from the underlying iterator will be transparently _consumed_ by the `next()` method.
Therefore there will be no need to treat such error.

Other IO errors are returned as `IoError`, together with the bytes already read of the character being decoded. The
`std::io::Error` is also available through `std::error::Error::source()`. Those bytes are kept: the next call to `next()`
carries on decoding the same character, so a temporary error such as `WouldBlock` or `TimedOut` does not lose any data.

## Panics

Panics if trying to use `unget()` twice before calling `next()`.
Use `try_unget()` to get an error instead.

## Safety

This crate does not use `unsafe {}` and enforces it with `#![forbid(unsafe_code)]`.

Once decoded, the values are converted using `char::from_u32()`, which rejects UTF-16 surrogates and values above U+10FFFF.
Overlong sequences, which encode a value with more bytes than needed, are rejected too.

Noncharacters such as U+FFFE and U+FFFF are valid Unicode scalar values (Unicode Corrigendum #9) and are decoded
like any other character. Applications that give them a special meaning must check for them.

## Minimum supported Rust version

Rust 1.85 or newer (edition 2024).
