#![cfg_attr(not(with_main), no_std)]
#[cfg(not(with_main))] extern crate std;

use std::io::{Cursor, Read, Write};

pub fn f(x: u8) -> u8 {
    let mut buf = [0; 10];

    let mut c = Cursor::new(&mut buf as &mut [_]);
    c.write(&[x]).unwrap();
    c.write(&[x]).unwrap();

    assert!(buf[0] == x);
    assert!(buf[1] == x);
    for &y in &buf[2..] {
        assert!(y == 0);
    }

    0
}

pub static ARG: u8 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u8 { f(ARG) }
