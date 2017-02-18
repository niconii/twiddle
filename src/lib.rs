// Copyright 2017 Nicolette Verlinden
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A library for various bit-twiddling utility functions.
//!
//! NOTE: Most of the functions in this library take ranges of
//! the form `7..4`. These are inclusive ranges, not exclusive,
//! signifying the bits 7 through 4 *including* 4.
//!
//! # Example
//!
//! ```
//! extern crate twiddle;
//!
//! use twiddle::Twiddle;
//!
//! struct UnpackedF32 {
//!     negative: bool,
//!     exponent: i16,
//!     fraction: u32,
//! }
//!
//! impl From<f32> for UnpackedF32 {
//!     fn from(f: f32) -> UnpackedF32 {
//!         let b = unsafe { std::mem::transmute::<f32, u32>(f) };
//!         UnpackedF32 {
//!             negative: b.bit(31),
//!             exponent: (b.bits(30..23) as i16) - 127,
//!             fraction: b.bits(22..0)
//!         }
//!     }
//! }
//!
//! fn main() {
//!     for f in (-5..6) {
//!         let u = UnpackedF32::from(f as f32);
//!         println!("{:+} = {}1.{:023b} * 2^{}",
//!             f,
//!             match u.negative { false => "+", true => "-" },
//!             u.fraction,
//!             u.exponent
//!         );
//!     }
//! }
//! ```

#![no_std]
#![cfg_attr(feature="inclusive_range", feature(inclusive_range, inclusive_range_syntax))]

use core::cmp::PartialEq;
use core::iter::Iterator;
use core::num::Wrapping;
use core::ops::{Range, Shl, Shr, Sub, Not, BitAnd, BitOr};
#[cfg(feature = "inclusive_range")]
use core::ops::RangeInclusive;

#[derive(Clone, Copy, Debug)]
pub struct BitRange {
    start: usize,
    end: usize,
}

impl From<Range<usize>> for BitRange {
    fn from(range: Range<usize>) -> Self {
        BitRange {
            start: range.start,
            end: range.end,
        }
    }
}

#[cfg(feature = "inclusive_range")]
impl From<RangeInclusive<usize>> for BitRange {
    fn from(range: RangeInclusive<usize>) -> Self {
        let (start, end) = match range {
            RangeInclusive::Empty { at } => (at, at),
            RangeInclusive::NonEmpty { start, end } => (start, end),
        };
        BitRange {
            start: start,
            end: end,
        }
    }
}

/// A trait for bit-twiddling utility functions.
pub trait Twiddle {
    /// Creates a bitmask from a range.
    ///
    /// # Example
    ///
    /// ```
    /// # use twiddle::Twiddle;
    /// let mask = u32::mask(9..0);
    /// assert_eq!(mask, 0x3ff);
    /// ```
    fn mask<R: Into<BitRange>>(range: R) -> Self;

    /// Returns a given bit as a boolean.
    ///
    /// # Example
    ///
    /// ```
    /// # use twiddle::Twiddle;
    /// let byte: u8 = 0b0100_0000;
    /// if byte.bit(6) {
    ///     println!("Bit 6 is set!")
    /// }
    /// ```
    fn bit(self, bit: usize) -> bool;

    /// Returns a set of bits.
    ///
    /// # Example
    ///
    /// ```
    /// # use twiddle::Twiddle;
    /// let word: u16 = 0b0011_0101_1000_0000;
    /// assert_eq!(word.bits(12..8), 0b10101);
    /// ```
    fn bits<R: Into<BitRange>>(self, R) -> Self;

    /// Replaces a set of bits with another.
    ///
    /// # Example
    ///
    /// ```
    /// # use twiddle::Twiddle;
    /// let word: u16 = 0b0000_1010_1010_0000;
    /// assert_eq!(word.replace(7..4, 0b0001), 0b0000_1010_0001_0000);
    /// ```
    ///
    /// # Notes
    ///
    /// - If too many bits are given, the highest bits will be truncated.
    fn replace<R: Into<BitRange>>(self, range: R, bits: Self) -> Self;

    /// Splits a number into an iterator over sets of bits.
    ///
    /// # Example
    ///
    /// ```
    /// # use twiddle::Twiddle;
    /// let byte: u8 = 0b1100_0111;
    /// let vec: Vec<u8> = byte.split(vec![2, 3, 5]).collect();
    ///
    /// assert_eq!(vec, vec![0b11, 0b000, 0b11100]);
    /// ```
    ///
    /// # Notes
    ///
    /// - The last set of bits will be zero-padded on the right end if there
    ///   are not enough bits remaining in the number.
    ///
    /// - Once there are no more bits remaining, the iterator will return
    ///   None even if there are more lengths remaining.
    fn split<I>(self, lengths: I) -> Split<Self, <I as IntoIterator>::IntoIter>
        where I: IntoIterator<Item = usize>,
              Self: Sized;
}

impl<T> Twiddle for T
    where T: Int,
          Wrapping<T>: Sub<Output = Wrapping<T>>
{
    fn mask<R: Into<BitRange>>(range: R) -> T {
        let range = range.into();
        debug_assert!(range.start < T::bit_width());
        debug_assert!(range.end <= range.start);

        // cshl is << but with overlong shifts resulting in 0
        let top = Wrapping(T::one().cshl(1 + range.start - range.end));
        let one = Wrapping(T::one());

        (top - one).0 << range.end
    }

    fn bit(self, bit: usize) -> bool {
        ((self >> bit) & T::one()) != T::zero()
    }

    fn bits<R: Into<BitRange>>(self, range: R) -> T {
        let range = range.into();
        (self & T::mask(range)) >> range.end
    }

    fn replace<R: Into<BitRange>>(self, range: R, bits: T) -> T {
        let range = range.into();
        let mask = T::mask(range);
        (self & !mask) | ((bits << range.end) & mask)
    }

    fn split<I>(self, lengths: I) -> Split<T, <I as IntoIterator>::IntoIter>
        where I: IntoIterator<Item = usize>
    {
        Split {
            number: self,
            lengths: lengths.into_iter(),
            bits_left: T::bit_width() as isize,
        }
    }
}

/// An iterator over sets of bits. See `Twiddle::split()` for more information.
pub struct Split<T, I> {
    number: T,
    lengths: I,
    bits_left: isize,
}

impl<T, I> Iterator for Split<T, I>
    where T: Twiddle + Int,
          I: Iterator<Item = usize>
{
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.bits_left <= 0 {
            return None;
        }

        match self.lengths.next() {
            None => None,
            Some(0) => Some(T::zero()),
            Some(n) => {
                let start = T::bit_width() - 1;
                let end = if n > start { 0 } else { start + 1 - n };

                let bits = self.number.bits(start..end);
                self.number = self.number << n;
                self.bits_left -= n as isize;

                Some(bits)
            }
        }
    }
}

/// A helper trait to avoid dependencies.
pub trait Int:
    Shl<usize, Output=Self> +
    Shr<usize, Output=Self> +
    Not<Output=Self> +
    BitAnd<Output=Self> +
    BitOr<Output=Self> +
    PartialEq<Self> +
    Clone + Copy
{
    fn bit_width() -> usize;
    fn zero() -> Self;
    fn one() -> Self;
    fn cshl(self, n: usize) -> Self;
}

macro_rules! impl_int {
    ($($t:ty : $w:expr, $z:expr, $o:expr);*) => ($(
        impl Int for $t {
            fn bit_width() -> usize { $w }
            fn zero() -> Self { $z }
            fn one() -> Self { $o }
            fn cshl(self, n: usize) -> Self {
                self.checked_shl(n as u32).unwrap_or(0)
            }
        }
    )*)
}

impl_int! {
    u8:   8, 0, 1;
    u16: 16, 0, 1;
    u32: 32, 0, 1;
    u64: 64, 0, 1
}

#[cfg(test)]
mod tests {
    use Twiddle;

    #[test]
    fn mask_middle() {
        assert_eq!(u8::mask(4..2), 0b0001_1100);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(u8::mask(4...2), 0b0001_1100);
    }

    #[test]
    fn mask_top() {
        assert_eq!(u8::mask(7..3), 0b1111_1000);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(u8::mask(7...3), 0b1111_1000);
    }

    #[test]
    fn mask_bottom() {
        assert_eq!(u8::mask(2..0), 0b0000_0111);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(u8::mask(2...0), 0b0000_0111);
    }

    #[test]
    fn mask_full() {
        assert_eq!(u8::mask(7..0), 0b1111_1111);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(u8::mask(7...0), 0b1111_1111);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed")]
    fn mask_reversed() {
        u8::mask(2..4);
        #[cfg(feature = "inclusive_range")]
        u8::mask(2...4);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "assertion failed")]
    fn mask_overflow() {
        u8::mask(99..2);
        #[cfg(feature = "inclusive_range")]
        u8::mask(99...2);
    }

    #[test]
    fn bit() {
        let byte: u8 = 0b0010_1001;

        let mut bits = [false; 8];
        for i in 0..8 {
            bits[i] = byte.bit(7 - i);
        }

        assert_eq!(bits, [false, false, true, false, true, false, false, true]);
    }

    #[test]
    fn bits_middle() {
        assert_eq!(0b0010_1110_1001_0011u16.bits(10..3), 0b0000_0000_1101_0010);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b0010_1110_1001_0011u16.bits(10...3), 0b0000_0000_1101_0010);
    }

    #[test]
    fn bits_top() {
        assert_eq!(0b1110_0011_0011_1111u16.bits(15..12), 0b0000_0000_0000_1110);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b1110_0011_0011_1111u16.bits(15...12),
                   0b0000_0000_0000_1110);
    }

    #[test]
    fn bits_bottom() {
        assert_eq!(0b0111_1011_1000_0110u16.bits(6..0), 0b0000_0000_0000_0110);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b0111_1011_1000_0110u16.bits(6...0), 0b0000_0000_0000_0110);
    }

    #[test]
    fn bits_full() {
        assert_eq!(0b1100_1010_0111_1000u16.bits(15..0), 0b1100_1010_0111_1000);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b1100_1010_0111_1000u16.bits(15...0), 0b1100_1010_0111_1000);
    }

    #[test]
    fn replace_middle() {
        assert_eq!(0b0111_0010_1100_1101u16.replace(11..5, 0b011_0011),
                   0b0111_0110_0110_1101u16);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b0111_0010_1100_1101u16.replace(11...5, 0b011_0011),
                   0b0111_0110_0110_1101u16);
    }

    #[test]
    fn replace_top() {
        assert_eq!(0b0011_1100_0101_0110u16.replace(15..10, 0b11_0101),
                   0b1101_0100_0101_0110u16);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b0011_1100_0101_0110u16.replace(15...10, 0b11_0101),
                   0b1101_0100_0101_0110u16);
    }

    #[test]
    fn replace_bottom() {
        assert_eq!(0b1111_1001_0100_1100u16.replace(7..0, 0b1110_1110),
                   0b1111_1001_1110_1110u16);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b1111_1001_0100_1100u16.replace(7...0, 0b1110_1110),
                   0b1111_1001_1110_1110u16);
    }

    #[test]
    fn replace_full() {
        assert_eq!(0b1001_1001_1110_0001u16.replace(15..0, 0b1010_0101_0010_0111),
                   0b1010_0101_0010_0111);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b1001_1001_1110_0001u16.replace(15...0, 0b1010_0101_0010_0111),
                   0b1010_0101_0010_0111);
    }

    #[test]
    fn replace_overlong() {
        assert_eq!(0b0000_0000_0000_0000u16.replace(7..4, 0b1111_1111_1111),
                   0b0000_0000_1111_0000);
        #[cfg(feature = "inclusive_range")]
        assert_eq!(0b0000_0000_0000_0000u16.replace(7...4, 0b1111_1111_1111),
                   0b0000_0000_1111_0000);
    }

    #[test]
    fn split() {
        let n: u32 = 0b111_000000_1111111_0000_1111_000000_11;
        let lengths = [3, 6, 7, 4, 4, 6, 5, 9];

        let mut sets = [0; 7];
        for (i, set) in n.split(lengths.iter().cloned()).enumerate() {
            sets[i] = set;
        }
        assert_eq!(sets, [0b111, 0b0, 0b1111111, 0b0, 0b1111, 0b0, 0b11000]);
    }
}
