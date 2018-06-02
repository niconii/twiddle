# twiddle

A small library for bit-twiddling.

[Documentation](https://docs.rs/twiddle)

## Usage

You can use it by adding this to your `Cargo.toml` file:

```toml
[dependencies]
twiddle = "1.0"
```

and adding this to the top of your crate root (`main.rs` or `lib.rs`):

```rust
extern crate twiddle;

use twiddle::Twiddle;
```

## Example

```rust
extern crate twiddle;

use twiddle::Twiddle;

struct UnpackedF32 {
    negative: bool,
    exponent: i16,
    fraction: u32,
}

impl From<f32> for UnpackedF32 {
    fn from(f: f32) -> UnpackedF32 {
        let b = unsafe { std::mem::transmute::<f32, u32>(f) };
        UnpackedF32 {
            negative: b.bit(31),
            exponent: (b.bits(30..23) as i16) - 127,
            fraction: b.bits(22..0)
        }
    }
}

fn main() {
    for f in -5..=5 {
        let u = UnpackedF32::from(f as f32);
        println!("{:+} = {}1.{:023b} * 2^{}",
            f,
            match u.negative { false => "+", true => "-" },
            u.fraction,
            u.exponent
        );
    }
}
```

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
