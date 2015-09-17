# twiddle

A small library for bit-twiddling.

You can use it as a dependency by adding it to your `Cargo.toml` file.

```toml
[dependencies]
twiddle = "*"
```

[Documentation](http://nicole.moe/docs/twiddle/index.html)

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
    for f in (-5..6) {
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
