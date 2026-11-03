//! `std/Float.taut` says what Nib's `Float` computes: the kernel's values
//! of its definitions are the hardware's, and a program the kernel checked
//! runs alike on every backend.
use std::{
    fmt::Write,
    path::{Path, PathBuf},
    process::Command,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[&str], path: &Path, target: &Path) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .arg(path)
        .env("TAUTO_TARGET_DIR", target)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn float_example_runs_alike_on_every_backend() {
    let example = root().join("examples/float");
    let target = std::env::temp_dir().join(format!("tauto-float-{}", std::process::id()));
    let expected = "\
hypot = 5
hypot_tiny = 0
tenths = false
mean_none = None
mean = Some(1.5)
units = Some(-3)
units_nan = None
units_large = None
nan_bits = 9221120237041090560
neg_nan_bits = 9221120237041090560
growth = 1.6487212707001282
";
    assert_eq!(run(&["run", "--tote"], &example, &target), expected);
    assert_eq!(
        run(&["run", "--backend", "rust"], &example, &target),
        expected
    );
    assert_eq!(
        run(&["run", "--backend", "javascript"], &example, &target),
        expected
    );
}

/// The bits a run gives for NaN, whichever NaN it is.
fn canonical(x: f64) -> u64 {
    if x.is_nan() {
        0x7FF8_0000_0000_0000
    } else {
        x.to_bits()
    }
}

struct Xorshift(u64);

impl Xorshift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// Edge values, any bits, small ratios, and numbers near overflow and
/// underflow, in turn.
fn pick(r: &mut Xorshift) -> f64 {
    const EDGES: &[f64] = &[
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -2.5,
        0.1,
        0.3,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::MAX,
        f64::MIN_POSITIVE,
        5e-324,
        -5e-324,
        2.225_073_858_507_201e-308,
        4503599627370497.0,
        9007199254740993.0,
        1.000_000_000_000_000_2,
        9.223_372_036_854_775e18,
        0.499_999_999_999_999_94,
    ];
    match r.next() % 4 {
        0 => EDGES[(r.next() % EDGES.len() as u64) as usize],
        1 => f64::from_bits(r.next()),
        2 => {
            let e = (r.next() % 80) as i32 - 40;
            ((r.next() % 2000) as f64 - 1000.0) * 2f64.powi(e) / 7.0
        }
        _ => f64::from_bits(
            r.next() & 0x800F_FFFF_FFFF_FFFF
                | ((r.next() % 64) << 52)
                | if r.next() % 2 == 0 {
                    0x7C00_0000_0000_0000
                } else {
                    0
                },
        ),
    }
}

#[test]
fn the_kernel_computes_what_the_hardware_does() {
    let dir = std::env::temp_dir().join(format!("tauto-float-model-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut src = String::from(
        "import std::Float\nimport std::UInt\n\n\
         fn raw(n: Nat): Float {\n  Float::of_raw(n)\n}\n\n\
         fn bits(x: Float): Nat {\n  U64::val(Float::bits(x))\n}\n\n",
    );
    let mut r = Xorshift(0x2545_F491_4F6C_DD1D);
    for i in 0..60 {
        let a = pick(&mut r);
        let mut b = pick(&mut r);
        // Nearly equal ones, for cancellation.
        if r.next() % 5 == 0 {
            b = f64::from_bits(a.to_bits() ^ (r.next() % 8));
            if r.next() % 2 == 0 {
                b = -b;
            }
        }
        let (x, y) = (a.to_bits(), b.to_bits());
        let mut checks = vec![
            (format!("Float::add(raw({x}), raw({y}))"), canonical(a + b)),
            (format!("Float::sub(raw({x}), raw({y}))"), canonical(a - b)),
            (format!("Float::mul(raw({x}), raw({y}))"), canonical(a * b)),
            (format!("Float::neg(raw({x}))"), canonical(-a)),
            (format!("Float::abs(raw({x}))"), canonical(a.abs())),
            (format!("Float::sqrt(raw({x}))"), canonical(a.sqrt())),
            (format!("Float::trunc(raw({x}))"), canonical(a.trunc())),
            (format!("Float::floor(raw({x}))"), canonical(a.floor())),
            (format!("Float::ceil(raw({x}))"), canonical(a.ceil())),
            (format!("Float::round(raw({x}))"), canonical(a.round())),
        ];
        if b != 0.0 {
            checks.push((
                format!("Float::div(raw({x}), raw({y}), Refl)"),
                canonical(a / b),
            ));
        }
        for (j, (e, want)) in checks.iter().enumerate() {
            writeln!(
                src,
                "theorem v{i}_{j}(): bits({e}) = {want} {{\n  Refl\n}}\n"
            )
            .unwrap();
        }
        for (name, op, want) in [
            ("lt", "Float::lt", a < b),
            ("le", "Float::le", a <= b),
            ("eq", "Float::eq", a == b),
        ] {
            let want = if want { "true" } else { "false" };
            writeln!(
                src,
                "theorem {name}{i}(): Eq(Bool, {op}(raw({x}), raw({y})), {want}) {{\n  Refl\n}}\n"
            )
            .unwrap();
        }
    }
    let file = dir.join("model.taut");
    std::fs::write(&file, src).unwrap();
    let out = run(&["check"], &file, &dir.join("target"));
    assert_eq!(out, "ok\n");
}

/// A finite `Float` whose number the kernel computes at once: below `2^30`,
/// with 30 binary digits and a denominator at most `2^34`, so that the
/// numbers of two of them, multiplied or divided and then rounded, stay
/// below `2^128`.
fn pick_moderate(r: &mut Xorshift) -> f64 {
    let m = (r.next() >> 34) as f64;
    let e = (r.next() % 35) as i32 - 34;
    let x = m * 2f64.powi(e);
    if r.next() % 2 == 0 { -x } else { x }
}

/// `std/FloatReal.taut`: each operation gives the rounding of the exact
/// result of the numbers it is given, and rounding a `Float`'s number gives
/// the `Float` back.
#[test]
fn operations_round_the_exact_result() {
    let dir = std::env::temp_dir().join(format!("tauto-float-real-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut src = String::from(
        "import std::Float\nimport std::FloatReal\nimport std::Rat\n\n\
         fn raw(n: Nat): Float {\n  Float::of_raw(n)\n}\n\n\
         fn val(n: Nat): Rat {\n  match Float::val(raw(n)): Rat {\n    None => Rat::of_nat(0)\n    Some(r) => r\n  }\n}\n\n",
    );
    let mut r = Xorshift(0x9E37_79B9_7F4A_7C15);
    for i in 0..60 {
        let (a, b) = (pick_moderate(&mut r), pick_moderate(&mut r));
        let (x, y) = (a.to_bits(), b.to_bits());
        let mut checks = vec![
            format!("Float::of_rat(val({x})) = raw({x})"),
            format!("Float::of_rat(Rat::add(val({x}), val({y}))) = Float::add(raw({x}), raw({y}))"),
            format!("Float::of_rat(Rat::sub(val({x}), val({y}))) = Float::sub(raw({x}), raw({y}))"),
            format!("Float::of_rat(Rat::mul(val({x}), val({y}))) = Float::mul(raw({x}), raw({y}))"),
            format!(
                "Float::of_rat(Rat::div(val({x}), val({y}), Refl)) = Float::div(raw({x}), raw({y}), Refl)"
            ),
        ];
        if a == b {
            // `x - x` is `+0`, the number 0 rounds to.
            checks.truncate(2);
        }
        for (j, c) in checks.iter().enumerate() {
            writeln!(src, "theorem r{i}_{j}(): {c} {{\n  Refl\n}}\n").unwrap();
        }
    }
    let file = dir.join("real.taut");
    std::fs::write(&file, src).unwrap();
    let out = run(&["check"], &file, &dir.join("target"));
    assert_eq!(out, "ok\n");
}

#[test]
fn float32_example_runs_alike_on_every_backend() {
    let example = root().join("examples/float32");
    let target = std::env::temp_dir().join(format!("tauto-float32-{}", std::process::id()));
    let expected = "\
dot2 = 5
tenths = true
tenth = 0.10000000149011612
tenth_bits = 1036831949
ratio_none = None
ratio = Some(0.3333333432674408)
overflow = inf
nan_bits = 2143289344
exp = 2.7182817459106445
";
    assert_eq!(run(&["run", "--tote"], &example, &target), expected);
    assert_eq!(
        run(&["run", "--backend", "eval", "--tote"], &example, &target),
        expected
    );
    assert_eq!(
        run(&["run", "--backend", "rust"], &example, &target),
        expected
    );
    assert_eq!(
        run(&["run", "--backend", "javascript"], &example, &target),
        expected
    );
}

/// The bits a run gives for a `Float32` NaN, whichever NaN it is.
fn canonical32(x: f32) -> u32 {
    if x.is_nan() { 0x7FC0_0000 } else { x.to_bits() }
}

/// `std/Float32.taut` computes what the hardware's `f32` does, and
/// `Float32::of_rat` rounds a number as `f32` arithmetic rounds its exact
/// result.
#[test]
fn the_kernel_computes_what_the_hardware_does_in_float32() {
    let dir = std::env::temp_dir().join(format!("tauto-float32-model-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut src = String::from(
        "import std::Float\nimport std::Float32\nimport std::FloatReal\nimport std::Rat\n\n\
         fn raw(n: Nat): Float32 {\n  Float32::of_raw(n)\n}\n\n\
         fn wide(n: Nat): Float {\n  Float::of_raw(n)\n}\n\n\
         fn val(n: Nat): Rat {\n  match Float32::val(raw(n)): Rat {\n    None => Rat::of_nat(0)\n    Some(r) => r\n  }\n}\n\n",
    );
    let mut r = Xorshift(0x2545_F491_4F6C_DD1D);
    for i in 0..60 {
        // Any bits, and `Float`s near the edges of `Float32`'s range.
        let a = f32::from_bits(r.next() as u32);
        let b = if r.next() % 3 == 0 {
            f32::from_bits(a.to_bits() ^ (r.next() as u32 % 8))
        } else {
            f32::from_bits(r.next() as u32)
        };
        let w = pick(&mut r);
        let (x, y) = (a.to_bits(), b.to_bits());
        let mut checks = vec![
            (
                format!("Float32::add(raw({x}), raw({y}))"),
                canonical32(a + b),
            ),
            (
                format!("Float32::sub(raw({x}), raw({y}))"),
                canonical32(a - b),
            ),
            (
                format!("Float32::mul(raw({x}), raw({y}))"),
                canonical32(a * b),
            ),
            (format!("Float32::neg(raw({x}))"), canonical32(-a)),
            (format!("Float32::abs(raw({x}))"), canonical32(a.abs())),
            (format!("Float32::sqrt(raw({x}))"), canonical32(a.sqrt())),
            (format!("Float32::floor(raw({x}))"), canonical32(a.floor())),
            (format!("Float32::round(raw({x}))"), canonical32(a.round())),
            (
                format!("Float32::of_float(wide({}))", w.to_bits()),
                canonical32(w as f32),
            ),
        ];
        if b != 0.0 {
            checks.push((
                format!("Float32::div(raw({x}), raw({y}), Refl)"),
                canonical32(a / b),
            ));
        }
        for (j, (e, want)) in checks.iter().enumerate() {
            writeln!(
                src,
                "theorem v{i}_{j}(): Float32::raw({e}) = {want} {{\n  Refl\n}}\n"
            )
            .unwrap();
        }
        writeln!(
            src,
            "theorem w{i}(): Float::raw(Float::of_float32(raw({x}))) = {} {{\n  Refl\n}}\n",
            canonical(f64::from(a))
        )
        .unwrap();
        writeln!(
            src,
            "theorem lt{i}(): (Float32::lt(raw({x}), raw({y})) = {}) {{\n  Refl\n}}\n",
            if a < b { "true" } else { "false" }
        )
        .unwrap();
        // Small numbers, whose sums and products the kernel computes at once.
        let (c, d) = (pick_moderate(&mut r) as f32, pick_moderate(&mut r) as f32);
        let (u, v) = (c.to_bits(), d.to_bits());
        for (k, (e, want)) in [
            (format!("Rat::add(val({u}), val({v}))"), canonical32(c + d)),
            (format!("Rat::mul(val({u}), val({v}))"), canonical32(c * d)),
        ]
        .iter()
        .enumerate()
        {
            if *want == 0 || *want == 0x8000_0000 {
                continue;
            }
            writeln!(
                src,
                "theorem q{i}_{k}(): Float32::raw(Float32::of_rat({e})) = {want} {{\n  Refl\n}}\n"
            )
            .unwrap();
        }
    }
    let file = dir.join("model32.taut");
    std::fs::write(&file, src).unwrap();
    let out = run(&["check"], &file, &dir.join("target"));
    assert_eq!(out, "ok\n");
}
