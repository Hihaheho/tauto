//! The functions of `Float` that are not exact in IEEE 754 (`sin`, `ln`,
//! `pow`, …), written out here so that every backend computes the same
//! bits: the evaluator and the Rust backend call these, and the JavaScript
//! backend runs the same algorithms, operation for operation
//! (`crates/tauto-jsgen/src/float.js`). The platform's own functions are not
//! used, because they differ between platforms in the last bit.
//!
//! Each module below is a copy of the module of the same name of the `libm`
//! crate, version 0.2.11 (MIT OR Apache-2.0), with the macros written out,
//! the tests and the paths for other precisions left out, and the notices of
//! the sources kept. The license of `libm` and the notices of musl libc and
//! FreeBSD it carries are in `NOTICE` at the root of the repository. The
//! `TODO` and `FIXME` comments in the modules are those of the sources,
//! kept as they are.
#![allow(
    clippy::all,
    unused_assignments,
    unused_mut,
    unused_parens,
    unused_variables,
    dead_code
)]

fn get_high_word(x: f64) -> u32 {
    (x.to_bits() >> 32) as u32
}

fn get_low_word(x: f64) -> u32 {
    x.to_bits() as u32
}

fn with_set_high_word(f: f64, hi: u32) -> f64 {
    f64::from_bits((f.to_bits() & 0x0000_0000_ffff_ffff) | ((hi as u64) << 32))
}

fn with_set_low_word(f: f64, lo: u32) -> f64 {
    f64::from_bits((f.to_bits() & 0xffff_ffff_0000_0000) | lo as u64)
}

fn combine_words(hi: u32, lo: u32) -> f64 {
    f64::from_bits(((hi as u64) << 32) | lo as u64)
}

// Exact in IEEE 754, so the platform's are the same everywhere.
fn sqrt(x: f64) -> f64 {
    x.sqrt()
}

fn fabs(x: f64) -> f64 {
    x.abs()
}

fn floor(x: f64) -> f64 {
    x.floor()
}

mod scalbn {
    #![allow(unused_imports)]
    use super::*;

    pub fn scalbn(x: f64, mut n: i32) -> f64 {
        let x1p1023 = f64::from_bits(0x7fe0000000000000); // 0x1p1023 === 2 ^ 1023
        let x1p53 = f64::from_bits(0x4340000000000000); // 0x1p53 === 2 ^ 53
        let x1p_1022 = f64::from_bits(0x0010000000000000); // 0x1p-1022 === 2 ^ (-1022)

        let mut y = x;

        if n > 1023 {
            y *= x1p1023;
            n -= 1023;
            if n > 1023 {
                y *= x1p1023;
                n -= 1023;
                if n > 1023 {
                    n = 1023;
                }
            }
        } else if n < -1022 {
            /* make sure final n < -53 to avoid double
            rounding in the subnormal range */
            y *= x1p_1022 * x1p53;
            n += 1022 - 53;
            if n < -1022 {
                y *= x1p_1022 * x1p53;
                n += 1022 - 53;
                if n < -1022 {
                    n = -1022;
                }
            }
        }
        y * f64::from_bits(((0x3ff + n) as u64) << 52)
    }
}
pub use scalbn::*;

mod k_sin {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/k_sin.c
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunSoft, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    const S1: f64 = -1.66666666666666324348e-01; /* 0xBFC55555, 0x55555549 */
    const S2: f64 = 8.33333333332248946124e-03; /* 0x3F811111, 0x1110F8A6 */
    const S3: f64 = -1.98412698298579493134e-04; /* 0xBF2A01A0, 0x19C161D5 */
    const S4: f64 = 2.75573137070700676789e-06; /* 0x3EC71DE3, 0x57B1FE7D */
    const S5: f64 = -2.50507602534068634195e-08; /* 0xBE5AE5E6, 0x8A2B9CEB */
    const S6: f64 = 1.58969099521155010221e-10; /* 0x3DE5D93A, 0x5ACFD57C */

    // kernel sin function on ~[-pi/4, pi/4] (except on -0), pi/4 ~ 0.7854
    // Input x is assumed to be bounded by ~pi/4 in magnitude.
    // Input y is the tail of x.
    // Input iy indicates whether y is 0. (if iy=0, y assume to be 0).
    //
    // Algorithm
    //      1. Since sin(-x) = -sin(x), we need only to consider positive x.
    //      2. Callers must return sin(-0) = -0 without calling here since our
    //         odd polynomial is not evaluated in a way that preserves -0.
    //         Callers may do the optimization sin(x) ~ x for tiny x.
    //      3. sin(x) is approximated by a polynomial of degree 13 on
    //         [0,pi/4]
    //                               3            13
    //              sin(x) ~ x + S1*x + ... + S6*x
    //         where
    //
    //      |sin(x)         2     4     6     8     10     12  |     -58
    //      |----- - (1+S1*x +S2*x +S3*x +S4*x +S5*x  +S6*x   )| <= 2
    //      |  x                                               |
    //
    //      4. sin(x+y) = sin(x) + sin'(x')*y
    //                  ~ sin(x) + (1-x*x/2)*y
    //         For better accuracy, let
    //                   3      2      2      2      2
    //              r = x *(S2+x *(S3+x *(S4+x *(S5+x *S6))))
    //         then                   3    2
    //              sin(x) = x + (S1*x + (x *(r-y/2)+y))
    pub fn k_sin(x: f64, y: f64, iy: i32) -> f64 {
        let z = x * x;
        let w = z * z;
        let r = S2 + z * (S3 + z * S4) + z * w * (S5 + z * S6);
        let v = z * x;
        if iy == 0 {
            x + v * (S1 + z * r)
        } else {
            x - ((z * (0.5 * y - v * r) - y) - v * S1)
        }
    }
}
pub use k_sin::*;

mod k_cos {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/k_cos.c
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunSoft, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    const C1: f64 = 4.16666666666666019037e-02; /* 0x3FA55555, 0x5555554C */
    const C2: f64 = -1.38888888888741095749e-03; /* 0xBF56C16C, 0x16C15177 */
    const C3: f64 = 2.48015872894767294178e-05; /* 0x3EFA01A0, 0x19CB1590 */
    const C4: f64 = -2.75573143513906633035e-07; /* 0xBE927E4F, 0x809C52AD */
    const C5: f64 = 2.08757232129817482790e-09; /* 0x3E21EE9E, 0xBDB4B1C4 */
    const C6: f64 = -1.13596475577881948265e-11; /* 0xBDA8FAE9, 0xBE8838D4 */

    // kernel cos function on [-pi/4, pi/4], pi/4 ~ 0.785398164
    // Input x is assumed to be bounded by ~pi/4 in magnitude.
    // Input y is the tail of x.
    //
    // Algorithm
    //      1. Since cos(-x) = cos(x), we need only to consider positive x.
    //      2. if x < 2^-27 (hx<0x3e400000 0), return 1 with inexact if x!=0.
    //      3. cos(x) is approximated by a polynomial of degree 14 on
    //         [0,pi/4]
    //                                       4            14
    //              cos(x) ~ 1 - x*x/2 + C1*x + ... + C6*x
    //         where the remez error is
    //
    //      |              2     4     6     8     10    12     14 |     -58
    //      |cos(x)-(1-.5*x +C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  )| <= 2
    //      |                                                      |
    //
    //                     4     6     8     10    12     14
    //      4. let r = C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  , then
    //             cos(x) ~ 1 - x*x/2 + r
    //         since cos(x+y) ~ cos(x) - sin(x)*y
    //                        ~ cos(x) - x*y,
    //         a correction term is necessary in cos(x) and hence
    //              cos(x+y) = 1 - (x*x/2 - (r - x*y))
    //         For better accuracy, rearrange to
    //              cos(x+y) ~ w + (tmp + (r-x*y))
    //         where w = 1 - x*x/2 and tmp is a tiny correction term
    //         (1 - x*x/2 == w + tmp exactly in infinite precision).
    //         The exactness of w + tmp in infinite precision depends on w
    //         and tmp having the same precision as x.  If they have extra
    //         precision due to compiler bugs, then the extra precision is
    //         only good provided it is retained in all terms of the final
    //         expression for cos().  Retention happens in all cases tested
    //         under FreeBSD, so don't pessimize things by forcibly clipping
    //         any extra precision in w.
    pub fn k_cos(x: f64, y: f64) -> f64 {
        let z = x * x;
        let w = z * z;
        let r = z * (C1 + z * (C2 + z * C3)) + w * w * (C4 + z * (C5 + z * C6));
        let hz = 0.5 * z;
        let w = 1.0 - hz;
        w + (((1.0 - w) - hz) + (z * r - x * y))
    }
}
pub use k_cos::*;

mod k_tan {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/k_tan.c */
    //
    // ====================================================
    // Copyright 2004 Sun Microsystems, Inc.  All Rights Reserved.
    //
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    // kernel tan function on ~[-pi/4, pi/4] (except on -0), pi/4 ~ 0.7854
    // Input x is assumed to be bounded by ~pi/4 in magnitude.
    // Input y is the tail of x.
    // Input odd indicates whether tan (if odd = 0) or -1/tan (if odd = 1) is returned.
    //
    // Algorithm
    //      1. Since tan(-x) = -tan(x), we need only to consider positive x.
    //      2. Callers must return tan(-0) = -0 without calling here since our
    //         odd polynomial is not evaluated in a way that preserves -0.
    //         Callers may do the optimization tan(x) ~ x for tiny x.
    //      3. tan(x) is approximated by a odd polynomial of degree 27 on
    //         [0,0.67434]
    //                               3             27
    //              tan(x) ~ x + T1*x + ... + T13*x
    //         where
    //
    //              |tan(x)         2     4            26   |     -59.2
    //              |----- - (1+T1*x +T2*x +.... +T13*x    )| <= 2
    //              |  x                                    |
    //
    //         Note: tan(x+y) = tan(x) + tan'(x)*y
    //                        ~ tan(x) + (1+x*x)*y
    //         Therefore, for better accuracy in computing tan(x+y), let
    //                   3      2      2       2       2
    //              r = x *(T2+x *(T3+x *(...+x *(T12+x *T13))))
    //         then
    //                                  3    2
    //              tan(x+y) = x + (T1*x + (x *(r+y)+y))
    //
    //      4. For x in [0.67434,pi/4],  let y = pi/4 - x, then
    //              tan(x) = tan(pi/4-y) = (1-tan(y))/(1+tan(y))
    //                     = 1 - 2*(tan(y) - (tan(y)^2)/(1+tan(y)))
    static T: [f64; 13] = [
        3.33333333333334091986e-01,  /* 3FD55555, 55555563 */
        1.33333333333201242699e-01,  /* 3FC11111, 1110FE7A */
        5.39682539762260521377e-02,  /* 3FABA1BA, 1BB341FE */
        2.18694882948595424599e-02,  /* 3F9664F4, 8406D637 */
        8.86323982359930005737e-03,  /* 3F8226E3, E96E8493 */
        3.59207910759131235356e-03,  /* 3F6D6D22, C9560328 */
        1.45620945432529025516e-03,  /* 3F57DBC8, FEE08315 */
        5.88041240820264096874e-04,  /* 3F4344D8, F2F26501 */
        2.46463134818469906812e-04,  /* 3F3026F7, 1A8D1068 */
        7.81794442939557092300e-05,  /* 3F147E88, A03792A6 */
        7.14072491382608190305e-05,  /* 3F12B80F, 32F0A7E9 */
        -1.85586374855275456654e-05, /* BEF375CB, DB605373 */
        2.59073051863633712884e-05,  /* 3EFB2A70, 74BF7AD4 */
    ];
    const PIO4: f64 = 7.85398163397448278999e-01; /* 3FE921FB, 54442D18 */
    const PIO4_LO: f64 = 3.06161699786838301793e-17; /* 3C81A626, 33145C07 */

    pub fn k_tan(mut x: f64, mut y: f64, odd: i32) -> f64 {
        let hx = (f64::to_bits(x) >> 32) as u32;
        let big = (hx & 0x7fffffff) >= 0x3FE59428; /* |x| >= 0.6744 */
        if big {
            let sign = hx >> 31;
            if sign != 0 {
                x = -x;
                y = -y;
            }
            x = (PIO4 - x) + (PIO4_LO - y);
            y = 0.0;
        }
        let z = x * x;
        let w = z * z;
        /*
         * Break x^5*(T[1]+x^2*T[2]+...) into
         * x^5(T[1]+x^4*T[3]+...+x^20*T[11]) +
         * x^5(x^2*(T[2]+x^4*T[4]+...+x^22*[T12]))
         */
        let r = T[1] + w * (T[3] + w * (T[5] + w * (T[7] + w * (T[9] + w * T[11]))));
        let v = z * (T[2] + w * (T[4] + w * (T[6] + w * (T[8] + w * (T[10] + w * T[12])))));
        let s = z * x;
        let r = y + z * (s * (r + v) + y) + s * T[0];
        let w = x + r;
        if big {
            let sign = hx >> 31;
            let s = 1.0 - 2.0 * odd as f64;
            let v = s - 2.0 * (x + (r - w * w / (w + s)));
            return if sign != 0 { -v } else { v };
        }
        if odd == 0 {
            return w;
        }
        /* -1.0/(x+r) has up to 2ulp error, so compute it accurately */
        let w0 = zero_low_word(w);
        let v = r - (w0 - x); /* w0+v = r+x */
        let a = -1.0 / w;
        let a0 = zero_low_word(a);
        a0 + a * (1.0 + a0 * w0 + a0 * v)
    }

    pub fn zero_low_word(x: f64) -> f64 {
        f64::from_bits(f64::to_bits(x) & 0xFFFF_FFFF_0000_0000)
    }
}
pub use k_tan::*;

mod rem_pio2_large {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/k_rem_pio2.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */

    // initial value for jk
    const INIT_JK: [usize; 4] = [3, 4, 4, 6];

    // Table of constants for 2/pi, 396 Hex digits (476 decimal) of 2/pi
    //
    //              integer array, contains the (24*i)-th to (24*i+23)-th
    //              bit of 2/pi after binary point. The corresponding
    //              floating value is
    //
    //                      ipio2[i] * 2^(-24(i+1)).
    //
    // NB: This table must have at least (e0-3)/24 + jk terms.
    //     For quad precision (e0 <= 16360, jk = 6), this is 686.
    const IPIO2: [i32; 66] = [
        0xA2F983, 0x6E4E44, 0x1529FC, 0x2757D1, 0xF534DD, 0xC0DB62, 0x95993C, 0x439041, 0xFE5163,
        0xABDEBB, 0xC561B7, 0x246E3A, 0x424DD2, 0xE00649, 0x2EEA09, 0xD1921C, 0xFE1DEB, 0x1CB129,
        0xA73EE8, 0x8235F5, 0x2EBB44, 0x84E99C, 0x7026B4, 0x5F7E41, 0x3991D6, 0x398353, 0x39F49C,
        0x845F8B, 0xBDF928, 0x3B1FF8, 0x97FFDE, 0x05980F, 0xEF2F11, 0x8B5A0A, 0x6D1F6D, 0x367ECF,
        0x27CB09, 0xB74F46, 0x3F669E, 0x5FEA2D, 0x7527BA, 0xC7EBE5, 0xF17B3D, 0x0739F7, 0x8A5292,
        0xEA6BFB, 0x5FB11F, 0x8D5D08, 0x560330, 0x46FC7B, 0x6BABF0, 0xCFBC20, 0x9AF436, 0x1DA9E3,
        0x91615E, 0xE61B08, 0x659985, 0x5F14A0, 0x68408D, 0xFFD880, 0x4D7327, 0x310606, 0x1556CA,
        0x73A8C9, 0x60E27B, 0xC08C6B,
    ];

    const PIO2: [f64; 8] = [
        1.57079625129699707031e+00, /* 0x3FF921FB, 0x40000000 */
        7.54978941586159635335e-08, /* 0x3E74442D, 0x00000000 */
        5.39030252995776476554e-15, /* 0x3CF84698, 0x80000000 */
        3.28200341580791294123e-22, /* 0x3B78CC51, 0x60000000 */
        1.27065575308067607349e-29, /* 0x39F01B83, 0x80000000 */
        1.22933308981111328932e-36, /* 0x387A2520, 0x40000000 */
        2.73370053816464559624e-44, /* 0x36E38222, 0x80000000 */
        2.16741683877804819444e-51, /* 0x3569F31D, 0x00000000 */
    ];

    // fn rem_pio2_large(x : &[f64], y : &mut [f64], e0 : i32, prec : usize) -> i32
    //
    // Input parameters:
    //      x[]     The input value (must be positive) is broken into nx
    //              pieces of 24-bit integers in double precision format.
    //              x[i] will be the i-th 24 bit of x. The scaled exponent
    //              of x[0] is given in input parameter e0 (i.e., x[0]*2^e0
    //              match x's up to 24 bits.
    //
    //              Example of breaking a double positive z into x[0]+x[1]+x[2]:
    //                      e0 = ilogb(z)-23
    //                      z  = scalbn(z,-e0)
    //              for i = 0,1,2
    //                      x[i] = floor(z)
    //                      z    = (z-x[i])*2**24
    //
    //      y[]     ouput result in an array of double precision numbers.
    //              The dimension of y[] is:
    //                      24-bit  precision       1
    //                      53-bit  precision       2
    //                      64-bit  precision       2
    //                      113-bit precision       3
    //              The actual value is the sum of them. Thus for 113-bit
    //              precison, one may have to do something like:
    //
    //              long double t,w,r_head, r_tail;
    //              t = (long double)y[2] + (long double)y[1];
    //              w = (long double)y[0];
    //              r_head = t+w;
    //              r_tail = w - (r_head - t);
    //
    //      e0      The exponent of x[0]. Must be <= 16360 or you need to
    //              expand the ipio2 table.
    //
    //      prec    an integer indicating the precision:
    //                      0       24  bits (single)
    //                      1       53  bits (double)
    //                      2       64  bits (extended)
    //                      3       113 bits (quad)
    //
    // Here is the description of some local variables:
    //
    //      jk      jk+1 is the initial number of terms of ipio2[] needed
    //              in the computation. The minimum and recommended value
    //              for jk is 3,4,4,6 for single, double, extended, and quad.
    //              jk+1 must be 2 larger than you might expect so that our
    //              recomputation test works. (Up to 24 bits in the integer
    //              part (the 24 bits of it that we compute) and 23 bits in
    //              the fraction part may be lost to cancelation before we
    //              recompute.)
    //
    //      jz      local integer variable indicating the number of
    //              terms of ipio2[] used.
    //
    //      jx      nx - 1
    //
    //      jv      index for pointing to the suitable ipio2[] for the
    //              computation. In general, we want
    //                      ( 2^e0*x[0] * ipio2[jv-1]*2^(-24jv) )/8
    //              is an integer. Thus
    //                      e0-3-24*jv >= 0 or (e0-3)/24 >= jv
    //              Hence jv = max(0,(e0-3)/24).
    //
    //      jp      jp+1 is the number of terms in PIo2[] needed, jp = jk.
    //
    //      q[]     double array with integral value, representing the
    //              24-bits chunk of the product of x and 2/pi.
    //
    //      q0      the corresponding exponent of q[0]. Note that the
    //              exponent for q[i] would be q0-24*i.
    //
    //      PIo2[]  double precision array, obtained by cutting pi/2
    //              into 24 bits chunks.
    //
    //      f[]     ipio2[] in floating point
    //
    //      iq[]    integer array by breaking up q[] in 24-bits chunk.
    //
    //      fq[]    final product of x*(2/pi) in fq[0],..,fq[jk]
    //
    //      ih      integer. If >0 it indicates q[] is >= 0.5, hence
    //              it also indicates the *sign* of the result.

    /// Return the last three digits of N with y = x - N*pi/2
    /// so that |y| < pi/2.
    ///
    /// The method is to compute the integer (mod 8) and fraction parts of
    /// (2/pi)*x without doing the full multiplication. In general we
    /// skip the part of the product that are known to be a huge integer (
    /// more accurately, = 0 mod 8 ). Thus the number of operations are
    /// independent of the exponent of the input.
    pub fn rem_pio2_large(x: &[f64], y: &mut [f64], e0: i32, prec: usize) -> i32 {
        let x1p24 = f64::from_bits(0x4170000000000000); // 0x1p24 === 2 ^ 24
        let x1p_24 = f64::from_bits(0x3e70000000000000); // 0x1p_24 === 2 ^ (-24)

        let nx = x.len();

        let mut fw: f64;
        let mut n: i32;
        let mut ih: i32;
        let mut z: f64;
        let mut f: [f64; 20] = [0.; 20];
        let mut fq: [f64; 20] = [0.; 20];
        let mut q: [f64; 20] = [0.; 20];
        let mut iq: [i32; 20] = [0; 20];

        let jk = INIT_JK[prec];
        let jp = jk;

        /* determine jx,jv,q0, note that 3>q0 */
        let jx = nx - 1;
        let mut jv = ((e0 - 3) / (24));
        if jv < 0 {
            jv = 0;
        }
        let mut q0 = e0 - 24 * (jv + 1);
        let jv = jv as usize;

        /* set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk] */
        let mut j = (jv as i32) - (jx as i32);
        let m = jx + jk;
        for i in 0..=m {
            f[i] = if j < 0 { 0. } else { IPIO2[j as usize] as f64 };
            j += 1;
        }

        for i in 0..=jk {
            fw = 0f64;
            for j in 0..=jx {
                fw += x[j] * f[jx + i - j];
            }
            q[i] = fw;
        }

        let mut jz = jk;

        'recompute: loop {
            let mut i = 0i32;
            z = q[jz];
            for j in (1..=jz).rev() {
                fw = (x1p_24 * z) as i32 as f64;
                iq[i as usize] = (z - x1p24 * fw) as i32;
                z = q[j - 1] + fw;
                i += 1;
            }

            z = scalbn(z, q0); /* actual value of z */
            z -= 8.0 * floor(z * 0.125); /* trim off integer >= 8 */
            n = z as i32;
            z -= n as f64;
            ih = 0;
            if q0 > 0 {
                /* need iq[jz-1] to determine n */
                i = iq[jz - 1] >> (24 - q0);
                n += i;
                iq[jz - 1] -= i << (24 - q0);
                ih = iq[jz - 1] >> (23 - q0);
            } else if q0 == 0 {
                ih = iq[jz - 1] >> 23;
            } else if z >= 0.5 {
                ih = 2;
            }

            if ih > 0 {
                n += 1;
                let mut carry = 0i32;
                for i in 0..jz {
                    let j = iq[i];
                    if carry == 0 {
                        if j != 0 {
                            carry = 1;
                            iq[i] = 0x1000000 - j;
                        }
                    } else {
                        iq[i] = 0xffffff - j;
                    }
                }
                if q0 > 0 {
                    /* rare case: chance is 1 in 12 */
                    match q0 {
                        1 => {
                            iq[jz - 1] &= 0x7fffff;
                        }
                        2 => {
                            iq[jz - 1] &= 0x3fffff;
                        }
                        _ => {}
                    }
                }
                if ih == 2 {
                    z = 1. - z;
                    if carry != 0 {
                        z -= scalbn(1., q0);
                    }
                }
            }

            if z == 0. {
                let mut j = 0;
                for i in (jk..=jz - 1).rev() {
                    j |= iq[i];
                }
                if j == 0 {
                    let mut k = 1;
                    while iq[jk - k] == 0 {
                        k += 1; /* k = no. of terms needed */
                    }

                    for i in (jz + 1)..=(jz + k) {
                        f[jx + i] = IPIO2[jv + i] as f64;
                        fw = 0f64;
                        for j in 0..=jx {
                            fw += x[j] * f[jx + i - j];
                        }
                        q[i] = fw;
                    }
                    jz += k;
                    continue 'recompute;
                }
            }

            break;
        }

        if z == 0. {
            jz -= 1;
            q0 -= 24;
            while iq[jz] == 0 {
                jz -= 1;
                q0 -= 24;
            }
        } else {
            z = scalbn(z, -q0);
            if z >= x1p24 {
                fw = (x1p_24 * z) as i32 as f64;
                iq[jz] = (z - x1p24 * fw) as i32;
                jz += 1;
                q0 += 24;
                iq[jz] = fw as i32;
            } else {
                iq[jz] = z as i32;
            }
        }

        fw = scalbn(1., q0);
        for i in (0..=jz).rev() {
            q[i] = fw * (iq[i] as f64);
            fw *= x1p_24;
        }

        for i in (0..=jz).rev() {
            fw = 0f64;
            let mut k = 0;
            while (k <= jp) && (k <= jz - i) {
                fw += PIO2[k] * q[i + k];
                k += 1;
            }
            fq[jz - i] = fw;
        }

        match prec {
            0 => {
                fw = 0f64;
                for i in (0..=jz).rev() {
                    fw += fq[i];
                }
                y[0] = if ih == 0 { fw } else { -fw };
            }
            1 | 2 => {
                fw = 0f64;
                for i in (0..=jz).rev() {
                    fw += fq[i];
                }
                fw = fw as f64;
                y[0] = if ih == 0 { fw } else { -fw };
                fw = fq[0] - fw;
                for i in 1..=jz {
                    fw += fq[i];
                }
                y[1] = if ih == 0 { fw } else { -fw };
            }
            3 => {
                for i in (1..=jz).rev() {
                    fw = fq[i - 1] + fq[i];
                    fq[i] += fq[i - 1] - fw;
                    fq[i - 1] = fw;
                }
                for i in (2..=jz).rev() {
                    fw = fq[i - 1] + fq[i];
                    fq[i] += fq[i - 1] - fw;
                    fq[i - 1] = fw;
                }
                fw = 0f64;
                for i in (2..=jz).rev() {
                    fw += fq[i];
                }
                if ih == 0 {
                    y[0] = fq[0];
                    y[1] = fq[1];
                    y[2] = fw;
                } else {
                    y[0] = -fq[0];
                    y[1] = -fq[1];
                    y[2] = -fw;
                }
            }
            _ => unreachable!(),
        }
        n & 7
    }
}
pub use rem_pio2_large::*;

mod rem_pio2 {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/e_rem_pio2.c
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunPro, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================
    //
    // Optimized by Bruce D. Evans. */
    // #if FLT_EVAL_METHOD==0 || FLT_EVAL_METHOD==1
    // #define EPS DBL_EPSILON
    const EPS: f64 = 2.2204460492503131e-16;

    const TO_INT: f64 = 1.5 / EPS;
    /// 53 bits of 2/pi
    const INV_PIO2: f64 = 6.36619772367581382433e-01; /* 0x3FE45F30, 0x6DC9C883 */
    /// first 33 bits of pi/2
    const PIO2_1: f64 = 1.57079632673412561417e+00; /* 0x3FF921FB, 0x54400000 */
    /// pi/2 - PIO2_1
    const PIO2_1T: f64 = 6.07710050650619224932e-11; /* 0x3DD0B461, 0x1A626331 */
    /// second 33 bits of pi/2
    const PIO2_2: f64 = 6.07710050630396597660e-11; /* 0x3DD0B461, 0x1A600000 */
    /// pi/2 - (PIO2_1+PIO2_2)
    const PIO2_2T: f64 = 2.02226624879595063154e-21; /* 0x3BA3198A, 0x2E037073 */
    /// third 33 bits of pi/2
    const PIO2_3: f64 = 2.02226624871116645580e-21; /* 0x3BA3198A, 0x2E000000 */
    /// pi/2 - (PIO2_1+PIO2_2+PIO2_3)
    const PIO2_3T: f64 = 8.47842766036889956997e-32; /* 0x397B839A, 0x252049C1 */

    // return the remainder of x rem pi/2 in y[0]+y[1]
    // use rem_pio2_large() for large x
    //
    // caller must handle the case when reduction is not needed: |x| ~<= pi/4 */
    pub fn rem_pio2(x: f64) -> (i32, f64, f64) {
        let x1p24 = f64::from_bits(0x4170000000000000);

        let sign = (f64::to_bits(x) >> 63) as i32;
        let ix = (f64::to_bits(x) >> 32) as u32 & 0x7fffffff;

        fn medium(x: f64, ix: u32) -> (i32, f64, f64) {
            /* rint(x/(pi/2)), Assume round-to-nearest. */
            let tmp = x as f64 * INV_PIO2 + TO_INT;
            // force rounding of tmp to it's storage format on x87 to avoid
            // excess precision issues.
            let f_n = tmp - TO_INT;
            let n = f_n as i32;
            let mut r = x - f_n * PIO2_1;
            let mut w = f_n * PIO2_1T; /* 1st round, good to 85 bits */
            let mut y0 = r - w;
            let ui = f64::to_bits(y0);
            let ey = (ui >> 52) as i32 & 0x7ff;
            let ex = (ix >> 20) as i32;
            if ex - ey > 16 {
                /* 2nd round, good to 118 bits */
                let t = r;
                w = f_n * PIO2_2;
                r = t - w;
                w = f_n * PIO2_2T - ((t - r) - w);
                y0 = r - w;
                let ey = (f64::to_bits(y0) >> 52) as i32 & 0x7ff;
                if ex - ey > 49 {
                    /* 3rd round, good to 151 bits, covers all cases */
                    let t = r;
                    w = f_n * PIO2_3;
                    r = t - w;
                    w = f_n * PIO2_3T - ((t - r) - w);
                    y0 = r - w;
                }
            }
            let y1 = (r - y0) - w;
            (n, y0, y1)
        }

        if ix <= 0x400f6a7a {
            /* |x| ~<= 5pi/4 */
            if (ix & 0xfffff) == 0x921fb {
                /* |x| ~= pi/2 or 2pi/2 */
                return medium(x, ix); /* cancellation -- use medium case */
            }
            if ix <= 0x4002d97c {
                /* |x| ~<= 3pi/4 */
                if sign == 0 {
                    let z = x - PIO2_1; /* one round good to 85 bits */
                    let y0 = z - PIO2_1T;
                    let y1 = (z - y0) - PIO2_1T;
                    return (1, y0, y1);
                } else {
                    let z = x + PIO2_1;
                    let y0 = z + PIO2_1T;
                    let y1 = (z - y0) + PIO2_1T;
                    return (-1, y0, y1);
                }
            } else if sign == 0 {
                let z = x - 2.0 * PIO2_1;
                let y0 = z - 2.0 * PIO2_1T;
                let y1 = (z - y0) - 2.0 * PIO2_1T;
                return (2, y0, y1);
            } else {
                let z = x + 2.0 * PIO2_1;
                let y0 = z + 2.0 * PIO2_1T;
                let y1 = (z - y0) + 2.0 * PIO2_1T;
                return (-2, y0, y1);
            }
        }
        if ix <= 0x401c463b {
            /* |x| ~<= 9pi/4 */
            if ix <= 0x4015fdbc {
                /* |x| ~<= 7pi/4 */
                if ix == 0x4012d97c {
                    /* |x| ~= 3pi/2 */
                    return medium(x, ix);
                }
                if sign == 0 {
                    let z = x - 3.0 * PIO2_1;
                    let y0 = z - 3.0 * PIO2_1T;
                    let y1 = (z - y0) - 3.0 * PIO2_1T;
                    return (3, y0, y1);
                } else {
                    let z = x + 3.0 * PIO2_1;
                    let y0 = z + 3.0 * PIO2_1T;
                    let y1 = (z - y0) + 3.0 * PIO2_1T;
                    return (-3, y0, y1);
                }
            } else {
                if ix == 0x401921fb {
                    /* |x| ~= 4pi/2 */
                    return medium(x, ix);
                }
                if sign == 0 {
                    let z = x - 4.0 * PIO2_1;
                    let y0 = z - 4.0 * PIO2_1T;
                    let y1 = (z - y0) - 4.0 * PIO2_1T;
                    return (4, y0, y1);
                } else {
                    let z = x + 4.0 * PIO2_1;
                    let y0 = z + 4.0 * PIO2_1T;
                    let y1 = (z - y0) + 4.0 * PIO2_1T;
                    return (-4, y0, y1);
                }
            }
        }
        if ix < 0x413921fb {
            /* |x| ~< 2^20*(pi/2), medium size */
            return medium(x, ix);
        }
        if ix >= 0x7ff00000 {
            let y0 = x - x;
            let y1 = y0;
            return (0, y0, y1);
        }
        /* set z = scalbn(|x|,-ilogb(x)+23) */
        let mut ui = f64::to_bits(x);
        ui &= (!1) >> 12;
        ui |= (0x3ff + 23) << 52;
        let mut z = f64::from_bits(ui);
        let mut tx = [0.0; 3];
        for i in 0..2 {
            tx[i] = z as i32 as f64;
            z = (z - tx[i]) * x1p24;
        }
        tx[2] = z;
        /* skip zero terms, first term is non-zero */
        let mut i = 2;
        while i != 0 && tx[i] == 0.0 {
            i -= 1;
        }
        let mut ty = [0.0; 3];
        let n = rem_pio2_large(&tx[..=i], &mut ty, ((ix as i32) >> 20) - (0x3ff + 23), 1);
        if sign != 0 {
            return (-n, -ty[0], -ty[1]);
        }
        (n, ty[0], ty[1])
    }
}
pub use rem_pio2::*;

mod sin {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/s_sin.c */
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunPro, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    // sin(x)
    // Return sine function of x.
    //
    // kernel function:
    //      k_sin            ... sine function on [-pi/4,pi/4]
    //      k_cos            ... cose function on [-pi/4,pi/4]
    //      rem_pio2         ... argument reduction routine
    //
    // Method.
    //      Let S,C and T denote the sin, cos and tan respectively on
    //      [-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2
    //      in [-pi/4 , +pi/4], and let n = k mod 4.
    //      We have
    //
    //          n        sin(x)      cos(x)        tan(x)
    //     ----------------------------------------------------------
    //          0          S           C             T
    //          1          C          -S            -1/T
    //          2         -S          -C             T
    //          3         -C           S            -1/T
    //     ----------------------------------------------------------
    //
    // Special cases:
    //      Let trig be any of sin, cos, or tan.
    //      trig(+-INF)  is NaN, with signals;
    //      trig(NaN)    is that NaN;
    //
    // Accuracy:
    //      TRIG(x) returns trig(x) nearly rounded

    /// The sine of `x` (f64).
    ///
    /// `x` is specified in radians.
    pub fn sin(x: f64) -> f64 {
        let x1p120 = f64::from_bits(0x4770000000000000); // 0x1p120f === 2 ^ 120

        /* High word of x. */
        let ix = (f64::to_bits(x) >> 32) as u32 & 0x7fffffff;

        /* |x| ~< pi/4 */
        if ix <= 0x3fe921fb {
            if ix < 0x3e500000 {
                /* |x| < 2**-26 */
                /* raise inexact if x != 0 and underflow if subnormal*/
                if ix < 0x00100000 {
                    let _ = x / x1p120;
                } else {
                    let _ = x + x1p120;
                }
                return x;
            }
            return k_sin(x, 0.0, 0);
        }

        if ix >= 0x7ff00000 {
            return x - x;
        }

        /* argument reduction needed */
        let (n, y0, y1) = rem_pio2(x);
        match n & 3 {
            0 => k_sin(y0, y1, 1),
            1 => k_cos(y0, y1),
            2 => -k_sin(y0, y1, 1),
            _ => -k_cos(y0, y1),
        }
    }
}
pub use sin::*;

mod cos {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/s_cos.c */
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunPro, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    // cos(x)
    // Return cosine function of x.
    //
    // kernel function:
    //      k_sin           ... sine function on [-pi/4,pi/4]
    //      k_cos           ... cosine function on [-pi/4,pi/4]
    //      rem_pio2        ... argument reduction routine
    //
    // Method.
    //      Let S,C and T denote the sin, cos and tan respectively on
    //      [-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2
    //      in [-pi/4 , +pi/4], and let n = k mod 4.
    //      We have
    //
    //          n        sin(x)      cos(x)        tan(x)
    //     ----------------------------------------------------------
    //          0          S           C             T
    //          1          C          -S            -1/T
    //          2         -S          -C             T
    //          3         -C           S            -1/T
    //     ----------------------------------------------------------
    //
    // Special cases:
    //      Let trig be any of sin, cos, or tan.
    //      trig(+-INF)  is NaN, with signals;
    //      trig(NaN)    is that NaN;
    //
    // Accuracy:
    //      TRIG(x) returns trig(x) nearly rounded
    //

    /// The cosine of `x` (f64).
    ///
    /// `x` is specified in radians.
    pub fn cos(x: f64) -> f64 {
        let ix = (f64::to_bits(x) >> 32) as u32 & 0x7fffffff;

        /* |x| ~< pi/4 */
        if ix <= 0x3fe921fb {
            if ix < 0x3e46a09e {
                /* if x < 2**-27 * sqrt(2) */
                /* raise inexact if x != 0 */
                if x as i32 == 0 {
                    return 1.0;
                }
            }
            return k_cos(x, 0.0);
        }

        if ix >= 0x7ff00000 {
            return x - x;
        }

        /* argument reduction needed */
        let (n, y0, y1) = rem_pio2(x);
        match n & 3 {
            0 => k_cos(y0, y1),
            1 => -k_sin(y0, y1, 1),
            2 => -k_cos(y0, y1),
            _ => k_sin(y0, y1, 1),
        }
    }
}
pub use cos::*;

mod tan {
    #![allow(unused_imports)]
    use super::*;

    // origin: FreeBSD /usr/src/lib/msun/src/s_tan.c */
    //
    // ====================================================
    // Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
    //
    // Developed at SunPro, a Sun Microsystems, Inc. business.
    // Permission to use, copy, modify, and distribute this
    // software is freely granted, provided that this notice
    // is preserved.
    // ====================================================

    // tan(x)
    // Return tangent function of x.
    //
    // kernel function:
    //      k_tan           ... tangent function on [-pi/4,pi/4]
    //      rem_pio2        ... argument reduction routine
    //
    // Method.
    //      Let S,C and T denote the sin, cos and tan respectively on
    //      [-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2
    //      in [-pi/4 , +pi/4], and let n = k mod 4.
    //      We have
    //
    //          n        sin(x)      cos(x)        tan(x)
    //     ----------------------------------------------------------
    //          0          S           C             T
    //          1          C          -S            -1/T
    //          2         -S          -C             T
    //          3         -C           S            -1/T
    //     ----------------------------------------------------------
    //
    // Special cases:
    //      Let trig be any of sin, cos, or tan.
    //      trig(+-INF)  is NaN, with signals;
    //      trig(NaN)    is that NaN;
    //
    // Accuracy:
    //      TRIG(x) returns trig(x) nearly rounded

    /// The tangent of `x` (f64).
    ///
    /// `x` is specified in radians.
    pub fn tan(x: f64) -> f64 {
        let x1p120 = f32::from_bits(0x7b800000); // 0x1p120f === 2 ^ 120

        let ix = (f64::to_bits(x) >> 32) as u32 & 0x7fffffff;
        /* |x| ~< pi/4 */
        if ix <= 0x3fe921fb {
            if ix < 0x3e400000 {
                /* |x| < 2**-27 */
                /* raise inexact if x!=0 and underflow if subnormal */
                let _ = if ix < 0x00100000 {
                    x / x1p120 as f64
                } else {
                    x + x1p120 as f64
                };
                return x;
            }
            return k_tan(x, 0.0, 0);
        }

        if ix >= 0x7ff00000 {
            return x - x;
        }

        /* argument reduction */
        let (n, y0, y1) = rem_pio2(x);
        k_tan(y0, y1, n & 1)
    }
}
pub use tan::*;

mod exp {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_exp.c */
    /*
     * ====================================================
     * Copyright (C) 2004 by Sun Microsystems, Inc. All rights reserved.
     *
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /* exp(x)
     * Returns the exponential of x.
     *
     * Method
     *   1. Argument reduction:
     *      Reduce x to an r so that |r| <= 0.5*ln2 ~ 0.34658.
     *      Given x, find r and integer k such that
     *
     *               x = k*ln2 + r,  |r| <= 0.5*ln2.
     *
     *      Here r will be represented as r = hi-lo for better
     *      accuracy.
     *
     *   2. Approximation of exp(r) by a special rational function on
     *      the interval [0,0.34658]:
     *      Write
     *          R(r**2) = r*(exp(r)+1)/(exp(r)-1) = 2 + r*r/6 - r**4/360 + ...
     *      We use a special Remez algorithm on [0,0.34658] to generate
     *      a polynomial of degree 5 to approximate R. The maximum error
     *      of this polynomial approximation is bounded by 2**-59. In
     *      other words,
     *          R(z) ~ 2.0 + P1*z + P2*z**2 + P3*z**3 + P4*z**4 + P5*z**5
     *      (where z=r*r, and the values of P1 to P5 are listed below)
     *      and
     *          |                  5          |     -59
     *          | 2.0+P1*z+...+P5*z   -  R(z) | <= 2
     *          |                             |
     *      The computation of exp(r) thus becomes
     *                              2*r
     *              exp(r) = 1 + ----------
     *                            R(r) - r
     *                                 r*c(r)
     *                     = 1 + r + ----------- (for better accuracy)
     *                                2 - c(r)
     *      where
     *                              2       4             10
     *              c(r) = r - (P1*r  + P2*r  + ... + P5*r   ).
     *
     *   3. Scale back to obtain exp(x):
     *      From step 1, we have
     *         exp(x) = 2^k * exp(r)
     *
     * Special cases:
     *      exp(INF) is INF, exp(NaN) is NaN;
     *      exp(-INF) is 0, and
     *      for finite argument, only exp(0)=1 is exact.
     *
     * Accuracy:
     *      according to an error analysis, the error is always less than
     *      1 ulp (unit in the last place).
     *
     * Misc. info.
     *      For IEEE double
     *          if x >  709.782712893383973096 then exp(x) overflows
     *          if x < -745.133219101941108420 then exp(x) underflows
     */

    const HALF: [f64; 2] = [0.5, -0.5];
    const LN2HI: f64 = 6.93147180369123816490e-01; /* 0x3fe62e42, 0xfee00000 */
    const LN2LO: f64 = 1.90821492927058770002e-10; /* 0x3dea39ef, 0x35793c76 */
    const INVLN2: f64 = 1.44269504088896338700e+00; /* 0x3ff71547, 0x652b82fe */
    const P1: f64 = 1.66666666666666019037e-01; /* 0x3FC55555, 0x5555553E */
    const P2: f64 = -2.77777777770155933842e-03; /* 0xBF66C16C, 0x16BEBD93 */
    const P3: f64 = 6.61375632143793436117e-05; /* 0x3F11566A, 0xAF25DE2C */
    const P4: f64 = -1.65339022054652515390e-06; /* 0xBEBBBD41, 0xC5D26BF1 */
    const P5: f64 = 4.13813679705723846039e-08; /* 0x3E663769, 0x72BEA4D0 */

    /// Exponential, base *e* (f64)
    ///
    /// Calculate the exponential of `x`, that is, *e* raised to the power `x`
    /// (where *e* is the base of the natural system of logarithms, approximately 2.71828).
    pub fn exp(mut x: f64) -> f64 {
        let x1p1023 = f64::from_bits(0x7fe0000000000000); // 0x1p1023 === 2 ^ 1023
        let x1p_149 = f64::from_bits(0x36a0000000000000); // 0x1p-149 === 2 ^ -149

        let hi: f64;
        let lo: f64;
        let c: f64;
        let xx: f64;
        let y: f64;
        let k: i32;
        let sign: i32;
        let mut hx: u32;

        hx = (x.to_bits() >> 32) as u32;
        sign = (hx >> 31) as i32;
        hx &= 0x7fffffff; /* high word of |x| */

        if hx >= 0x4086232b {
            /* if |x| >= 708.39... */
            if x.is_nan() {
                return x;
            }
            if x > 709.782712893383973096 {
                /* overflow if x!=inf */
                x *= x1p1023;
                return x;
            }
            if x < -708.39641853226410622 {
                /* underflow if x!=-inf */
                let _ = (-x1p_149 / x) as f32;
                if x < -745.13321910194110842 {
                    return 0.;
                }
            }
        }

        /* argument reduction */
        if hx > 0x3fd62e42 {
            /* if |x| > 0.5 ln2 */
            if hx >= 0x3ff0a2b2 {
                /* if |x| >= 1.5 ln2 */
                k = (INVLN2 * x + HALF[sign as usize]) as i32;
            } else {
                k = 1 - sign - sign;
            }
            hi = x - k as f64 * LN2HI; /* k*ln2hi is exact here */
            lo = k as f64 * LN2LO;
            x = hi - lo;
        } else if hx > 0x3e300000 {
            /* if |x| > 2**-28 */
            k = 0;
            hi = x;
            lo = 0.;
        } else {
            /* inexact if x!=0 */
            let _ = x1p1023 + x;
            return 1. + x;
        }

        /* x is now in primary range */
        xx = x * x;
        c = x - xx * (P1 + xx * (P2 + xx * (P3 + xx * (P4 + xx * P5))));
        y = 1. + (x * c / (2. - c) - lo + hi);
        if k == 0 { y } else { scalbn(y, k) }
    }
}
pub use exp::*;

mod expm1 {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/s_expm1.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunPro, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */

    const O_THRESHOLD: f64 = 7.09782712893383973096e+02; /* 0x40862E42, 0xFEFA39EF */
    const LN2_HI: f64 = 6.93147180369123816490e-01; /* 0x3fe62e42, 0xfee00000 */
    const LN2_LO: f64 = 1.90821492927058770002e-10; /* 0x3dea39ef, 0x35793c76 */
    const INVLN2: f64 = 1.44269504088896338700e+00; /* 0x3ff71547, 0x652b82fe */
    /* Scaled Q's: Qn_here = 2**n * Qn_above, for R(2*z) where z = hxs = x*x/2: */
    const Q1: f64 = -3.33333333333331316428e-02; /* BFA11111 111110F4 */
    const Q2: f64 = 1.58730158725481460165e-03; /* 3F5A01A0 19FE5585 */
    const Q3: f64 = -7.93650757867487942473e-05; /* BF14CE19 9EAADBB7 */
    const Q4: f64 = 4.00821782732936239552e-06; /* 3ED0CFCA 86E65239 */
    const Q5: f64 = -2.01099218183624371326e-07; /* BE8AFDB7 6E09C32D */

    /// Exponential, base *e*, of x-1 (f64)
    ///
    /// Calculates the exponential of `x` and subtract 1, that is, *e* raised
    /// to the power `x` minus 1 (where *e* is the base of the natural
    /// system of logarithms, approximately 2.71828).
    /// The result is accurate even for small values of `x`,
    /// where using `exp(x)-1` would lose many significant digits.
    pub fn expm1(mut x: f64) -> f64 {
        let hi: f64;
        let lo: f64;
        let k: i32;
        let c: f64;
        let mut t: f64;
        let mut y: f64;

        let mut ui = x.to_bits();
        let hx = ((ui >> 32) & 0x7fffffff) as u32;
        let sign = (ui >> 63) as i32;

        /* filter out huge and non-finite argument */
        if hx >= 0x4043687A {
            /* if |x|>=56*ln2 */
            if x.is_nan() {
                return x;
            }
            if sign != 0 {
                return -1.0;
            }
            if x > O_THRESHOLD {
                x *= f64::from_bits(0x7fe0000000000000);
                return x;
            }
        }

        /* argument reduction */
        if hx > 0x3fd62e42 {
            /* if  |x| > 0.5 ln2 */
            if hx < 0x3FF0A2B2 {
                /* and |x| < 1.5 ln2 */
                if sign == 0 {
                    hi = x - LN2_HI;
                    lo = LN2_LO;
                    k = 1;
                } else {
                    hi = x + LN2_HI;
                    lo = -LN2_LO;
                    k = -1;
                }
            } else {
                k = (INVLN2 * x + if sign != 0 { -0.5 } else { 0.5 }) as i32;
                t = k as f64;
                hi = x - t * LN2_HI; /* t*ln2_hi is exact here */
                lo = t * LN2_LO;
            }
            x = hi - lo;
            c = (hi - x) - lo;
        } else if hx < 0x3c900000 {
            /* |x| < 2**-54, return x */
            if hx < 0x00100000 {
                let _ = x;
            }
            return x;
        } else {
            c = 0.0;
            k = 0;
        }

        /* x is now in primary range */
        let hfx = 0.5 * x;
        let hxs = x * hfx;
        let r1 = 1.0 + hxs * (Q1 + hxs * (Q2 + hxs * (Q3 + hxs * (Q4 + hxs * Q5))));
        t = 3.0 - r1 * hfx;
        let mut e = hxs * ((r1 - t) / (6.0 - x * t));
        if k == 0 {
            return x - (x * e - hxs);
        }
        e = x * (e - c) - c;
        e -= hxs;
        /* exp(x) ~ 2^k (x_reduced - e + 1) */
        if k == -1 {
            return 0.5 * (x - e) - 0.5;
        }
        if k == 1 {
            if x < -0.25 {
                return -2.0 * (e - (x + 0.5));
            }
            return 1.0 + 2.0 * (x - e);
        }
        ui = ((0x3ff + k) as u64) << 52; /* 2^k */
        let twopk = f64::from_bits(ui);
        if k < 0 || k > 56 {
            /* suffice to return exp(x)-1 */
            y = x - e + 1.0;
            if k == 1024 {
                y = y * 2.0 * f64::from_bits(0x7fe0000000000000);
            } else {
                y = y * twopk;
            }
            return y - 1.0;
        }
        ui = ((0x3ff - k) as u64) << 52; /* 2^-k */
        let uf = f64::from_bits(ui);
        if k < 20 {
            y = (x - e + (1.0 - uf)) * twopk;
        } else {
            y = (x - (e + uf) + 1.0) * twopk;
        }
        y
    }
}
pub use expm1::*;

mod expo2 {
    #![allow(unused_imports)]
    use super::*;

    /* exp(x)/2 for x >= log(DBL_MAX), slightly better than 0.5*exp(x/2)*exp(x/2) */
    pub fn expo2(x: f64) -> f64 {
        /* k is such that k*ln2 has minimal relative error and x - kln2 > log(DBL_MIN) */
        const K: i32 = 2043;
        let kln2 = f64::from_bits(0x40962066151add8b);

        /* note that k is odd and scale*scale overflows */
        let scale = combine_words(((0x3ff + K / 2) as u32) << 20, 0);
        /* exp(x - k ln2) * 2**(k-1) */
        exp(x - kln2) * scale * scale
    }
}
pub use expo2::*;

mod k_expo2 {
    #![allow(unused_imports)]
    use super::*;

    /* k is such that k*ln2 has minimal relative error and x - kln2 > log(FLT_MIN) */
    const K: i32 = 2043;

    /* expf(x)/2 for x >= log(FLT_MAX), slightly better than 0.5f*expf(x/2)*expf(x/2) */
    pub fn k_expo2(x: f64) -> f64 {
        let k_ln2 = f64::from_bits(0x40962066151add8b);
        /* note that k is odd and scale*scale overflows */
        let scale = f64::from_bits(((((0x3ff + K / 2) as u32) << 20) as u64) << 32);
        /* exp(x - k ln2) * 2**(k-1) */
        exp(x - k_ln2) * scale * scale
    }
}
pub use k_expo2::*;

mod log {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_log.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /* log(x)
     * Return the logarithm of x
     *
     * Method :
     *   1. Argument Reduction: find k and f such that
     *                      x = 2^k * (1+f),
     *         where  sqrt(2)/2 < 1+f < sqrt(2) .
     *
     *   2. Approximation of log(1+f).
     *      Let s = f/(2+f) ; based on log(1+f) = log(1+s) - log(1-s)
     *               = 2s + 2/3 s**3 + 2/5 s**5 + .....,
     *               = 2s + s*R
     *      We use a special Remez algorithm on [0,0.1716] to generate
     *      a polynomial of degree 14 to approximate R The maximum error
     *      of this polynomial approximation is bounded by 2**-58.45. In
     *      other words,
     *                      2      4      6      8      10      12      14
     *          R(z) ~ Lg1*s +Lg2*s +Lg3*s +Lg4*s +Lg5*s  +Lg6*s  +Lg7*s
     *      (the values of Lg1 to Lg7 are listed in the program)
     *      and
     *          |      2          14          |     -58.45
     *          | Lg1*s +...+Lg7*s    -  R(z) | <= 2
     *          |                             |
     *      Note that 2s = f - s*f = f - hfsq + s*hfsq, where hfsq = f*f/2.
     *      In order to guarantee error in log below 1ulp, we compute log
     *      by
     *              log(1+f) = f - s*(f - R)        (if f is not too large)
     *              log(1+f) = f - (hfsq - s*(hfsq+R)).     (better accuracy)
     *
     *      3. Finally,  log(x) = k*ln2 + log(1+f).
     *                          = k*ln2_hi+(f-(hfsq-(s*(hfsq+R)+k*ln2_lo)))
     *         Here ln2 is split into two floating point number:
     *                      ln2_hi + ln2_lo,
     *         where n*ln2_hi is always exact for |n| < 2000.
     *
     * Special cases:
     *      log(x) is NaN with signal if x < 0 (including -INF) ;
     *      log(+INF) is +INF; log(0) is -INF with signal;
     *      log(NaN) is that NaN with no signal.
     *
     * Accuracy:
     *      according to an error analysis, the error is always less than
     *      1 ulp (unit in the last place).
     *
     * Constants:
     * The hexadecimal values are the intended ones for the following
     * constants. The decimal values may be used, provided that the
     * compiler will convert from decimal to binary accurately enough
     * to produce the hexadecimal values shown.
     */

    const LN2_HI: f64 = 6.93147180369123816490e-01; /* 3fe62e42 fee00000 */
    const LN2_LO: f64 = 1.90821492927058770002e-10; /* 3dea39ef 35793c76 */
    const LG1: f64 = 6.666666666666735130e-01; /* 3FE55555 55555593 */
    const LG2: f64 = 3.999999999940941908e-01; /* 3FD99999 9997FA04 */
    const LG3: f64 = 2.857142874366239149e-01; /* 3FD24924 94229359 */
    const LG4: f64 = 2.222219843214978396e-01; /* 3FCC71C5 1D8E78AF */
    const LG5: f64 = 1.818357216161805012e-01; /* 3FC74664 96CB03DE */
    const LG6: f64 = 1.531383769920937332e-01; /* 3FC39A09 D078C69F */
    const LG7: f64 = 1.479819860511658591e-01; /* 3FC2F112 DF3E5244 */

    pub fn log(mut x: f64) -> f64 {
        let x1p54 = f64::from_bits(0x4350000000000000); // 0x1p54 === 2 ^ 54

        let mut ui = x.to_bits();
        let mut hx: u32 = (ui >> 32) as u32;
        let mut k: i32 = 0;

        if (hx < 0x00100000) || ((hx >> 31) != 0) {
            /* x < 2**-126  */
            if ui << 1 == 0 {
                return -1. / (x * x); /* log(+-0)=-inf */
            }
            if hx >> 31 != 0 {
                return (x - x) / 0.0; /* log(-#) = NaN */
            }
            /* subnormal number, scale x up */
            k -= 54;
            x *= x1p54;
            ui = x.to_bits();
            hx = (ui >> 32) as u32;
        } else if hx >= 0x7ff00000 {
            return x;
        } else if hx == 0x3ff00000 && ui << 32 == 0 {
            return 0.;
        }

        /* reduce x into [sqrt(2)/2, sqrt(2)] */
        hx += 0x3ff00000 - 0x3fe6a09e;
        k += ((hx >> 20) as i32) - 0x3ff;
        hx = (hx & 0x000fffff) + 0x3fe6a09e;
        ui = ((hx as u64) << 32) | (ui & 0xffffffff);
        x = f64::from_bits(ui);

        let f: f64 = x - 1.0;
        let hfsq: f64 = 0.5 * f * f;
        let s: f64 = f / (2.0 + f);
        let z: f64 = s * s;
        let w: f64 = z * z;
        let t1: f64 = w * (LG2 + w * (LG4 + w * LG6));
        let t2: f64 = z * (LG1 + w * (LG3 + w * (LG5 + w * LG7)));
        let r: f64 = t2 + t1;
        let dk: f64 = k as f64;
        s * (hfsq + r) + dk * LN2_LO - hfsq + f + dk * LN2_HI
    }
}
pub use log::*;

mod log2 {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_log2.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /*
     * Return the base 2 logarithm of x.  See log.c for most comments.
     *
     * Reduce x to 2^k (1+f) and calculate r = log(1+f) - f + f*f/2
     * as in log.c, then combine and scale in extra precision:
     *    log2(x) = (f - f*f/2 + r)/log(2) + k
     */

    const IVLN2HI: f64 = 1.44269504072144627571e+00; /* 0x3ff71547, 0x65200000 */
    const IVLN2LO: f64 = 1.67517131648865118353e-10; /* 0x3de705fc, 0x2eefa200 */
    const LG1: f64 = 6.666666666666735130e-01; /* 3FE55555 55555593 */
    const LG2: f64 = 3.999999999940941908e-01; /* 3FD99999 9997FA04 */
    const LG3: f64 = 2.857142874366239149e-01; /* 3FD24924 94229359 */
    const LG4: f64 = 2.222219843214978396e-01; /* 3FCC71C5 1D8E78AF */
    const LG5: f64 = 1.818357216161805012e-01; /* 3FC74664 96CB03DE */
    const LG6: f64 = 1.531383769920937332e-01; /* 3FC39A09 D078C69F */
    const LG7: f64 = 1.479819860511658591e-01; /* 3FC2F112 DF3E5244 */

    pub fn log2(mut x: f64) -> f64 {
        let x1p54 = f64::from_bits(0x4350000000000000); // 0x1p54 === 2 ^ 54

        let mut ui: u64 = x.to_bits();
        let hfsq: f64;
        let f: f64;
        let s: f64;
        let z: f64;
        let r: f64;
        let mut w: f64;
        let t1: f64;
        let t2: f64;
        let y: f64;
        let mut hi: f64;
        let lo: f64;
        let mut val_hi: f64;
        let mut val_lo: f64;
        let mut hx: u32;
        let mut k: i32;

        hx = (ui >> 32) as u32;
        k = 0;
        if hx < 0x00100000 || (hx >> 31) > 0 {
            if ui << 1 == 0 {
                return -1. / (x * x); /* log(+-0)=-inf */
            }
            if (hx >> 31) > 0 {
                return (x - x) / 0.0; /* log(-#) = NaN */
            }
            /* subnormal number, scale x up */
            k -= 54;
            x *= x1p54;
            ui = x.to_bits();
            hx = (ui >> 32) as u32;
        } else if hx >= 0x7ff00000 {
            return x;
        } else if hx == 0x3ff00000 && ui << 32 == 0 {
            return 0.;
        }

        /* reduce x into [sqrt(2)/2, sqrt(2)] */
        hx += 0x3ff00000 - 0x3fe6a09e;
        k += (hx >> 20) as i32 - 0x3ff;
        hx = (hx & 0x000fffff) + 0x3fe6a09e;
        ui = (hx as u64) << 32 | (ui & 0xffffffff);
        x = f64::from_bits(ui);

        f = x - 1.0;
        hfsq = 0.5 * f * f;
        s = f / (2.0 + f);
        z = s * s;
        w = z * z;
        t1 = w * (LG2 + w * (LG4 + w * LG6));
        t2 = z * (LG1 + w * (LG3 + w * (LG5 + w * LG7)));
        r = t2 + t1;

        /* hi+lo = f - hfsq + s*(hfsq+R) ~ log(1+f) */
        hi = f - hfsq;
        ui = hi.to_bits();
        ui &= (-1i64 as u64) << 32;
        hi = f64::from_bits(ui);
        lo = f - hi - hfsq + s * (hfsq + r);

        val_hi = hi * IVLN2HI;
        val_lo = (lo + hi) * IVLN2LO + lo * IVLN2HI;

        /* spadd(val_hi, val_lo, y), except for not using double_t: */
        y = k.into();
        w = y + val_hi;
        val_lo += (y - w) + val_hi;
        val_hi = w;

        val_lo + val_hi
    }
}
pub use log2::*;

mod log10 {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_log10.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /*
     * Return the base 10 logarithm of x.  See log.c for most comments.
     *
     * Reduce x to 2^k (1+f) and calculate r = log(1+f) - f + f*f/2
     * as in log.c, then combine and scale in extra precision:
     *    log10(x) = (f - f*f/2 + r)/log(10) + k*log10(2)
     */

    const IVLN10HI: f64 = 4.34294481878168880939e-01; /* 0x3fdbcb7b, 0x15200000 */
    const IVLN10LO: f64 = 2.50829467116452752298e-11; /* 0x3dbb9438, 0xca9aadd5 */
    const LOG10_2HI: f64 = 3.01029995663611771306e-01; /* 0x3FD34413, 0x509F6000 */
    const LOG10_2LO: f64 = 3.69423907715893078616e-13; /* 0x3D59FEF3, 0x11F12B36 */
    const LG1: f64 = 6.666666666666735130e-01; /* 3FE55555 55555593 */
    const LG2: f64 = 3.999999999940941908e-01; /* 3FD99999 9997FA04 */
    const LG3: f64 = 2.857142874366239149e-01; /* 3FD24924 94229359 */
    const LG4: f64 = 2.222219843214978396e-01; /* 3FCC71C5 1D8E78AF */
    const LG5: f64 = 1.818357216161805012e-01; /* 3FC74664 96CB03DE */
    const LG6: f64 = 1.531383769920937332e-01; /* 3FC39A09 D078C69F */
    const LG7: f64 = 1.479819860511658591e-01; /* 3FC2F112 DF3E5244 */

    pub fn log10(mut x: f64) -> f64 {
        let x1p54 = f64::from_bits(0x4350000000000000); // 0x1p54 === 2 ^ 54

        let mut ui: u64 = x.to_bits();
        let hfsq: f64;
        let f: f64;
        let s: f64;
        let z: f64;
        let r: f64;
        let mut w: f64;
        let t1: f64;
        let t2: f64;
        let dk: f64;
        let y: f64;
        let mut hi: f64;
        let lo: f64;
        let mut val_hi: f64;
        let mut val_lo: f64;
        let mut hx: u32;
        let mut k: i32;

        hx = (ui >> 32) as u32;
        k = 0;
        if hx < 0x00100000 || (hx >> 31) > 0 {
            if ui << 1 == 0 {
                return -1. / (x * x); /* log(+-0)=-inf */
            }
            if (hx >> 31) > 0 {
                return (x - x) / 0.0; /* log(-#) = NaN */
            }
            /* subnormal number, scale x up */
            k -= 54;
            x *= x1p54;
            ui = x.to_bits();
            hx = (ui >> 32) as u32;
        } else if hx >= 0x7ff00000 {
            return x;
        } else if hx == 0x3ff00000 && ui << 32 == 0 {
            return 0.;
        }

        /* reduce x into [sqrt(2)/2, sqrt(2)] */
        hx += 0x3ff00000 - 0x3fe6a09e;
        k += (hx >> 20) as i32 - 0x3ff;
        hx = (hx & 0x000fffff) + 0x3fe6a09e;
        ui = (hx as u64) << 32 | (ui & 0xffffffff);
        x = f64::from_bits(ui);

        f = x - 1.0;
        hfsq = 0.5 * f * f;
        s = f / (2.0 + f);
        z = s * s;
        w = z * z;
        t1 = w * (LG2 + w * (LG4 + w * LG6));
        t2 = z * (LG1 + w * (LG3 + w * (LG5 + w * LG7)));
        r = t2 + t1;

        /* hi+lo = f - hfsq + s*(hfsq+R) ~ log(1+f) */
        hi = f - hfsq;
        ui = hi.to_bits();
        ui &= (-1i64 as u64) << 32;
        hi = f64::from_bits(ui);
        lo = f - hi - hfsq + s * (hfsq + r);

        /* val_hi+val_lo ~ log10(1+f) + k*log10(2) */
        val_hi = hi * IVLN10HI;
        dk = k as f64;
        y = dk * LOG10_2HI;
        val_lo = dk * LOG10_2LO + (lo + hi) * IVLN10LO + lo * IVLN10HI;

        /*
         * Extra precision in for adding y is not strictly needed
         * since there is no very large cancellation near x = sqrt(2) or
         * x = 1/sqrt(2), but we do it anyway since it costs little on CPUs
         * with some parallelism and it reduces the error for many args.
         */
        w = y + val_hi;
        val_lo += (y - w) + val_hi;
        val_hi = w;

        val_lo + val_hi
    }
}
pub use log10::*;

mod pow {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_pow.c */
    /*
     * ====================================================
     * Copyright (C) 2004 by Sun Microsystems, Inc. All rights reserved.
     *
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */

    // pow(x,y) return x**y
    //
    //                    n
    // Method:  Let x =  2   * (1+f)
    //      1. Compute and return log2(x) in two pieces:
    //              log2(x) = w1 + w2,
    //         where w1 has 53-24 = 29 bit trailing zeros.
    //      2. Perform y*log2(x) = n+y' by simulating multi-precision
    //         arithmetic, where |y'|<=0.5.
    //      3. Return x**y = 2**n*exp(y'*log2)
    //
    // Special cases:
    //      1.  (anything) ** 0  is 1
    //      2.  1 ** (anything)  is 1
    //      3.  (anything except 1) ** NAN is NAN
    //      4.  NAN ** (anything except 0) is NAN
    //      5.  +-(|x| > 1) **  +INF is +INF
    //      6.  +-(|x| > 1) **  -INF is +0
    //      7.  +-(|x| < 1) **  +INF is +0
    //      8.  +-(|x| < 1) **  -INF is +INF
    //      9.  -1          ** +-INF is 1
    //      10. +0 ** (+anything except 0, NAN)               is +0
    //      11. -0 ** (+anything except 0, NAN, odd integer)  is +0
    //      12. +0 ** (-anything except 0, NAN)               is +INF, raise divbyzero
    //      13. -0 ** (-anything except 0, NAN, odd integer)  is +INF, raise divbyzero
    //      14. -0 ** (+odd integer) is -0
    //      15. -0 ** (-odd integer) is -INF, raise divbyzero
    //      16. +INF ** (+anything except 0,NAN) is +INF
    //      17. +INF ** (-anything except 0,NAN) is +0
    //      18. -INF ** (+odd integer) is -INF
    //      19. -INF ** (anything) = -0 ** (-anything), (anything except odd integer)
    //      20. (anything) ** 1 is (anything)
    //      21. (anything) ** -1 is 1/(anything)
    //      22. (-anything) ** (integer) is (-1)**(integer)*(+anything**integer)
    //      23. (-anything except 0 and inf) ** (non-integer) is NAN
    //
    // Accuracy:
    //      pow(x,y) returns x**y nearly rounded. In particular
    //                      pow(integer,integer)
    //      always returns the correct integer provided it is
    //      representable.
    //
    // Constants :
    // The hexadecimal values are the intended ones for the following
    // constants. The decimal values may be used, provided that the
    // compiler will convert from decimal to binary accurately enough
    // to produce the hexadecimal values shown.
    //

    const BP: [f64; 2] = [1.0, 1.5];
    const DP_H: [f64; 2] = [0.0, 5.84962487220764160156e-01]; /* 0x3fe2b803_40000000 */
    const DP_L: [f64; 2] = [0.0, 1.35003920212974897128e-08]; /* 0x3E4CFDEB, 0x43CFD006 */
    const TWO53: f64 = 9007199254740992.0; /* 0x43400000_00000000 */
    const HUGE: f64 = 1.0e300;
    const TINY: f64 = 1.0e-300;

    // poly coefs for (3/2)*(log(x)-2s-2/3*s**3:
    const L1: f64 = 5.99999999999994648725e-01; /* 0x3fe33333_33333303 */
    const L2: f64 = 4.28571428578550184252e-01; /* 0x3fdb6db6_db6fabff */
    const L3: f64 = 3.33333329818377432918e-01; /* 0x3fd55555_518f264d */
    const L4: f64 = 2.72728123808534006489e-01; /* 0x3fd17460_a91d4101 */
    const L5: f64 = 2.30660745775561754067e-01; /* 0x3fcd864a_93c9db65 */
    const L6: f64 = 2.06975017800338417784e-01; /* 0x3fca7e28_4a454eef */
    const P1: f64 = 1.66666666666666019037e-01; /* 0x3fc55555_5555553e */
    const P2: f64 = -2.77777777770155933842e-03; /* 0xbf66c16c_16bebd93 */
    const P3: f64 = 6.61375632143793436117e-05; /* 0x3f11566a_af25de2c */
    const P4: f64 = -1.65339022054652515390e-06; /* 0xbebbbd41_c5d26bf1 */
    const P5: f64 = 4.13813679705723846039e-08; /* 0x3e663769_72bea4d0 */
    const LG2: f64 = 6.93147180559945286227e-01; /* 0x3fe62e42_fefa39ef */
    const LG2_H: f64 = 6.93147182464599609375e-01; /* 0x3fe62e43_00000000 */
    const LG2_L: f64 = -1.90465429995776804525e-09; /* 0xbe205c61_0ca86c39 */
    const OVT: f64 = 8.0085662595372944372e-017; /* -(1024-log2(ovfl+.5ulp)) */
    const CP: f64 = 9.61796693925975554329e-01; /* 0x3feec709_dc3a03fd =2/(3ln2) */
    const CP_H: f64 = 9.61796700954437255859e-01; /* 0x3feec709_e0000000 =(float)cp */
    const CP_L: f64 = -7.02846165095275826516e-09; /* 0xbe3e2fe0_145b01f5 =tail of cp_h*/
    const IVLN2: f64 = 1.44269504088896338700e+00; /* 0x3ff71547_652b82fe =1/ln2 */
    const IVLN2_H: f64 = 1.44269502162933349609e+00; /* 0x3ff71547_60000000 =24b 1/ln2*/
    const IVLN2_L: f64 = 1.92596299112661746887e-08; /* 0x3e54ae0b_f85ddf44 =1/ln2 tail*/

    pub fn pow(x: f64, y: f64) -> f64 {
        let t1: f64;
        let t2: f64;

        let (hx, lx): (i32, u32) = ((x.to_bits() >> 32) as i32, x.to_bits() as u32);
        let (hy, ly): (i32, u32) = ((y.to_bits() >> 32) as i32, y.to_bits() as u32);

        let mut ix: i32 = (hx & 0x7fffffff) as i32;
        let iy: i32 = (hy & 0x7fffffff) as i32;

        /* x**0 = 1, even if x is NaN */
        if ((iy as u32) | ly) == 0 {
            return 1.0;
        }

        /* 1**y = 1, even if y is NaN */
        if hx == 0x3ff00000 && lx == 0 {
            return 1.0;
        }

        /* NaN if either arg is NaN */
        if ix > 0x7ff00000
            || (ix == 0x7ff00000 && lx != 0)
            || iy > 0x7ff00000
            || (iy == 0x7ff00000 && ly != 0)
        {
            return x + y;
        }

        /* determine if y is an odd int when x < 0
         * yisint = 0       ... y is not an integer
         * yisint = 1       ... y is an odd int
         * yisint = 2       ... y is an even int
         */
        let mut yisint: i32 = 0;
        let mut k: i32;
        let mut j: i32;
        if hx < 0 {
            if iy >= 0x43400000 {
                yisint = 2; /* even integer y */
            } else if iy >= 0x3ff00000 {
                k = (iy >> 20) - 0x3ff; /* exponent */

                if k > 20 {
                    j = (ly >> (52 - k)) as i32;

                    if (j << (52 - k)) == (ly as i32) {
                        yisint = 2 - (j & 1);
                    }
                } else if ly == 0 {
                    j = iy >> (20 - k);

                    if (j << (20 - k)) == iy {
                        yisint = 2 - (j & 1);
                    }
                }
            }
        }

        if ly == 0 {
            if iy == 0x7ff00000 {
                return if ((ix - 0x3ff00000) | (lx as i32)) == 0 {
                    /* (-1)**+-inf is 1 */
                    1.0
                } else if ix >= 0x3ff00000 {
                    /* (|x|>1)**+-inf = inf,0 */
                    if hy >= 0 { y } else { 0.0 }
                } else {
                    /* (|x|<1)**+-inf = 0,inf */
                    if hy >= 0 { 0.0 } else { -y }
                };
            }

            if iy == 0x3ff00000 {
                return if hy >= 0 { x } else { 1.0 / x };
            }

            if hy == 0x40000000 {
                return x * x;
            }

            if hy == 0x3fe00000 {
                if hx >= 0 {
                    return sqrt(x);
                }
            }
        }

        let mut ax: f64 = fabs(x);
        if lx == 0 {
            if ix == 0x7ff00000 || ix == 0 || ix == 0x3ff00000 {
                let mut z: f64 = ax;

                if hy < 0 {
                    z = 1.0 / z;
                }

                if hx < 0 {
                    if ((ix - 0x3ff00000) | yisint) == 0 {
                        z = (z - z) / (z - z); /* (-1)**non-int is NaN */
                    } else if yisint == 1 {
                        z = -z; /* (x<0)**odd = -(|x|**odd) */
                    }
                }

                return z;
            }
        }

        let mut s: f64 = 1.0; /* sign of result */
        if hx < 0 {
            if yisint == 0 {
                /* (x<0)**(non-int) is NaN */
                return (x - x) / (x - x);
            }

            if yisint == 1 {
                /* (x<0)**(odd int) */
                s = -1.0;
            }
        }

        if iy > 0x41e00000 {
            if iy > 0x43f00000 {
                /* if |y| > 2**64, must o/uflow */
                if ix <= 0x3fefffff {
                    return if hy < 0 { HUGE * HUGE } else { TINY * TINY };
                }

                if ix >= 0x3ff00000 {
                    return if hy > 0 { HUGE * HUGE } else { TINY * TINY };
                }
            }

            /* over/underflow if x is not close to one */
            if ix < 0x3fefffff {
                return if hy < 0 {
                    s * HUGE * HUGE
                } else {
                    s * TINY * TINY
                };
            }
            if ix > 0x3ff00000 {
                return if hy > 0 {
                    s * HUGE * HUGE
                } else {
                    s * TINY * TINY
                };
            }

            /* now |1-x| is TINY <= 2**-20, suffice to compute
            log(x) by x-x^2/2+x^3/3-x^4/4 */
            let t: f64 = ax - 1.0; /* t has 20 trailing zeros */
            let w: f64 = (t * t) * (0.5 - t * (0.3333333333333333333333 - t * 0.25));
            let u: f64 = IVLN2_H * t; /* ivln2_h has 21 sig. bits */
            let v: f64 = t * IVLN2_L - w * IVLN2;
            t1 = with_set_low_word(u + v, 0);
            t2 = v - (t1 - u);
        } else {
            let mut n: i32 = 0;

            if ix < 0x00100000 {
                ax *= TWO53;
                n -= 53;
                ix = get_high_word(ax) as i32;
            }

            n += (ix >> 20) - 0x3ff;
            j = ix & 0x000fffff;

            let k: i32;
            ix = j | 0x3ff00000; /* normalize ix */
            if j <= 0x3988E {
                k = 0;
            } else if j < 0xBB67A {
                k = 1;
            } else {
                k = 0;
                n += 1;
                ix -= 0x00100000;
            }
            ax = with_set_high_word(ax, ix as u32);

            /* compute ss = s_h+s_l = (x-1)/(x+1) or (x-1.5)/(x+1.5) */
            let u: f64 = ax - BP[k as usize]; /* bp[0]=1.0, bp[1]=1.5 */
            let v: f64 = 1.0 / (ax + BP[k as usize]);
            let ss: f64 = u * v;
            let s_h = with_set_low_word(ss, 0);

            let t_h: f64 = with_set_high_word(
                0.0,
                ((ix as u32 >> 1) | 0x20000000) + 0x00080000 + ((k as u32) << 18),
            );
            let t_l: f64 = ax - (t_h - BP[k as usize]);
            let s_l: f64 = v * ((u - s_h * t_h) - s_h * t_l);

            let s2: f64 = ss * ss;
            let mut r: f64 =
                s2 * s2 * (L1 + s2 * (L2 + s2 * (L3 + s2 * (L4 + s2 * (L5 + s2 * L6)))));
            r += s_l * (s_h + ss);
            let s2: f64 = s_h * s_h;
            let t_h: f64 = with_set_low_word(3.0 + s2 + r, 0);
            let t_l: f64 = r - ((t_h - 3.0) - s2);

            /* u+v = ss*(1+...) */
            let u: f64 = s_h * t_h;
            let v: f64 = s_l * t_h + t_l * ss;

            /* 2/(3log2)*(ss+...) */
            let p_h: f64 = with_set_low_word(u + v, 0);
            let p_l = v - (p_h - u);
            let z_h: f64 = CP_H * p_h; /* cp_h+cp_l = 2/(3*log2) */
            let z_l: f64 = CP_L * p_h + p_l * CP + DP_L[k as usize];

            /* log2(ax) = (ss+..)*2/(3*log2) = n + dp_h + z_h + z_l */
            let t: f64 = n as f64;
            t1 = with_set_low_word(((z_h + z_l) + DP_H[k as usize]) + t, 0);
            t2 = z_l - (((t1 - t) - DP_H[k as usize]) - z_h);
        }

        /* split up y into y1+y2 and compute (y1+y2)*(t1+t2) */
        let y1: f64 = with_set_low_word(y, 0);
        let p_l: f64 = (y - y1) * t1 + y * t2;
        let mut p_h: f64 = y1 * t1;
        let z: f64 = p_l + p_h;
        let mut j: i32 = (z.to_bits() >> 32) as i32;
        let i: i32 = z.to_bits() as i32;

        if j >= 0x40900000 {
            if (j - 0x40900000) | i != 0 {
                return s * HUGE * HUGE; /* overflow */
            }

            if p_l + OVT > z - p_h {
                return s * HUGE * HUGE; /* overflow */
            }
        } else if (j & 0x7fffffff) >= 0x4090cc00 {
            if (((j as u32) - 0xc090cc00) | (i as u32)) != 0 {
                return s * TINY * TINY; /* underflow */
            }

            if p_l <= z - p_h {
                return s * TINY * TINY; /* underflow */
            }
        }

        let i: i32 = j & (0x7fffffff as i32);
        k = (i >> 20) - 0x3ff;
        let mut n: i32 = 0;

        if i > 0x3fe00000 {
            /* if |z| > 0.5, set n = [z+0.5] */
            n = j + (0x00100000 >> (k + 1));
            k = ((n & 0x7fffffff) >> 20) - 0x3ff; /* new k for n */
            let t: f64 = with_set_high_word(0.0, (n & !(0x000fffff >> k)) as u32);
            n = ((n & 0x000fffff) | 0x00100000) >> (20 - k);
            if j < 0 {
                n = -n;
            }
            p_h -= t;
        }

        let t: f64 = with_set_low_word(p_l + p_h, 0);
        let u: f64 = t * LG2_H;
        let v: f64 = (p_l - (t - p_h)) * LG2 + t * LG2_L;
        let mut z: f64 = u + v;
        let w: f64 = v - (z - u);
        let t: f64 = z * z;
        let t1: f64 = z - t * (P1 + t * (P2 + t * (P3 + t * (P4 + t * P5))));
        let r: f64 = (z * t1) / (t1 - 2.0) - (w + z * w);
        z = 1.0 - (r - z);
        j = get_high_word(z) as i32;
        j += n << 20;

        if (j >> 20) <= 0 {
            z = scalbn(z, n);
        } else {
            z = with_set_high_word(z, j as u32);
        }

        s * z
    }
}
pub use pow::*;

mod cbrt {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/s_cbrt.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunPro, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     *
     * Optimized by Bruce D. Evans.
     */

    const B1: u32 = 715094163; /* B1 = (1023-1023/3-0.03306235651)*2**20 */
    const B2: u32 = 696219795; /* B2 = (1023-1023/3-54/3-0.03306235651)*2**20 */

    /* |1/cbrt(x) - p(x)| < 2**-23.5 (~[-7.93e-8, 7.929e-8]). */
    const P0: f64 = 1.87595182427177009643; /* 0x3ffe03e6, 0x0f61e692 */
    const P1: f64 = -1.88497979543377169875; /* 0xbffe28e0, 0x92f02420 */
    const P2: f64 = 1.621429720105354466140; /* 0x3ff9f160, 0x4a49d6c2 */
    const P3: f64 = -0.758397934778766047437; /* 0xbfe844cb, 0xbee751d9 */
    const P4: f64 = 0.145996192886612446982; /* 0x3fc2b000, 0xd4e4edd7 */

    pub fn cbrt(x: f64) -> f64 {
        let x1p54 = f64::from_bits(0x4350000000000000); // 0x1p54 === 2 ^ 54

        let mut ui: u64 = x.to_bits();
        let mut r: f64;
        let s: f64;
        let mut t: f64;
        let w: f64;
        let mut hx: u32 = (ui >> 32) as u32 & 0x7fffffff;

        if hx >= 0x7ff00000 {
            /* cbrt(NaN,INF) is itself */
            return x + x;
        }

        /*
         * Rough cbrt to 5 bits:
         *    cbrt(2**e*(1+m) ~= 2**(e/3)*(1+(e%3+m)/3)
         * where e is integral and >= 0, m is real and in [0, 1), and "/" and
         * "%" are integer division and modulus with rounding towards minus
         * infinity.  The RHS is always >= the LHS and has a maximum relative
         * error of about 1 in 16.  Adding a bias of -0.03306235651 to the
         * (e%3+m)/3 term reduces the error to about 1 in 32. With the IEEE
         * floating point representation, for finite positive normal values,
         * ordinary integer divison of the value in bits magically gives
         * almost exactly the RHS of the above provided we first subtract the
         * exponent bias (1023 for doubles) and later add it back.  We do the
         * subtraction virtually to keep e >= 0 so that ordinary integer
         * division rounds towards minus infinity; this is also efficient.
         */
        if hx < 0x00100000 {
            ui = (x * x1p54).to_bits();
            hx = (ui >> 32) as u32 & 0x7fffffff;
            if hx == 0 {
                return x; /* cbrt(0) is itself */
            }
            hx = hx / 3 + B2;
        } else {
            hx = hx / 3 + B1;
        }
        ui &= 1 << 63;
        ui |= (hx as u64) << 32;
        t = f64::from_bits(ui);

        /*
         * New cbrt to 23 bits:
         *    cbrt(x) = t*cbrt(x/t**3) ~= t*P(t**3/x)
         * where P(r) is a polynomial of degree 4 that approximates 1/cbrt(r)
         * to within 2**-23.5 when |r - 1| < 1/10.  The rough approximation
         * has produced t such than |t/cbrt(x) - 1| ~< 1/32, and cubing this
         * gives us bounds for r = t**3/x.
         *
         * Try to optimize for parallel evaluation as in __tanf.c.
         */
        r = (t * t) * (t / x);
        t = t * ((P0 + r * (P1 + r * P2)) + ((r * r) * r) * (P3 + r * P4));

        /*
         * Round t away from zero to 23 bits (sloppily except for ensuring that
         * the result is larger in magnitude than cbrt(x) but not much more than
         * 2 23-bit ulps larger).  With rounding towards zero, the error bound
         * would be ~5/6 instead of ~4/6.  With a maximum error of 2 23-bit ulps
         * in the rounded t, the infinite-precision error in the Newton
         * approximation barely affects third digit in the final error
         * 0.667; the error in the rounded t can be up to about 3 23-bit ulps
         * before the final error is larger than 0.667 ulps.
         */
        ui = t.to_bits();
        ui = (ui + 0x80000000) & 0xffffffffc0000000;
        t = f64::from_bits(ui);

        /* one step Newton iteration to 53 bits with error < 0.667 ulps */
        s = t * t; /* t*t is exact */
        r = x / s; /* error <= 0.5 ulps; |r| < |t| */
        w = t + t; /* t+t is exact */
        r = (r - t) / (w + r); /* r-t is exact; w+r ~= 3*t */
        t = t + t * r; /* error <= 0.5 + 0.5/3 + epsilon */
        t
    }
}
pub use cbrt::*;

mod atan {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/s_atan.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunPro, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /* atan(x)
     * Method
     *   1. Reduce x to positive by atan(x) = -atan(-x).
     *   2. According to the integer k=4t+0.25 chopped, t=x, the argument
     *      is further reduced to one of the following intervals and the
     *      arctangent of t is evaluated by the corresponding formula:
     *
     *      [0,7/16]      atan(x) = t-t^3*(a1+t^2*(a2+...(a10+t^2*a11)...)
     *      [7/16,11/16]  atan(x) = atan(1/2) + atan( (t-0.5)/(1+t/2) )
     *      [11/16.19/16] atan(x) = atan( 1 ) + atan( (t-1)/(1+t) )
     *      [19/16,39/16] atan(x) = atan(3/2) + atan( (t-1.5)/(1+1.5t) )
     *      [39/16,INF]   atan(x) = atan(INF) + atan( -1/t )
     *
     * Constants:
     * The hexadecimal values are the intended ones for the following
     * constants. The decimal values may be used, provided that the
     * compiler will convert from decimal to binary accurately enough
     * to produce the hexadecimal values shown.
     */

    const ATANHI: [f64; 4] = [
        4.63647609000806093515e-01, /* atan(0.5)hi 0x3FDDAC67, 0x0561BB4F */
        7.85398163397448278999e-01, /* atan(1.0)hi 0x3FE921FB, 0x54442D18 */
        9.82793723247329054082e-01, /* atan(1.5)hi 0x3FEF730B, 0xD281F69B */
        1.57079632679489655800e+00, /* atan(inf)hi 0x3FF921FB, 0x54442D18 */
    ];

    const ATANLO: [f64; 4] = [
        2.26987774529616870924e-17, /* atan(0.5)lo 0x3C7A2B7F, 0x222F65E2 */
        3.06161699786838301793e-17, /* atan(1.0)lo 0x3C81A626, 0x33145C07 */
        1.39033110312309984516e-17, /* atan(1.5)lo 0x3C700788, 0x7AF0CBBD */
        6.12323399573676603587e-17, /* atan(inf)lo 0x3C91A626, 0x33145C07 */
    ];

    const AT: [f64; 11] = [
        3.33333333333329318027e-01,  /* 0x3FD55555, 0x5555550D */
        -1.99999999998764832476e-01, /* 0xBFC99999, 0x9998EBC4 */
        1.42857142725034663711e-01,  /* 0x3FC24924, 0x920083FF */
        -1.11111104054623557880e-01, /* 0xBFBC71C6, 0xFE231671 */
        9.09088713343650656196e-02,  /* 0x3FB745CD, 0xC54C206E */
        -7.69187620504482999495e-02, /* 0xBFB3B0F2, 0xAF749A6D */
        6.66107313738753120669e-02,  /* 0x3FB10D66, 0xA0D03D51 */
        -5.83357013379057348645e-02, /* 0xBFADDE2D, 0x52DEFD9A */
        4.97687799461593236017e-02,  /* 0x3FA97B4B, 0x24760DEB */
        -3.65315727442169155270e-02, /* 0xBFA2B444, 0x2C6A6C2F */
        1.62858201153657823623e-02,  /* 0x3F90AD3A, 0xE322DA11 */
    ];

    /// Arctangent (f64)
    ///
    /// Computes the inverse tangent (arc tangent) of the input value.
    /// Returns a value in radians, in the range of -pi/2 to pi/2.
    pub fn atan(x: f64) -> f64 {
        let mut x = x;
        let mut ix = (x.to_bits() >> 32) as u32;
        let sign = ix >> 31;
        ix &= 0x7fff_ffff;
        if ix >= 0x4410_0000 {
            if x.is_nan() {
                return x;
            }

            let z = ATANHI[3] + f64::from_bits(0x0380_0000); // 0x1p-120f
            return if sign != 0 { -z } else { z };
        }

        let id = if ix < 0x3fdc_0000 {
            if ix < 0x3e40_0000 {
                if ix < 0x0010_0000 {
                    /* raise underflow for subnormal x */
                    let _ = x as f32;
                }

                return x;
            }

            -1
        } else {
            x = fabs(x);
            if ix < 0x3ff30000 {
                if ix < 0x3fe60000 {
                    x = (2. * x - 1.) / (2. + x);
                    0
                } else {
                    x = (x - 1.) / (x + 1.);
                    1
                }
            } else if ix < 0x40038000 {
                x = (x - 1.5) / (1. + 1.5 * x);
                2
            } else {
                x = -1. / x;
                3
            }
        };

        let z = x * x;
        let w = z * z;
        /* break sum from i=0 to 10 AT[i]z**(i+1) into odd and even poly */
        let s1 = z * (AT[0] + w * (AT[2] + w * (AT[4] + w * (AT[6] + w * (AT[8] + w * AT[10])))));
        let s2 = w * (AT[1] + w * (AT[3] + w * (AT[5] + w * (AT[7] + w * AT[9]))));

        if id < 0 {
            return x - x * (s1 + s2);
        }

        let z = ATANHI[id as usize] - (x * (s1 + s2) - ATANLO[id as usize] - x);

        if sign != 0 { -z } else { z }
    }
}
pub use atan::*;

mod atan2 {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_atan2.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     *
     */
    /* atan2(y,x)
     * Method :
     *      1. Reduce y to positive by atan2(y,x)=-atan2(-y,x).
     *      2. Reduce x to positive by (if x and y are unexceptional):
     *              ARG (x+iy) = arctan(y/x)           ... if x > 0,
     *              ARG (x+iy) = pi - arctan[y/(-x)]   ... if x < 0,
     *
     * Special cases:
     *
     *      ATAN2((anything), NaN ) is NaN;
     *      ATAN2(NAN , (anything) ) is NaN;
     *      ATAN2(+-0, +(anything but NaN)) is +-0  ;
     *      ATAN2(+-0, -(anything but NaN)) is +-pi ;
     *      ATAN2(+-(anything but 0 and NaN), 0) is +-pi/2;
     *      ATAN2(+-(anything but INF and NaN), +INF) is +-0 ;
     *      ATAN2(+-(anything but INF and NaN), -INF) is +-pi;
     *      ATAN2(+-INF,+INF ) is +-pi/4 ;
     *      ATAN2(+-INF,-INF ) is +-3pi/4;
     *      ATAN2(+-INF, (anything but,0,NaN, and INF)) is +-pi/2;
     *
     * Constants:
     * The hexadecimal values are the intended ones for the following
     * constants. The decimal values may be used, provided that the
     * compiler will convert from decimal to binary accurately enough
     * to produce the hexadecimal values shown.
     */

    const PI: f64 = 3.1415926535897931160E+00; /* 0x400921FB, 0x54442D18 */
    const PI_LO: f64 = 1.2246467991473531772E-16; /* 0x3CA1A626, 0x33145C07 */

    /// Arctangent of y/x (f64)
    ///
    /// Computes the inverse tangent (arc tangent) of `y/x`.
    /// Produces the correct result even for angles near pi/2 or -pi/2 (that is, when `x` is near 0).
    /// Returns a value in radians, in the range of -pi to pi.
    pub fn atan2(y: f64, x: f64) -> f64 {
        if x.is_nan() || y.is_nan() {
            return x + y;
        }
        let mut ix = (x.to_bits() >> 32) as u32;
        let lx = x.to_bits() as u32;
        let mut iy = (y.to_bits() >> 32) as u32;
        let ly = y.to_bits() as u32;
        if ((ix.wrapping_sub(0x3ff00000)) | lx) == 0 {
            return atan(y);
        }
        let m = ((iy >> 31) & 1) | ((ix >> 30) & 2); /* 2*sign(x)+sign(y) */
        ix &= 0x7fffffff;
        iy &= 0x7fffffff;

        if (iy | ly) == 0 {
            return match m {
                0 | 1 => y, /* atan(+-0,+anything)=+-0 */
                2 => PI,    /* atan(+0,-anything) = PI */
                _ => -PI,   /* atan(-0,-anything) =-PI */
            };
        }
        if (ix | lx) == 0 {
            return if m & 1 != 0 { -PI / 2.0 } else { PI / 2.0 };
        }
        if ix == 0x7ff00000 {
            if iy == 0x7ff00000 {
                return match m {
                    0 => PI / 4.0,        /* atan(+INF,+INF) */
                    1 => -PI / 4.0,       /* atan(-INF,+INF) */
                    2 => 3.0 * PI / 4.0,  /* atan(+INF,-INF) */
                    _ => -3.0 * PI / 4.0, /* atan(-INF,-INF) */
                };
            } else {
                return match m {
                    0 => 0.0,  /* atan(+...,+INF) */
                    1 => -0.0, /* atan(-...,+INF) */
                    2 => PI,   /* atan(+...,-INF) */
                    _ => -PI,  /* atan(-...,-INF) */
                };
            }
        }
        if ix.wrapping_add(64 << 20) < iy || iy == 0x7ff00000 {
            return if m & 1 != 0 { -PI / 2.0 } else { PI / 2.0 };
        }

        /* z = atan(|y/x|) without spurious underflow */
        let z = if (m & 2 != 0) && iy.wrapping_add(64 << 20) < ix {
            0.0
        } else {
            atan(fabs(y / x))
        };
        match m {
            0 => z,                /* atan(+,+) */
            1 => -z,               /* atan(-,+) */
            2 => PI - (z - PI_LO), /* atan(+,-) */
            _ => (z - PI_LO) - PI, /* atan(-,-) */
        }
    }
}
pub use atan2::*;

mod asin {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_asin.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /* asin(x)
     * Method :
     *      Since  asin(x) = x + x^3/6 + x^5*3/40 + x^7*15/336 + ...
     *      we approximate asin(x) on [0,0.5] by
     *              asin(x) = x + x*x^2*R(x^2)
     *      where
     *              R(x^2) is a rational approximation of (asin(x)-x)/x^3
     *      and its remez error is bounded by
     *              |(asin(x)-x)/x^3 - R(x^2)| < 2^(-58.75)
     *
     *      For x in [0.5,1]
     *              asin(x) = pi/2-2*asin(sqrt((1-x)/2))
     *      Let y = (1-x), z = y/2, s := sqrt(z), and pio2_hi+pio2_lo=pi/2;
     *      then for x>0.98
     *              asin(x) = pi/2 - 2*(s+s*z*R(z))
     *                      = pio2_hi - (2*(s+s*z*R(z)) - pio2_lo)
     *      For x<=0.98, let pio4_hi = pio2_hi/2, then
     *              f = hi part of s;
     *              c = sqrt(z) - f = (z-f*f)/(s+f)         ...f+c=sqrt(z)
     *      and
     *              asin(x) = pi/2 - 2*(s+s*z*R(z))
     *                      = pio4_hi+(pio4-2s)-(2s*z*R(z)-pio2_lo)
     *                      = pio4_hi+(pio4-2f)-(2s*z*R(z)-(pio2_lo+2c))
     *
     * Special cases:
     *      if x is NaN, return x itself;
     *      if |x|>1, return NaN with invalid signal.
     *
     */

    const PIO2_HI: f64 = 1.57079632679489655800e+00; /* 0x3FF921FB, 0x54442D18 */
    const PIO2_LO: f64 = 6.12323399573676603587e-17; /* 0x3C91A626, 0x33145C07 */
    /* coefficients for R(x^2) */
    const P_S0: f64 = 1.66666666666666657415e-01; /* 0x3FC55555, 0x55555555 */
    const P_S1: f64 = -3.25565818622400915405e-01; /* 0xBFD4D612, 0x03EB6F7D */
    const P_S2: f64 = 2.01212532134862925881e-01; /* 0x3FC9C155, 0x0E884455 */
    const P_S3: f64 = -4.00555345006794114027e-02; /* 0xBFA48228, 0xB5688F3B */
    const P_S4: f64 = 7.91534994289814532176e-04; /* 0x3F49EFE0, 0x7501B288 */
    const P_S5: f64 = 3.47933107596021167570e-05; /* 0x3F023DE1, 0x0DFDF709 */
    const Q_S1: f64 = -2.40339491173441421878e+00; /* 0xC0033A27, 0x1C8A2D4B */
    const Q_S2: f64 = 2.02094576023350569471e+00; /* 0x40002AE5, 0x9C598AC8 */
    const Q_S3: f64 = -6.88283971605453293030e-01; /* 0xBFE6066C, 0x1B8D0159 */
    const Q_S4: f64 = 7.70381505559019352791e-02; /* 0x3FB3B8C5, 0xB12E9282 */

    pub fn comp_r(z: f64) -> f64 {
        let p = z * (P_S0 + z * (P_S1 + z * (P_S2 + z * (P_S3 + z * (P_S4 + z * P_S5)))));
        let q = 1.0 + z * (Q_S1 + z * (Q_S2 + z * (Q_S3 + z * Q_S4)));
        p / q
    }

    /// Arcsine (f64)
    ///
    /// Computes the inverse sine (arc sine) of the argument `x`.
    /// Arguments to asin must be in the range -1 to 1.
    /// Returns values in radians, in the range of -pi/2 to pi/2.
    pub fn asin(mut x: f64) -> f64 {
        let z: f64;
        let r: f64;
        let s: f64;
        let hx: u32;
        let ix: u32;

        hx = get_high_word(x);
        ix = hx & 0x7fffffff;
        /* |x| >= 1 or nan */
        if ix >= 0x3ff00000 {
            let lx: u32;
            lx = get_low_word(x);
            if ((ix - 0x3ff00000) | lx) == 0 {
                /* asin(1) = +-pi/2 with inexact */
                return x * PIO2_HI + f64::from_bits(0x3870000000000000);
            } else {
                return 0.0 / (x - x);
            }
        }
        /* |x| < 0.5 */
        if ix < 0x3fe00000 {
            /* if 0x1p-1022 <= |x| < 0x1p-26, avoid raising underflow */
            if ix < 0x3e500000 && ix >= 0x00100000 {
                return x;
            } else {
                return x + x * comp_r(x * x);
            }
        }
        z = (1.0 - fabs(x)) * 0.5;
        s = sqrt(z);
        r = comp_r(z);
        if ix >= 0x3fef3333 {
            x = PIO2_HI - (2. * (s + s * r) - PIO2_LO);
        } else {
            let f: f64;
            let c: f64;
            /* f+c = sqrt(z) */
            f = with_set_low_word(s, 0);
            c = (z - f * f) / (s + f);
            x = 0.5 * PIO2_HI - (2.0 * s * r - (PIO2_LO - 2.0 * c) - (0.5 * PIO2_HI - 2.0 * f));
        }
        if hx >> 31 != 0 { -x } else { x }
    }
}
pub use asin::*;

mod acos {
    #![allow(unused_imports)]
    use super::*;

    /* origin: FreeBSD /usr/src/lib/msun/src/e_acos.c */
    /*
     * ====================================================
     * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
     *
     * Developed at SunSoft, a Sun Microsystems, Inc. business.
     * Permission to use, copy, modify, and distribute this
     * software is freely granted, provided that this notice
     * is preserved.
     * ====================================================
     */
    /* acos(x)
     * Method :
     *      acos(x)  = pi/2 - asin(x)
     *      acos(-x) = pi/2 + asin(x)
     * For |x|<=0.5
     *      acos(x) = pi/2 - (x + x*x^2*R(x^2))     (see asin.c)
     * For x>0.5
     *      acos(x) = pi/2 - (pi/2 - 2asin(sqrt((1-x)/2)))
     *              = 2asin(sqrt((1-x)/2))
     *              = 2s + 2s*z*R(z)        ...z=(1-x)/2, s=sqrt(z)
     *              = 2f + (2c + 2s*z*R(z))
     *     where f=hi part of s, and c = (z-f*f)/(s+f) is the correction term
     *     for f so that f+c ~ sqrt(z).
     * For x<-0.5
     *      acos(x) = pi - 2asin(sqrt((1-|x|)/2))
     *              = pi - 0.5*(s+s*z*R(z)), where z=(1-|x|)/2,s=sqrt(z)
     *
     * Special cases:
     *      if x is NaN, return x itself;
     *      if |x|>1, return NaN with invalid signal.
     *
     * Function needed: sqrt
     */

    const PIO2_HI: f64 = 1.57079632679489655800e+00; /* 0x3FF921FB, 0x54442D18 */
    const PIO2_LO: f64 = 6.12323399573676603587e-17; /* 0x3C91A626, 0x33145C07 */
    const PS0: f64 = 1.66666666666666657415e-01; /* 0x3FC55555, 0x55555555 */
    const PS1: f64 = -3.25565818622400915405e-01; /* 0xBFD4D612, 0x03EB6F7D */
    const PS2: f64 = 2.01212532134862925881e-01; /* 0x3FC9C155, 0x0E884455 */
    const PS3: f64 = -4.00555345006794114027e-02; /* 0xBFA48228, 0xB5688F3B */
    const PS4: f64 = 7.91534994289814532176e-04; /* 0x3F49EFE0, 0x7501B288 */
    const PS5: f64 = 3.47933107596021167570e-05; /* 0x3F023DE1, 0x0DFDF709 */
    const QS1: f64 = -2.40339491173441421878e+00; /* 0xC0033A27, 0x1C8A2D4B */
    const QS2: f64 = 2.02094576023350569471e+00; /* 0x40002AE5, 0x9C598AC8 */
    const QS3: f64 = -6.88283971605453293030e-01; /* 0xBFE6066C, 0x1B8D0159 */
    const QS4: f64 = 7.70381505559019352791e-02; /* 0x3FB3B8C5, 0xB12E9282 */

    pub fn r(z: f64) -> f64 {
        let p: f64 = z * (PS0 + z * (PS1 + z * (PS2 + z * (PS3 + z * (PS4 + z * PS5)))));
        let q: f64 = 1.0 + z * (QS1 + z * (QS2 + z * (QS3 + z * QS4)));
        p / q
    }

    /// Arccosine (f64)
    ///
    /// Computes the inverse cosine (arc cosine) of the input value.
    /// Arguments must be in the range -1 to 1.
    /// Returns values in radians, in the range of 0 to pi.
    pub fn acos(x: f64) -> f64 {
        let x1p_120f = f64::from_bits(0x3870000000000000); // 0x1p-120 === 2 ^ -120
        let z: f64;
        let w: f64;
        let s: f64;
        let c: f64;
        let df: f64;
        let hx: u32;
        let ix: u32;

        hx = (x.to_bits() >> 32) as u32;
        ix = hx & 0x7fffffff;
        /* |x| >= 1 or nan */
        if ix >= 0x3ff00000 {
            let lx: u32 = x.to_bits() as u32;

            if ((ix - 0x3ff00000) | lx) == 0 {
                /* acos(1)=0, acos(-1)=pi */
                if (hx >> 31) != 0 {
                    return 2. * PIO2_HI + x1p_120f;
                }
                return 0.;
            }
            return 0. / (x - x);
        }
        /* |x| < 0.5 */
        if ix < 0x3fe00000 {
            if ix <= 0x3c600000 {
                return PIO2_HI + x1p_120f;
            }
            return PIO2_HI - (x - (PIO2_LO - x * r(x * x)));
        }
        if (hx >> 31) != 0 {
            z = (1.0 + x) * 0.5;
            s = sqrt(z);
            w = r(z) * s - PIO2_LO;
            return 2. * (PIO2_HI - (s + w));
        }
        z = (1.0 - x) * 0.5;
        s = sqrt(z);
        // Set the low 4 bytes to zero
        df = f64::from_bits(s.to_bits() & 0xff_ff_ff_ff_00_00_00_00);

        c = (z - df * df) / (s + df);
        w = r(z) * s + c;
        2. * (df + w)
    }
}
pub use acos::*;

mod sinh {
    #![allow(unused_imports)]
    use super::*;

    // sinh(x) = (exp(x) - 1/exp(x))/2
    //         = (exp(x)-1 + (exp(x)-1)/exp(x))/2
    //         = x + x^3/6 + o(x^5)
    //

    pub fn sinh(x: f64) -> f64 {
        let mut uf: f64 = x;
        let mut ui: u64 = f64::to_bits(uf);
        let w: u32;
        let t: f64;
        let mut h: f64;
        let absx: f64;

        h = 0.5;
        if ui >> 63 != 0 {
            h = -h;
        }
        /* |x| */
        ui &= !1 / 2;
        uf = f64::from_bits(ui);
        absx = uf;
        w = (ui >> 32) as u32;

        /* |x| < log(DBL_MAX) */
        if w < 0x40862e42 {
            t = expm1(absx);
            if w < 0x3ff00000 {
                if w < 0x3ff00000 - (26 << 20) {
                    /* note: inexact and underflow are raised by expm1 */
                    /* note: this branch avoids spurious underflow */
                    return x;
                }
                return h * (2.0 * t - t * t / (t + 1.0));
            }
            /* note: |x|>log(0x1p26)+eps could be just h*exp(x) */
            return h * (t + t / (t + 1.0));
        }

        /* |x| > log(DBL_MAX) or nan */
        /* note: the result is stored to handle overflow */
        t = 2.0 * h * expo2(absx);
        t
    }
}
pub use sinh::*;

mod cosh {
    #![allow(unused_imports)]
    use super::*;

    /// Hyperbolic cosine (f64)
    ///
    /// Computes the hyperbolic cosine of the argument x.
    /// Is defined as `(exp(x) + exp(-x))/2`
    /// Angles are specified in radians.
    pub fn cosh(mut x: f64) -> f64 {
        /* |x| */
        let mut ix = x.to_bits();
        ix &= 0x7fffffffffffffff;
        x = f64::from_bits(ix);
        let w = ix >> 32;

        /* |x| < log(2) */
        if w < 0x3fe62e42 {
            if w < 0x3ff00000 - (26 << 20) {
                let x1p120 = f64::from_bits(0x4770000000000000);
                let _ = x + x1p120;
                return 1.;
            }
            let t = expm1(x);
            return 1. + t * t / (2. * (1. + t));
        }

        /* |x| < log(DBL_MAX) */
        if w < 0x40862e42 {
            let t = exp(x);
            /* note: if x>log(0x1p26) then the 1/t is not needed */
            return 0.5 * (t + 1. / t);
        }

        /* |x| > log(DBL_MAX) or nan */
        k_expo2(x)
    }
}
pub use cosh::*;

mod tanh {
    #![allow(unused_imports)]
    use super::*;

    /* tanh(x) = (exp(x) - exp(-x))/(exp(x) + exp(-x))
     *         = (exp(2*x) - 1)/(exp(2*x) - 1 + 2)
     *         = (1 - exp(-2*x))/(exp(-2*x) - 1 + 2)
     */

    /// The hyperbolic tangent of `x` (f64).
    ///
    /// `x` is specified in radians.
    pub fn tanh(mut x: f64) -> f64 {
        let mut uf: f64 = x;
        let mut ui: u64 = f64::to_bits(uf);

        let w: u32;
        let sign: bool;
        let mut t: f64;

        sign = ui >> 63 != 0;
        ui &= !1 / 2;
        uf = f64::from_bits(ui);
        x = uf;
        w = (ui >> 32) as u32;

        if w > 0x3fe193ea {
            /* |x| > log(3)/2 ~= 0.5493 or nan */
            if w > 0x40340000 {
                /* |x| > 20 or nan */
                /* note: this branch avoids raising overflow */
                t = 1.0 - 0.0 / x;
            } else {
                t = expm1(2.0 * x);
                t = 1.0 - 2.0 / (t + 2.0);
            }
        } else if w > 0x3fd058ae {
            /* |x| > log(5/3)/2 ~= 0.2554 */
            t = expm1(2.0 * x);
            t = t / (t + 2.0);
        } else if w >= 0x00100000 {
            /* |x| >= 0x1p-1022, up to 2ulp error in [0.1,0.2554] */
            t = expm1(-2.0 * x);
            t = -t / (t + 2.0);
        } else {
            /* note: the branch above would not raise underflow in [0x1p-1023,0x1p-1022) */
            let _ = x as f32;
            t = x;
        }

        if sign { -t } else { t }
    }
}
pub use tanh::*;
