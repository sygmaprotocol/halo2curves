use crate::bls12_381::Fq;
use crate::bls12_381::Fq2;
use crate::bls12_381::Fr;
use crate::{Coordinates, CurveAffine, CurveAffineExt, CurveExt, Group};
use core::cmp;
use core::fmt::Debug;
use core::iter::Sum;
use core::ops::{Add, Mul, Neg, Sub};
use ff::Field;
use group::Curve;
use group::{cofactor::CofactorGroup, prime::PrimeCurveAffine, Group as _, GroupEncoding};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    batch_add, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, new_curve_impl_bls12_381,
};

use super::BLS_X;
use super::BLS_X_IS_NEGATIVE;

new_curve_impl_bls12_381!(
    (pub),  // (($($privacy:tt)*),
    G1,  // $name:ident,
    G1Affine,  // $name_affine:ident,
    G1Compressed,  // $name_compressed:ident,
    Fq::size(),  // $compressed_size:expr,
    Fq,  // $base:ident,
    Fr,  // $scalar:ident,
    (G1_GENERATOR_X,G1_GENERATOR_Y),  // $generator:expr,
    G1_B,  // $constant_b:expr,
    "bls12-381_g1",  // $curve_id:literal,
);

new_curve_impl_bls12_381!(
    (pub),
    G2,  // $name:ident,
    G2Affine,  // $name_affine:ident,
    G2Compressed,  // $name_compressed:ident,
    Fq2::size(),  // $compressed_size:expr,
    Fq2,  // $base:ident,
    Fr,  // $scalar:ident,
    (G2_GENERATOR_X, G2_GENERATOR_Y),  // $generator:expr,
    G2_B,  // $constant_b:expr,
    "bls12-381_g2",  // $curve_id:literal,
);

impl CurveAffineExt for G1Affine {
    batch_add!();

    fn into_coordinates(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }
}

impl CurveAffineExt for G2Affine {
    batch_add!();

    fn into_coordinates(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }
}

const G1_GENERATOR_X: Fq = Fq::from_raw_unchecked([
    0x5cb38790fd530c16,
    0x7817fc679976fff5,
    0x154f95c7143ba1c1,
    0xf0ae6acdf3d0e747,
    0xedce6ecc21dbf440,
    0x120177419e0bfb75,
]);
const G1_GENERATOR_Y: Fq = Fq::from_raw_unchecked([
    0xbaac93d50ce72271,
    0x8c22631a7918fd8e,
    0xdd595f13570725ce,
    0x51ac582950405194,
    0x0e1c8c3fad0059c0,
    0x0bbc3efc5008a26a,
]);
const G1_B: Fq = Fq::from_raw_unchecked([
    0xaa270000000cfff3,
    0x53cc0032fc34000a,
    0x478fe97a6b0a807f,
    0xb1d37ebee6ba24d7,
    0x8ec9733bbf78ab2f,
    0x09d645513d83de7e,
]);

const ENDO_BETA: Fq = Fq::from_raw_unchecked([
    0x30f1361b798a64e8,
    0xf3b8ddab7ece5a2a,
    0x16a8ca3ac61577f7,
    0xc26a2ff874fd029b,
    0x3636b76660701c6e,
    0x051ba4ab241b6160,
]);

const G2_B: Fq2 = Fq2 {
    c0: Fq::from_raw_unchecked([
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x09d645513d83de7e,
    ]),
    c1: Fq::from_raw_unchecked([
        0xaa270000000cfff3,
        0x53cc0032fc34000a,
        0x478fe97a6b0a807f,
        0xb1d37ebee6ba24d7,
        0x8ec9733bbf78ab2f,
        0x09d645513d83de7e,
    ]),
};

const G2_GENERATOR_X: Fq2 = Fq2 {
    c0: Fq::from_raw_unchecked([
        0xf5f28fa202940a10,
        0xb3f5fb2687b4961a,
        0xa1a893b53e2ae580,
        0x9894999d1a3caee9,
        0x6f67b7631863366b,
        0x058191924350bcd7,
    ]),
    c1: Fq::from_raw_unchecked([
        0xa5a9c0759e23f606,
        0xaaa0c59dbccd60c3,
        0x3bb17e18e2867806,
        0x1b1ab6cc8541b367,
        0xc2b6ed0ef2158547,
        0x11922a097360edf3,
    ]),
};

const G2_GENERATOR_Y: Fq2 = Fq2 {
    c0: Fq::from_raw_unchecked([
        0x4c730af860494c4a,
        0x597cfa1f5e369c5a,
        0xe7e6856caa0a635a,
        0xbbefb5e96e0d495f,
        0x07d3a975f0ef25a2,
        0x0083fd8e7e80dae5,
    ]),

    c1: Fq::from_raw_unchecked([
        0xadc0fc92df64b05d,
        0x18aa270a2b1461dc,
        0x86adac6a3be4eba0,
        0x79495c4ec93da33a,
        0xe7175850a43ccaed,
        0x0b2bc2a163de1bf2,
    ]),
};

// const B3: Fq2 = Fq2::add(&Fq2::add(&B, &B), &B);

trait CurveEndo: CurveExt {
    fn endomorphism_base(&self) -> Self;
    fn endomorphism_scalars(k: &Self::ScalarExt) -> (u128, u128);
}

impl CurveEndo for G1 {
    fn endomorphism_base(&self) -> Self {
        unimplemented!();
    }

    fn endomorphism_scalars(_: &Self::ScalarExt) -> (u128, u128) {
        unimplemented!();
    }
}

impl CurveEndo for G2 {
    fn endomorphism_base(&self) -> Self {
        unimplemented!();
    }

    fn endomorphism_scalars(_: &Self::ScalarExt) -> (u128, u128) {
        unimplemented!();
    }
}

fn endomorphism(p: &G1Affine) -> G1Affine {
    // Endomorphism of the points on the curve.
    // endomorphism_p(x,y) = (BETA * x, y)
    // where BETA is a non-trivial cubic root of unity in Fq.
    let mut res = *p;
    res.x *= ENDO_BETA;
    res
}

impl G1 {
    /// Multiply `self` by `crate::BLS_X`, using double and add.
    fn mul_by_x(&self) -> Self {
        let mut xself = G1::identity();
        // NOTE: in BLS12-381 we can just skip the first bit.
        let mut x = BLS_X >> 1;
        let mut tmp = *self;
        while x != 0 {
            tmp = tmp.double();

            if x % 2 == 1 {
                xself += tmp;
            }
            x >>= 1;
        }
        // finally, flip the sign
        if BLS_X_IS_NEGATIVE {
            xself = -xself;
        }
        xself
    }

    #[inline(always)]
    fn mul_by_3b(a: Fq) -> Fq {
        let a = a + a; // 2
        let a = a + a; // 4
        a + a + a // 12
    }
}

impl group::cofactor::CofactorGroup for G1 {
    type Subgroup = G1;

    fn clear_cofactor(&self) -> Self {
        self - self.mul_by_x()
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, 1.into())
    }

    fn is_torsion_free(&self) -> Choice {
        unimplemented!()
    }
}

impl G2 {
    /// Multiply `self` by `crate::BLS_X`, using double and add.
    fn mul_by_x(&self) -> Self {
        let mut xself = Self::identity();
        // NOTE: in BLS12-381 we can just skip the first bit.
        let mut x = BLS_X >> 1;
        let mut acc = *self;
        while x != 0 {
            acc = acc.double();
            if x % 2 == 1 {
                xself += acc;
            }
            x >>= 1;
        }
        // finally, flip the sign
        if BLS_X_IS_NEGATIVE {
            xself = -xself;
        }
        xself
    }

    fn psi(&self) -> Self {
        // 1 / ((u+1) ^ ((q-1)/3))
        let psi_coeff_x = Fq2 {
            c0: Fq::zero(),
            c1: Fq([
                0x890dc9e4867545c3,
                0x2af322533285a5d5,
                0x50880866309b7e2c,
                0xa20d1b8c7e881024,
                0x14e4f04fe2db9068,
                0x14e56d3f1564853a,
            ]),
        };
        // 1 / ((u+1) ^ (p-1)/2)
        let psi_coeff_y = Fq2 {
            c0: Fq([
                0x3e2f585da55c9ad1,
                0x4294213d86c18183,
                0x382844c88b623732,
                0x92ad2afd19103e18,
                0x1d794e4fac7cf0b9,
                0x0bd592fc7d825ec8,
            ]),
            c1: Fq([
                0x7bcfa7a25aa30fda,
                0xdc17dec12a927e7c,
                0x2f088dd86b4ebef1,
                0xd1ca2087da74d4a7,
                0x2da2596696cebc1d,
                0x0e2b7eedbbfd87d2,
            ]),
        };

        let mut x = self.x;
        let mut y = self.y;
        let mut z = self.z;

        x.frobenius_map(1);
        y.frobenius_map(1);
        z.frobenius_map(1);

        Self {
            // x = frobenius(x)/((u+1)^((p-1)/3))
            x: x * psi_coeff_x,
            // y = frobenius(y)/(u+1)^((p-1)/2)
            y: y * psi_coeff_y,
            // z = frobenius(z)
            z,
        }
    }

    fn psi2(&self) -> Self {
        // 1 / 2 ^ ((q-1)/3)
        let psi2_coeff_x = Fq2 {
            c0: Fq([
                0xcd03c9e48671f071,
                0x5dab22461fcda5d2,
                0x587042afd3851b95,
                0x8eb60ebe01bacb9e,
                0x03f97d6e83d050d2,
                0x18f0206554638741,
            ]),
            c1: Fq::zero(),
        };

        Self {
            // x = frobenius^2(x)/2^((p-1)/3); note that q^2 is the order of the field.
            x: self.x * psi2_coeff_x,
            // y = -frobenius^2(y); note that q^2 is the order of the field.
            y: self.y.neg(),
            // z = z
            z: self.z,
        }
    }

    #[inline(always)]
    fn mul_by_3b(x: Fq2) -> Fq2 {
        let b3: Fq2 = Fq2::add(&Fq2::add(&G2_B, &G2_B), &G2_B);
        x * b3
    }
}

impl CofactorGroup for G2 {
    type Subgroup = G2;

    /// Clears the cofactor, using [Budroni-Pintore](https://ia.cr/2017/419).
    /// This is equivalent to multiplying by $h\_\textrm{eff} = 3(z^2 - 1) \cdot
    /// h_2$, where $h_2$ is the cofactor of $\mathbb{G}\_2$ and $z$ is the
    /// parameter of BLS12-381.
    fn clear_cofactor(&self) -> Self {
        let t1 = self.mul_by_x(); // P
        let t2 = self.psi(); // psi(P)

        self.double().psi2() // psi^2(2P)
            + (t1 + t2).mul_by_x() // psi^2(2P) + [x^2] P + [x] psi(P)
            - t1 // psi^2(2P) + [x^2 - x] P + [x] psi(P)
            - t2 // psi^2(2P) + [x^2 - x] P + [x - 1] psi(P)
            - self // psi^2(2P) + [x^2 - x - 1] P + [x - 1] psi(P)
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        unimplemented!();
    }

    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_2$. This should always return true
    /// unless an "unchecked" API was used.
    fn is_torsion_free(&self) -> Choice {
        // Algorithm from Section 4 of https://eprint.iacr.org/2021/1130
        // Updated proof of correctness in https://eprint.iacr.org/2022/352
        //
        // Check that psi(P) == [x] P
        let p = *self;
        p.psi().ct_eq(&p.mul_by_x())
    }
}

#[cfg(test)]
mod tests {

    use crate::bls12_381::G1;
    // use crate::bls12_381::{curve::CurveEndo, curve::ENDO_BETA, Fr, G1Affine, G2};
    // use ff::Field;
    // use rand_core::OsRng;
    // use crate::CurveExt;

    #[test]
    fn test_curve_g1() {
        crate::tests::curve::curve_tests_bls12_381::<G1>();
    }

    #[test]
    fn test_curve_g2() {
        crate::tests::curve::curve_tests_bls12_381::<G1>();
    }

    // TODO - [TEST] [serde] Need to add support for serde
    // #[test]
    // fn test_serialization() {
    //     crate::tests::curve::random_serialization_test::<G1>();
    //     crate::tests::curve::random_serialization_test::<G2>();
    // }
}

impl group::UncompressedEncoding for G1Affine {
    type Uncompressed = G1Compressed;

    fn from_uncompressed(_: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!();
    }

    fn from_uncompressed_unchecked(_: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!();
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        unimplemented!();
    }
}

impl group::UncompressedEncoding for G2Affine {
    type Uncompressed = G2Compressed;

    fn from_uncompressed(_: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!();
    }

    fn from_uncompressed_unchecked(_: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!();
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        unimplemented!();
    }
}

impl G1Affine {
    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_1$. This should always return true
    /// unless an "unchecked" API was used.
    fn is_torsion_free(&self) -> Choice {
        // Algorithm from Section 6 of https://eprint.iacr.org/2021/1130
        // Updated proof of correctness in https://eprint.iacr.org/2022/352
        //
        // Check that endomorphism_p(P) == -[x^2] P

        let minus_x_squared_times_p = G1::from(self).mul_by_x().mul_by_x().neg();
        let endomorphism_p = endomorphism(self);
        minus_x_squared_times_p.ct_eq(&G1::from(endomorphism_p))
    }

    fn to_compressed(self) -> [u8; 48] {
        // Strictly speaking, self.x is zero already when self.infinity is true, but
        // to guard against implementation mistakes we do not assume this.
        let mut res = Fq::conditional_select(&self.x, &Fq::zero(), self.infinity).to_bytes();

        // This point is in compressed form, so we set the most significant bit.
        res[0] |= 1u8 << 7;

        // Is this point at infinity? If so, set the second-most significant bit.
        res[0] |= u8::conditional_select(&0u8, &(1u8 << 6), self.infinity);

        // Is the y-coordinate the lexicographically largest of the two associated with the
        // x-coordinate? If so, set the third-most significant bit so long as this is not
        // the point at infinity.
        res[0] |= u8::conditional_select(
            &0u8,
            &(1u8 << 5),
            (!self.infinity) & self.y.lexicographically_largest(),
        );

        res
    }

    /// Attempts to deserialize a compressed element. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn from_compressed(bytes: &[u8; 48]) -> CtOption<Self> {
        // We already know the point is on the curve because this is established
        // by the y-coordinate recovery procedure in from_compressed_unchecked().

        Self::from_compressed_unchecked(bytes).and_then(|p| CtOption::new(p, p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 48]) -> CtOption<Self> {
        // Obtain the three flags from the start of the byte sequence
        let compression_flag_set = Choice::from((bytes[0] >> 7) & 1);
        let infinity_flag_set = Choice::from((bytes[0] >> 6) & 1);
        let sort_flag_set = Choice::from((bytes[0] >> 5) & 1);

        // Attempt to obtain the x-coordinate
        let x = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            Fq::from_bytes(&tmp)
        };

        x.and_then(|x| {
            // If the infinity flag is set, return the value assuming
            // the x-coordinate is zero and the sort bit is not set.
            //
            // Otherwise, return a recovered point (assuming the correct
            // y-coordinate can be found) so long as the infinity flag
            // was not set.
            CtOption::new(
                G1Affine::identity(),
                infinity_flag_set & // Infinity flag should be set
                compression_flag_set & // Compression flag should be set
                (!sort_flag_set) & // Sort flag should not be set
                x.is_zero(), // The x-coordinate should be zero
            )
            .or_else(|| {
                // Recover a y-coordinate given x by y = sqrt(x^3 + 4)
                ((x.square() * x) + G1_B).sqrt().and_then(|y| {
                    // Switch to the correct y-coordinate if necessary.
                    let y = Fq::conditional_select(
                        &y,
                        &-y,
                        y.lexicographically_largest() ^ sort_flag_set,
                    );

                    CtOption::new(
                        G1Affine {
                            x,
                            y,
                            infinity: infinity_flag_set,
                        },
                        (!infinity_flag_set) & // Infinity flag should not be set
                        compression_flag_set, // Compression flag should be set
                    )
                })
            })
        })
    }
}

impl G2Affine {
    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_2$. This should always return true
    /// unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        // Algorithm from Section 4 of https://eprint.iacr.org/2021/1130
        // Updated proof of correctness in https://eprint.iacr.org/2022/352
        //
        // Check that psi(P) == [x] P
        let p = G2::from(self);
        p.psi().ct_eq(&p.mul_by_x())
    }

    fn to_compressed(self) -> [u8; 96] {
        // Strictly speaking, self.x is zero already when self.infinity is true, but
        // to guard against implementation mistakes we do not assume this.
        let x = Fq2::conditional_select(&self.x, &Fq2::zero(), self.infinity);

        let mut res = [0; 96];

        res[0..48].copy_from_slice(&x.c1.to_bytes()[..]);
        res[48..96].copy_from_slice(&x.c0.to_bytes()[..]);

        // This point is in compressed form, so we set the most significant bit.
        res[0] |= 1u8 << 7;

        // Is this point at infinity? If so, set the second-most significant bit.
        res[0] |= u8::conditional_select(&0u8, &(1u8 << 6), self.infinity);

        // Is the y-coordinate the lexicographically largest of the two associated with the
        // x-coordinate? If so, set the third-most significant bit so long as this is not
        // the point at infinity.
        res[0] |= u8::conditional_select(
            &0u8,
            &(1u8 << 5),
            (!self.infinity) & self.y.lexicographically_largest(),
        );

        res
    }

    /// Attempts to deserialize a compressed element. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn from_compressed(bytes: &[u8; 96]) -> CtOption<Self> {
        // We already know the point is on the curve because this is established
        // by the y-coordinate recovery procedure in from_compressed_unchecked().

        Self::from_compressed_unchecked(bytes).and_then(|p| CtOption::new(p, p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        // Obtain the three flags from the start of the byte sequence
        let compression_flag_set = Choice::from((bytes[0] >> 7) & 1);
        let infinity_flag_set = Choice::from((bytes[0] >> 6) & 1);
        let sort_flag_set = Choice::from((bytes[0] >> 5) & 1);

        // Attempt to obtain the x-coordinate
        let xc1 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            Fq::from_bytes(&tmp)
        };
        let xc0 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            Fq::from_bytes(&tmp)
        };

        xc1.and_then(|xc1| {
            xc0.and_then(|xc0| {
                let x = Fq2 { c0: xc0, c1: xc1 };

                // If the infinity flag is set, return the value assuming
                // the x-coordinate is zero and the sort bit is not set.
                //
                // Otherwise, return a recovered point (assuming the correct
                // y-coordinate can be found) so long as the infinity flag
                // was not set.
                CtOption::new(
                    G2Affine::identity(),
                    infinity_flag_set & // Infinity flag should be set
                    compression_flag_set & // Compression flag should be set
                    (!sort_flag_set) & // Sort flag should not be set
                    x.is_zero(), // The x-coordinate should be zero
                )
                .or_else(|| {
                    // Recover a y-coordinate given x by y = sqrt(x^3 + 4)
                    ((x.square() * x) + G2_B).sqrt().and_then(|y| {
                        // Switch to the correct y-coordinate if necessary.
                        let y = Fq2::conditional_select(
                            &y,
                            &-y,
                            y.lexicographically_largest() ^ sort_flag_set,
                        );

                        CtOption::new(
                            G2Affine {
                                x,
                                y,
                                infinity: infinity_flag_set,
                            },
                            (!infinity_flag_set) & // Infinity flag should not be set
                            compression_flag_set, // Compression flag should be set
                        )
                    })
                })
            })
        })
    }
}
