//! This module provides an implementation of the $\mathbb{G}_1$ group of BLS12-381.

use crate::bls12_381::fq::Fq;
use crate::bls12_381::Fr;
use crate::{Coordinates, CurveAffine, CurveAffineExt, CurveExt, Group};
use core::cmp;
use core::fmt::Debug;
use core::iter::Sum;
use core::ops::{Add, Mul, Neg, Sub};
use ff::{Field, PrimeField};
use group::Curve;
use group::{cofactor::CofactorGroup, prime::PrimeCurveAffine, Group as _, GroupEncoding};
use pasta_curves::arithmetic::FieldExt;
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    batch_add, impl_add_binop_specify_output, impl_binops_additive,
    impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_sub_binop_specify_output, new_curve_impl,
};

new_curve_impl!(
    (pub),
    G1,
    G1Affine,
    G1Compressed,
    G1Uncompressed,
    Fq::size(),
    Fq,
    Fr,
    (G1_GENERATOR_X,G1_GENERATOR_Y),
    G1_B,
    "bls12_381_g1",
);

impl CurveAffineExt for G1Affine {
    batch_add!();

    fn into_coordinates(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }
}

const G1_GENERATOR_X: Fq = Fq::from_raw_unchecked([
    0x5cb3_8790_fd53_0c16,
    0x7817_fc67_9976_fff5,
    0x154f_95c7_143b_a1c1,
    0xf0ae_6acd_f3d0_e747,
    0xedce_6ecc_21db_f440,
    0x1201_7741_9e0b_fb75,
]);

const G1_GENERATOR_Y: Fq = Fq::from_raw_unchecked([
    0xbaac_93d5_0ce7_2271,
    0x8c22_631a_7918_fd8e,
    0xdd59_5f13_5707_25ce,
    0x51ac_5829_5040_5194,
    0x0e1c_8c3f_ad00_59c0,
    0x0bbc_3efc_5008_a26a,
]);

const G1_B: Fq = Fq::from_raw_unchecked([
    0xaa27_0000_000c_fff3,
    0x53cc_0032_fc34_000a,
    0x478f_e97a_6b0a_807f,
    0xb1d3_7ebe_e6ba_24d7,
    0x8ec9_733b_bf78_ab2f,
    0x09d6_4551_3d83_de7e,
]);

/// A nontrivial third root of unity in Fp
pub const BETA: Fq = Fq::from_raw_unchecked([
    0x30f1_361b_798a_64e8,
    0xf3b8_ddab_7ece_5a2a,
    0x16a8_ca3a_c615_77f7,
    0xc26a_2ff8_74fd_029b,
    0x3636_b766_6070_1c6e,
    0x051b_a4ab_241b_6160,
]);

pub const BLS_X: u64 = 0xd201_0000_0001_0000;
pub const BLS_X_IS_NEGATIVE: bool = true;

impl G1 {
    /// Multiply `self` by `crate::BLS_X`, using double and add.
    fn mul_by_x(&self) -> Self {
        let mut xself = Self::identity();
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
}

impl CofactorGroup for G1 {
    type Subgroup = G1;

    /// Multiplies by $(1 - z)$, where $z$ is the parameter of BLS12-381, which
    /// [suffices to clear](https://ia.cr/2019/403) the cofactor and map
    /// elliptic curve points to elements of $\mathbb{G}\_1$.
    fn clear_cofactor(&self) -> G1 {
        self - self.mul_by_x()
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, self.is_torsion_free())
    }

    fn is_torsion_free(&self) -> Choice {
        // Algorithm from Section 6 of https://eprint.iacr.org/2021/1130
        // Updated proof of correctness in https://eprint.iacr.org/2022/352
        //
        // Check that endomorphism_p(P) == -[x^2] P

        let minus_x_squared_times_p = self.mul_by_x().mul_by_x().neg();
        let endomorphism_p = endomorphism(&self.to_affine());
        minus_x_squared_times_p.ct_eq(&G1::from(endomorphism_p))
    }
}

trait CurveEndo: CurveExt {
    fn endomorphism_base(&self) -> Self;
    fn endomorphism_scalars(k: &Self::ScalarExt) -> (u128, u128);
}

impl CurveEndo for G1 {
    fn endomorphism_base(&self) -> Self {
        // Endomorphism of the points on the curve.
        // endomorphism_p(x,y) = (BETA * x, y)
        // where BETA is a non-trivial cubic root of unity in Fq.
        let mut res = *self;
        res.x *= BETA;
        res
    }

    fn endomorphism_scalars(k: &Self::ScalarExt) -> (u128, u128) {
        todo!()
    }
}

fn endomorphism(p: &G1Affine) -> G1Affine {
    // Endomorphism of the points on the curve.
    // endomorphism_p(x,y) = (BETA * x, y)
    // where BETA is a non-trivial cubic root of unity in Fq.
    let mut res = *p;
    res.x *= BETA;
    res
}

#[cfg(test)]
mod tests {
    use crate::bls12_381::G1;

    #[test]
    fn test_curve() {
        crate::tests::curve::curve_tests::<G1>();
    }

    #[test]
    fn test_serialization() {
        crate::tests::curve::random_serialization_test::<G1>();
        #[cfg(feature = "derive_serde")]
        {
            crate::tests::curve::random_serde_test::<G1>();
        }
    }
}
