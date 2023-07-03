#[cfg(feature = "asm")]
use super::assembly::assembly_field;

use super::LegendreSymbol;
use crate::arithmetic::{adc, adc_u64, mac, macx, sbb};
use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};
use serde::{Deserialize, Serialize};

use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::PrimeField;
use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// This represents an element of $\mathbb{F}_q$ where
///
/// `q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787`
/// `q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
///
/// is the base field of the BLS12-381 curve.
// The internal representation of this type is six 64-bit unsigned
// integers in little-endian order. `Fq` values are always in
// Montgomery form; i.e., Fq(a) = aR mod q, with R = 2^384.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Fq(pub(crate) [u64; 6]);

/// Constant representing the modulus
/// q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
const MODULUS: Fq = Fq([
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
]);
const MODULUS_STR: &str = "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
const MODULUS_BITS: u32 = 381;

// 2^s * t = MODULUS - 1 with t odd
const S: u32 = 1;

/// INV = -(q^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x89f3fffcfffcfffd;

// R = 2^384 % q
// R = 0x15f65ec3fa80e4935c071a97a256ec6d77ce5853705257455f48985753c758baebf4000bc40c0002760900000002fffd
const R: Fq = Fq([
    0x760900000002fffd,
    0xebf4000bc40c0002,
    0x5f48985753c758ba,
    0x77ce585370525745,
    0x5c071a97a256ec6d,
    0x15f65ec3fa80e493,
]);

// ` = 2^(384*2) mod p
// R2 = 0x11988fe592cae3aa9a793e85b519952d67eb88a9939d83c08de5476c4c95b6d50a76e6a609d104f1f4df1f341c341746
const R2: Fq = Fq([
    0xf4df1f341c341746,
    0xa76e6a609d104f1,
    0x8de5476c4c95b6d5,
    0x67eb88a9939d83c0,
    0x9a793e85b519952d,
    0x11988fe592cae3aa,
]);

// R2 = 2^(384*3) mod p
// R2 = 0xaa6346091755d4d2512d4356572472834c04e5e921e17619a53352a615e29dd315f831e03a7adf8ed48ac6bd94ca1e0
const R3: Fq = Fq([
    0xed48ac6bd94ca1e0,
    0x315f831e03a7adf8,
    0x9a53352a615e29dd,
    0x34c04e5e921e1761,
    0x2512d43565724728,
    0x0aa6346091755d4d,
]);

// NEGATIVE_ONE = -((2**384) mod q) mod q
// NEGATIVE_ONE = 0x40ab3263eff0206ef148d1ea0f4c069eca8f3318332bb7a07e83a49a2e99d6932b7fff2ed47fffd43f5fffffffcaaae
pub const NEGATIVE_ONE: Fq = Fq([
    0x43f5fffffffcaaae,
    0x32b7fff2ed47fffd,
    0x7e83a49a2e99d69,
    0xeca8f3318332bb7a,
    0xef148d1ea0f4c069,
    0x40ab3263eff0206,
]);

// Unused constant
const TWO_INV: Fq = Fq::zero();

// 2^s root of unity computed by GENERATOR^t
// 0x40ab3263eff0206ef148d1ea0f4c069eca8f3318332bb7a7e83a49a2e99d6932b7fff2ed47fffd43f5fffffffcaaae
const ROOT_OF_UNITY: Fq = Fq([
    0x43f5fffffffcaaae,
    0x32b7fff2ed47fffd,
    0x7e83a49a2e99d69,
    0xeca8f3318332bb7a,
    0xef148d1ea0f4c069,
    0x40ab3263eff0206,
]);

// Unused constant for base field
const ROOT_OF_UNITY_INV: Fq = Fq::zero();

// Unused constant for base field
const DELTA: Fq = Fq::zero();

// Unused constant
const ZETA: Fq = Fq::zero();

use crate::{
    field_arithmetic_bls12_381, field_common_fq, field_specific_bls12_381,
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fq, Fq);
impl_binops_multiplicative!(Fq, Fq);
#[cfg(not(feature = "asm"))]
field_common_fq!(
    Fq,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);
#[cfg(not(feature = "asm"))]
field_arithmetic_bls12_381!(Fq, MODULUS, INV, sparse);
#[cfg(feature = "asm")]
assembly_field!(
    Fq,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);

impl Fq {
    pub const fn size() -> usize {
        48
    }

    pub fn legendre(&self) -> LegendreSymbol {
        // s = self^((q - 1) // 2)
        // (q - 1) / 2 = 0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b12f55ffff58a9ffffdcff7fffffffd555
        let s = &[
            0xdcff7fffffffd555,
            0xf55ffff58a9ffff,
            0xb39869507b587b12,
            0xb23ba5c279c2895f,
            0x258dd3db21a5d66b,
            0xd0088f51cbff34d,
        ];
        let s = self.pow_fq(s);
        if s == Self::zero() {
            LegendreSymbol::Zero
        } else if s == Self::one() {
            LegendreSymbol::QuadraticResidue
        } else {
            LegendreSymbol::QuadraticNonResidue
        }
    }

    fn pow_fq(&self, by: &[u64; 6]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();

                if ((*e >> i) & 1) == 1 {
                    res *= self;
                }
            }
        }
        res
    }
}

impl ff::Field for Fq {
    fn random(mut rng: impl RngCore) -> Self {
        let mut random_bytes = [0; 64];
        rng.fill_bytes(&mut random_bytes[..]);

        Self::from_bytes_wide(&random_bytes)
    }

    #[inline(always)]
    fn zero() -> Self {
        Self::zero()
    }

    #[inline(always)]
    fn one() -> Self {
        Self::one()
    }

    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        // We use Shank's method, as q = 3 (mod 4). This means
        // we only need to exponentiate by ( q + 1 ) / 4. This only
        // works for elements that are actually quadratic residue,
        // so we check that we got the correct result at the end.
        // (q + 1) / 4 =  0x680447a8e5ff9a692c6e9ed90d2eb35d91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab
        const Q_PLUS_1_DIV_4: [u64; 6] = [
            0xee7fbfffffffeaab,
            0x07aaffffac54ffff,
            0xd9cc34a83dac3d89,
            0xd91dd2e13ce144af,
            0x92c6e9ed90d2eb35,
            0x0680447a8e5ff9a6,
        ];
        let sqrt = self.pow_fq(&Q_PLUS_1_DIV_4);

        CtOption::new(sqrt, sqrt.square().ct_eq(self))
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        // Exponentiate by q - 2
        // Q_MIN_2 = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9
        let tmp = self.pow_fq(&[
            0xb9feffffffffaaa9,
            0x1eabfffeb153ffff,
            0x6730d2a0f6b0f624,
            0x64774b84f38512bf,
            0x4b1ba7b6434bacd7,
            0x1a0111ea397fe69a,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }
}

use std::ops::Index;
use std::ops::RangeFull;

#[derive(Clone, Copy, Debug)]
pub struct FqBytes {
    pub slice: [u8; 48],
}

impl From<[u8; 48]> for FqBytes {
    fn from(bytes: [u8; 48]) -> Self {
        Self { slice: bytes }
    }
}

impl Index<RangeFull> for FqBytes {
    type Output = [u8];
    fn index(&self, _: RangeFull) -> &[u8] {
        &self.slice[..]
    }
}

impl Index<usize> for FqBytes {
    type Output = u8;
    fn index(&self, idx: usize) -> &Self::Output {
        &self.slice[idx]
    }
}

impl Default for FqBytes {
    fn default() -> Self {
        Self { slice: [0u8; 48] }
    }
}

impl AsMut<[u8]> for FqBytes {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.slice
    }
}

impl AsRef<[u8]> for FqBytes {
    fn as_ref(&self) -> &[u8] {
        &self.slice
    }
}

impl ff::PrimeField for Fq {
    // type Repr = [u8; 48];
    // Need to implement FqBytes otherwise will get the error:
    // "the trait bound `[u8; 48]: std::default::Default` is not satisfied the
    // following other types implement trait `std::default::Default`",
    // where trade bound `Default` on Repr is required by PrimeField
    type Repr = FqBytes;

    const NUM_BITS: u32 = MODULUS_BITS;
    const CAPACITY: u32 = Self::NUM_BITS - 1;
    const S: u32 = S;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fq([0, 0, 0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr.slice[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr.slice[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr.slice[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr.slice[24..32].try_into().unwrap());
        tmp.0[4] = u64::from_le_bytes(repr.slice[32..40].try_into().unwrap());
        tmp.0[5] = u64::from_le_bytes(repr.slice[40..48].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = tmp.0[0].overflowing_sub(MODULUS.0[0]);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);
        let (_, borrow) = sbb(tmp.0[4], MODULUS.0[4], borrow);
        let (_, borrow) = sbb(tmp.0[5], MODULUS.0[5], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        // Turn into canonical form by computing
        // (a.R) / R = a
        #[cfg(feature = "asm")]
        let tmp = Self::montgomery_reduce(&[
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], 0, 0, 0, 0, 0, 0,
        ]);

        #[cfg(not(feature = "asm"))]
        let tmp = Self::montgomery_reduce_short(
            self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5],
        );

        let mut res = [0; 48];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());
        res[32..40].copy_from_slice(&tmp.0[4].to_le_bytes());
        res[40..48].copy_from_slice(&tmp.0[5].to_le_bytes());

        FqBytes { slice: res }
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr().as_ref()[0] & 1)
    }

    fn multiplicative_generator() -> Self {
        unimplemented!()
    }

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

impl SqrtRatio for Fq {
    const T_MINUS1_OVER2: [u64; 4] = unimplemented!();

    fn get_lower_32(&self) -> u32 {
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ff::Field;
    use rand_core::OsRng;

    #[test]
    fn test_ser() {
        let a0 = Fq::random(OsRng);
        let a_bytes = a0.to_bytes();
        let a1 = Fq::from_bytes(&a_bytes).unwrap();
        assert_eq!(a0, a1);
    }

    #[test]
    fn test_sqrt_fq() {
        // a = 4
        let a = Fq::from_raw_unchecked([
            0xaa270000000cfff3,
            0x53cc0032fc34000a,
            0x478fe97a6b0a807f,
            0xb1d37ebee6ba24d7,
            0x8ec9733bbf78ab2f,
            0x09d645513d83de7e,
        ]);

        assert_eq!(
            // sqrt(4) = -2
            -a.sqrt().unwrap(),
            // 2
            Fq::from_raw_unchecked([
                0x3213_0000_0006_554f,
                0xb93c_0018_d6c4_0005,
                0x5760_5e0d_b0dd_bb51,
                0x8b25_6521_ed1f_9bcb,
                0x6cf2_8d79_0162_2c03,
                0x11eb_ab9d_bb81_e28c,
            ])
        );

        for _ in 0..10000 {
            let a = Fq::random(OsRng);
            let mut b = a;
            b = b.square();
            assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

            let b = b.sqrt().unwrap();
            let mut negb = b;
            negb = negb.neg();

            assert!(a == b || a == negb);
        }

        let mut c = Fq::one();
        for _ in 0..10000 {
            let mut b = c;
            b = b.square();
            assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

            b = b.sqrt().unwrap();

            if b != c {
                b = b.neg();
            }

            assert_eq!(b, c);

            c += &Fq::one();
        }
    }

    // TODO [TEST] [from_u512]
    // #[test]
    // fn test_from_u512() {
    //     let a = Fq::from_u512([
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //         0xaaaaaaaaaaaaaaaa,
    //     ]);
    //     println!("a = {:?}", a);
    //     // 0x01dce8d1b03439d8a725335a9edeb9d2b94a9d23e2648fdfac2575af577605842e217ad51b4754df0efe265b19724868

    //     assert_eq!(
    //         Fq::from_raw_unchecked([
    //             0x0efe265b19724868,
    //             0x2e217ad51b4754df,
    //             0xac2575af57760584,
    //             0xb94a9d23e2648fdf,
    //             0xa725335a9edeb9d2,
    //             0x01dce8d1b03439d8,
    //         ]),
    //         Fq::from_u512([
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa,
    //             0xaaaaaaaaaaaaaaaa
    //         ])
    //     );
    // }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fq>("fq".to_string());
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<Fq>("fq".to_string());
    }
}
