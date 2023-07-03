use super::fq::Fq;
use super::LegendreSymbol;
use core::convert::TryInto;
use core::ops::{Add, Mul, Neg, Sub};
use ff::Field;
use pasta_curves::arithmetic::{FieldExt, Group, SqrtRatio};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

const MODULUS_BITS: u32 = 381;

/// An element of Fq2, represented by c0 + c1 * u.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct Fq2 {
    pub c0: Fq,
    pub c1: Fq,
}

/// `Fq2` elements are ordered lexicographically.
impl Ord for Fq2 {
    #[inline(always)]
    fn cmp(&self, other: &Fq2) -> Ordering {
        match self.c1.cmp(&other.c1) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c0.cmp(&other.c0),
        }
    }
}

impl PartialOrd for Fq2 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq2) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fq2 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fq2 {
            c0: Fq::conditional_select(&a.c0, &b.c0, choice),
            c1: Fq::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl Eq for Fq2 {}
impl PartialEq for Fq2 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl ConstantTimeEq for Fq2 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl Default for Fq2 {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl From<Fq2> for [u8; 96] {
    fn from(value: Fq2) -> [u8; 96] {
        value.to_bytes()
    }
}

impl<'a> From<&'a Fq2> for [u8; 96] {
    fn from(value: &'a Fq2) -> [u8; 96] {
        value.to_bytes()
    }
}

impl Neg for Fq2 {
    type Output = Fq2;

    #[inline]
    fn neg(self) -> Fq2 {
        -&self
    }
}

impl<'a> Neg for &'a Fq2 {
    type Output = Fq2;

    #[inline]
    fn neg(self) -> Fq2 {
        self.neg()
    }
}

impl<'a, 'b> Sub<&'b Fq2> for &'a Fq2 {
    type Output = Fq2;

    #[inline]
    fn sub(self, rhs: &'b Fq2) -> Fq2 {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fq2> for &'a Fq2 {
    type Output = Fq2;

    #[inline]
    fn add(self, rhs: &'b Fq2) -> Fq2 {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fq2> for &'a Fq2 {
    type Output = Fq2;

    #[inline]
    fn mul(self, rhs: &'b Fq2) -> Fq2 {
        self.mul(rhs)
    }
}

use crate::{
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fq2, Fq2);
impl_binops_multiplicative!(Fq2, Fq2);

impl Fq2 {
    pub const fn new(c0: Fq, c1: Fq) -> Self {
        Fq2 { c0, c1 }
    }

    pub const fn size() -> usize {
        96
    }
    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Fq`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; 96]) -> CtOption<Fq2> {
        let c0 = Fq::from_bytes(bytes[0..48].try_into().unwrap());
        let c1 = Fq::from_bytes(bytes[48..96].try_into().unwrap());
        CtOption::new(
            Fq2 {
                c0: c0.unwrap(),
                c1: c1.unwrap(),
            },
            c0.is_some() & c1.is_some(),
        )
    }

    /// Converts an element of `Fq2` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes(&self) -> [u8; 96] {
        let mut res = [0u8; 96];
        let c0_bytes = self.c0.to_bytes();
        let c1_bytes = self.c1.to_bytes();
        res[0..48].copy_from_slice(&c0_bytes[..]);
        res[48..96].copy_from_slice(&c1_bytes[..]);
        res
    }

    pub fn legendre(&self) -> LegendreSymbol {
        self.norm().legendre()
    }

    pub fn mul_assign(&mut self, other: &Self) {
        let mut t1 = self.c0 * other.c0;
        let mut t0 = self.c0 + self.c1;
        let t2 = self.c1 * other.c1;
        self.c1 = other.c0 + other.c1;
        self.c0 = t1 - t2;
        t1 += t2;
        t0 *= self.c1;
        self.c1 = t0 - t1;
    }

    pub fn square_assign(&mut self) {
        let ab = self.c0 * self.c1;
        let c0c1 = self.c0 + self.c1;
        let mut c0 = -self.c1;
        c0 += self.c0;
        c0 *= c0c1;
        c0 -= ab;
        self.c1 = ab.double();
        self.c0 = c0 + ab;
    }

    pub fn double(&self) -> Self {
        Self {
            c0: self.c0.double(),
            c1: self.c1.double(),
        }
    }

    pub fn double_assign(&mut self) {
        self.c0 = self.c0.double();
        self.c1 = self.c1.double();
    }

    pub fn add(&self, other: &Self) -> Self {
        Self {
            c0: self.c0.add(&other.c0),
            c1: self.c1.add(&other.c1),
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self {
            c0: self.c0.sub(&other.c0),
            c1: self.c1.sub(&other.c1),
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut t = *other;
        t.mul_assign(self);
        t
    }

    pub fn square(&self) -> Self {
        let mut t = *self;
        t.square_assign();
        t
    }

    pub fn neg(&self) -> Self {
        Self {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }

    /// Alternative implementation of frobenius_map(), keeping here for reference
    /// Raises this element to p.
    // #[inline(always)]
    // pub fn frobenius_map_conjugate(&mut self) {
    // This is always just a conjugation. If you're curious why, here's
    // an article about it: https://alicebob.cryptoland.net/the-frobenius-endomorphism-with-finite-fields/
    // self.conjugate()
    //     self.c1 = -self.c1;
    // }

    pub fn frobenius_map(&mut self, power: usize) {
        self.c1 = self.c1.mul(&FROBENIUS_COEFF_FQ2_C1[power % 2]);
    }

    #[inline(always)]
    pub fn mul_by_nonresidue(&mut self) {
        // Multiply a + bu by u + 1, getting
        // au + a + bu^2 + bu
        // and because u^2 = -1, we get
        // (a - b) + (a + b)u
        let t0 = self.c0;
        self.c0 -= self.c1;
        self.c1 += t0;
    }

    #[inline(always)]
    pub fn mul_by_nonresidue_bls12_381(&self) -> Fq2 {
        // Multiply a + bu by u + 1, getting
        // au + a + bu^2 + bu
        // and because u^2 = -1, we get
        // (a - b) + (a + b)u

        Fq2 {
            c0: self.c0 - self.c1,
            c1: self.c0 + self.c1,
        }
    }

    // Multiply this element by ξ where ξ=i+9
    pub fn mul_by_xi(&mut self) {
        // (xi+y)(i+9) = (9x+y)i+(9y-x)
        let t0 = self.c0;
        let t1 = self.c1;

        // 8*x*i + 8*y
        self.double_assign();
        self.double_assign();
        self.double_assign();

        // 9*y
        self.c0 += &t0;
        // (9*y - x)
        self.c0 -= &t1;

        // (9*x)i
        self.c1 += &t1;
        // (9*x + y)
        self.c1 += &t0;
    }

    /// Norm of Fq2 as extension field in i over Fq
    pub fn norm(&self) -> Fq {
        let mut t0 = self.c0;
        let mut t1 = self.c1;
        t0 = t0.square();
        t1 = t1.square();
        t1 + t0
    }

    pub fn invert(&self) -> CtOption<Self> {
        let mut t1 = self.c1;
        t1 = t1.square();
        let mut t0 = self.c0;
        t0 = t0.square();
        t0 += &t1;
        t0.invert().map(|t| {
            let mut tmp = Fq2 {
                c0: self.c0,
                c1: self.c1,
            };
            tmp.c0 *= &t;
            tmp.c1 *= &t;
            tmp.c1 = -tmp.c1;

            tmp
        })
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    #[inline]
    pub fn lexicographically_largest(&self) -> Choice {
        // If this element's c1 coefficient is lexicographically largest
        // then it is lexicographically largest. Otherwise, in the event
        // the c1 coefficient is zero and the c0 coefficient is
        // lexicographically largest, then this element is lexicographically
        // largest.

        self.c1.lexicographically_largest()
            | (self.c1.is_zero() & self.c0.lexicographically_largest())
    }
}

impl Field for Fq2 {
    fn random(mut rng: impl RngCore) -> Self {
        Fq2 {
            c0: Fq::random(&mut rng),
            c1: Fq::random(&mut rng),
        }
    }

    fn zero() -> Self {
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        }
    }

    fn one() -> Self {
        Fq2 {
            c0: Fq::one(),
            c1: Fq::zero(),
        }
    }

    fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero()
    }

    fn square(&self) -> Self {
        self.square()
    }

    fn double(&self) -> Self {
        self.double()
    }

    fn sqrt(&self) -> CtOption<Self> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf
        // with constant time modifications.

        CtOption::new(Fq2::zero(), self.is_zero()).or_else(|| {
            // a1 = self^((p - 3) / 4)
            let a1 = self.pow_vartime([
                0xee7f_bfff_ffff_eaaa,
                0x07aa_ffff_ac54_ffff,
                0xd9cc_34a8_3dac_3d89,
                0xd91d_d2e1_3ce1_44af,
                0x92c6_e9ed_90d2_eb35,
                0x0680_447a_8e5f_f9a6,
            ]);

            // alpha = a1^2 * self = self^((p - 3) / 2 + 1) = self^((p - 1) / 2)
            let alpha = a1.square() * self;

            // x0 = self^((p + 1) / 4)
            let x0 = a1 * self;

            // In the event that alpha = -1, the element is order p - 1 and so
            // we're just trying to get the square of an element of the subfield
            // Fp. This is given by x0 * u, since u = sqrt(-1). Since the element
            // x0 = a + bu has b = 0, the solution is therefore au.
            CtOption::new(
                Fq2 {
                    c0: -x0.c1,
                    c1: x0.c0,
                },
                alpha.ct_eq(&(Fq2::one()).neg()),
            )
            // Otherwise, the correct solution is (1 + alpha)^((q - 1) // 2) * x0
            .or_else(|| {
                CtOption::new(
                    (alpha + Fq2::one()).pow_vartime([
                        0xdcff_7fff_ffff_d555,
                        0x0f55_ffff_58a9_ffff,
                        0xb398_6950_7b58_7b12,
                        0xb23b_a5c2_79c2_895f,
                        0x258d_d3db_21a5_d66b,
                        0x0d00_88f5_1cbf_f34d,
                    ]) * x0,
                    Choice::from(1),
                )
            })
            // Only return the result if it's really the square root (and so
            // self is actually quadratic nonresidue)
            .and_then(|sqrt| CtOption::new(sqrt, sqrt.square().ct_eq(self)))
        })
    }

    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }
}

impl From<bool> for Fq2 {
    fn from(bit: bool) -> Fq2 {
        if bit {
            Fq2::one()
        } else {
            Fq2::zero()
        }
    }
}

impl From<u64> for Fq2 {
    fn from(val: u64) -> Self {
        Fq2 {
            c0: Fq::from(val),
            c1: Fq::zero(),
        }
    }
}

impl FieldExt for Fq2 {
    const MODULUS: &'static str =
        "0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";

    const ROOT_OF_UNITY_INV: Self = Fq2 {
        c0: Fq::zero(),
        c1: Fq::zero(),
    };
    const DELTA: Self = Fq2 {
        c0: Fq::zero(),
        c1: Fq::zero(),
    };
    const TWO_INV: Fq2 = Fq2 {
        c0: Fq::zero(),
        c1: Fq::zero(),
    };

    // Unused constant
    const ZETA: Self = Fq2 {
        c0: Fq::zero(),
        c1: Fq::zero(),
    };

    /// Converts a 512-bit little endian integer into
    /// a `Fq` by reducing by the modulus.
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        Self::new(Fq::from_bytes_wide(bytes), Fq::zero())
    }

    fn from_u128(v: u128) -> Self {
        Fq2 {
            c0: Fq::from_raw_unchecked([v as u64, (v >> 64) as u64, 0, 0, 0, 0]),
            c1: Fq::zero(),
        }
    }

    fn get_lower_128(&self) -> u128 {
        self.c0.get_lower_128()
    }

    // /// Writes this element in its normalized, little endian form into a buffer.
    // fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
    //     let compressed = self.to_bytes();
    //     writer.write_all(&compressed[..])
    // }

    // /// Reads a normalized, little endian represented field element from a
    // /// buffer.
    // fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
    //     let mut compressed = [0u8; 96];
    //     reader.read_exact(&mut compressed[..])?;
    //     Option::from(Self::from_bytes(&compressed))
    //         .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof"))
    // }
}

impl SqrtRatio for Fq2 {
    const T_MINUS1_OVER2: [u64; 4] = unimplemented!();

    fn pow_by_t_minus1_over2(&self) -> Self {
        unimplemented!();
    }

    fn get_lower_32(&self) -> u32 {
        unimplemented!();
    }

    #[cfg(feature = "sqrt-table")]
    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        unimplemented!();
    }

    #[cfg(feature = "sqrt-table")]
    fn sqrt_alt(&self) -> (Choice, Self) {
        unimplemented!();
    }
}

impl Group for Fq2 {
    type Scalar = Fq2;

    fn group_zero() -> Self {
        Self::zero()
    }
    fn group_add(&mut self, rhs: &Self) {
        *self += *rhs;
    }
    fn group_sub(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
    fn group_scale(&mut self, by: &Self::Scalar) {
        *self *= *by;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Fq2Bytes {
    pub slice: [u8; 96],
}

impl Default for Fq2Bytes {
    fn default() -> Self {
        Self { slice: [0u8; 96] }
    }
}

impl AsMut<[u8]> for Fq2Bytes {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.slice
    }
}

impl AsRef<[u8]> for Fq2Bytes {
    fn as_ref(&self) -> &[u8] {
        &self.slice
    }
}

impl ff::PrimeField for Fq2 {
    type Repr = Fq2Bytes;

    const NUM_BITS: u32 = MODULUS_BITS;
    const CAPACITY: u32 = MODULUS_BITS - 1;

    const S: u32 = 0;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let c0 = Fq::from_bytes(&repr.slice[..48].try_into().unwrap());
        let c1 = Fq::from_bytes(&repr.slice[48..].try_into().unwrap());
        // Disallow overflow representation
        CtOption::new(Fq2::new(c0.unwrap(), c1.unwrap()), Choice::from(1))
    }

    fn to_repr(&self) -> Self::Repr {
        Fq2Bytes {
            slice: self.to_bytes(),
        }
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr().as_ref()[0] & 1)
    }

    fn multiplicative_generator() -> Self {
        unimplemented!()
    }

    fn root_of_unity() -> Self {
        unimplemented!()
    }
}

impl crate::serde::SerdeObject for Fq2 {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), 96);
        let [c0, c1] = [0, 48].map(|i| Fq::from_raw_bytes_unchecked(&bytes[i..i + 48]));
        Self { c0, c1 }
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 96 {
            return None;
        }
        let [c0, c1] = [0, 48].map(|i| Fq::from_raw_bytes(&bytes[i..i + 48]));
        c0.zip(c1).map(|(c0, c1)| Self { c0, c1 })
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(96);
        for limb in self.c0.0.iter().chain(self.c1.0.iter()) {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let [c0, c1] = [(); 2].map(|_| Fq::read_raw_unchecked(reader));
        Self { c0, c1 }
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let c0 = Fq::read_raw(reader)?;
        let c1 = Fq::read_raw(reader)?;
        Ok(Self { c0, c1 })
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        self.c0.write_raw(writer)?;
        self.c1.write_raw(writer)
    }
}

pub const FROBENIUS_COEFF_FQ2_C1: [Fq; 2] = [
    // Fq(-1)**(((q^0) - 1) / 2)
    // it's 1 in Montgommery form
    Fq([
        0x760900000002fffd,
        0xebf4000bc40c0002,
        0x5f48985753c758ba,
        0x77ce585370525745,
        0x5c071a97a256ec6d,
        0x15f65ec3fa80e493,
    ]),
    // Fq(-1)**(((q^1) - 1) / 2)
    Fq([
        0x43f5fffffffcaaae,
        0x32b7fff2ed47fffd,
        0x7e83a49a2e99d69,
        0xeca8f3318332bb7a,
        0xef148d1ea0f4c069,
        0x40ab3263eff0206,
    ]),
];

#[cfg(test)]
mod test {
    use super::*;
    use rand::SeedableRng;
    use rand_core::OsRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    #[ignore]
    fn test_ser() {
        let a0 = Fq2::random(OsRng);
        let a_bytes = a0.to_bytes();
        let a1 = Fq2::from_bytes(&a_bytes).unwrap();
        assert_eq!(a0, a1);
    }

    #[test]
    fn test_fq2_ordering() {
        let mut a = Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        };

        let mut b = a;

        assert!(a.cmp(&b) == Ordering::Equal);
        b.c0 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Less);
        a.c0 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Equal);
        b.c1 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Less);
        a.c0 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Less);
        a.c1 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Greater);
        b.c0 += &Fq::one();
        assert!(a.cmp(&b) == Ordering::Equal);
    }

    #[test]
    fn test_fq2_basics() {
        assert_eq!(
            Fq2 {
                c0: Fq::zero(),
                c1: Fq::zero(),
            },
            Fq2::zero()
        );
        assert_eq!(
            Fq2 {
                c0: Fq::one(),
                c1: Fq::zero(),
            },
            Fq2::one()
        );
        assert_eq!(Fq2::zero().is_zero().unwrap_u8(), 1);
        assert_eq!(Fq2::one().is_zero().unwrap_u8(), 0);
        assert_eq!(
            Fq2 {
                c0: Fq::zero(),
                c1: Fq::one(),
            }
            .is_zero()
            .unwrap_u8(),
            0
        );
    }

    #[test]
    fn test_fq2_squaring() {
        let mut a = Fq2 {
            c0: Fq::one(),
            c1: Fq::one(),
        }; // u + 1
        a.square_assign();
        assert_eq!(
            a,
            Fq2 {
                c0: Fq::zero(),
                c1: Fq::one() + Fq::one(),
            }
        ); // 2u

        let mut a = Fq2 {
            c0: Fq::zero(),
            c1: Fq::one(),
        }; // u
        a.square_assign();
        assert_eq!(a, {
            let neg1 = -Fq::one();
            Fq2 {
                c0: neg1,
                c1: Fq::zero(),
            }
        }); // -1
    }

    #[test]
    fn test_fq2_mul_nonresidue() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let nqr = Fq2 {
            c0: Fq::one(),
            c1: Fq::one(),
        };

        for _ in 0..1000 {
            let mut a = Fq2::random(&mut rng);
            let mut b = a;
            a.mul_by_nonresidue();
            b.mul_assign(&nqr);

            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_fq2_legendre() {
        assert_eq!(LegendreSymbol::Zero, Fq2::zero().legendre());
        // i^2 = -1
        let mut m1 = Fq2::one();
        m1 = m1.neg();
        assert_eq!(LegendreSymbol::QuadraticResidue, m1.legendre());
        m1.mul_by_nonresidue();
        assert_eq!(LegendreSymbol::QuadraticNonResidue, m1.legendre());
    }

    #[test]
    pub fn test_sqrt() {
        // a = 1488924004771393321054797166853618474668089414631333405711627789629391903630694737978065425271543178763948256226639*u + 784063022264861764559335808165825052288770346101304131934508881646553551234697082295473567906267937225174620141295
        let a = Fq2 {
            c0: Fq::from_raw_unchecked([
                0x2bee_d146_27d7_f9e9,
                0xb661_4e06_660e_5dce,
                0x06c4_cc7c_2f91_d42c,
                0x996d_7847_4b7a_63cc,
                0xebae_bc4c_820d_574e,
                0x1886_5e12_d93f_d845,
            ]),
            c1: Fq::from_raw_unchecked([
                0x7d82_8664_baf4_f566,
                0xd17e_6639_96ec_7339,
                0x679e_ad55_cb40_78d0,
                0xfe3b_2260_e001_ec28,
                0x3059_93d0_43d9_1b68,
                0x0626_f03c_0489_b72d,
            ]),
        };

        assert_eq!(a.sqrt().unwrap().square(), a);

        // b = 5, which is a generator of the p - 1 order
        // multiplicative subgroup
        let b = Fq2 {
            c0: Fq::from_raw_unchecked([
                0x6631_0000_0010_5545,
                0x2114_0040_0eec_000d,
                0x3fa7_af30_c820_e316,
                0xc52a_8b8d_6387_695d,
                0x9fb4_e61d_1e83_eac5,
                0x005c_b922_afe8_4dc7,
            ]),
            c1: Fq::zero(),
        };

        assert_eq!(b.sqrt().unwrap().square(), b);

        // c = 25, which is a generator of the (p - 1) / 2 order
        // multiplicative subgroup
        let c = Fq2 {
            c0: Fq::from_raw_unchecked([
                0x44f6_0000_0051_ffae,
                0x86b8_0141_9948_0043,
                0xd715_9952_f1f3_794a,
                0x755d_6e3d_fe1f_fc12,
                0xd36c_d6db_5547_e905,
                0x02f8_c8ec_bf18_67bb,
            ]),
            c1: Fq::zero(),
        };

        assert_eq!(c.sqrt().unwrap().square(), c);

        // 2155129644831861015726826462986972654175647013268275306775721078997042729172900466542651176384766902407257452753362*u + 2796889544896299244102912275102369318775038861758288697415827248356648685135290329705805931514906495247464901062529
        // is nonsquare.
        assert!(bool::from(
            Fq2 {
                c0: Fq::from_raw_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                c1: Fq::from_raw_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            }
            .sqrt()
            .is_none()
        ));
    }

    #[test]
    fn test_frobenius_map() {
        let fq2_basic = Fq2 {
            c0: Fq::from_raw_unchecked([
                0x2d0078036923ffc7,
                0x11e59ea221a3b6d2,
                0x8b1a52e0a90f59ed,
                0xb966ce3bc2108b13,
                0xccc649c4b9532bf3,
                0xf8d295b2ded9dc,
            ]),
            c1: Fq::from_raw_unchecked([
                0x977df6efcdaee0db,
                0x946ae52d684fa7ed,
                0xbe203411c66fb3a5,
                0xb3f8afc0ee248cad,
                0x4e464dea5bcfd41e,
                0x12d1137b8a6a837,
            ]),
        };

        let mut fq2_test = fq2_basic;
        fq2_test.frobenius_map(0);
        assert_eq!(fq2_test, fq2_basic);

        let mut fq2_test_2 = fq2_basic;
        fq2_test_2.frobenius_map(1);
        assert_eq!(
            fq2_test_2,
            Fq2 {
                c0: Fq::from_raw_unchecked([
                    0x2d0078036923ffc7,
                    0x11e59ea221a3b6d2,
                    0x8b1a52e0a90f59ed,
                    0xb966ce3bc2108b13,
                    0xccc649c4b9532bf3,
                    0xf8d295b2ded9dc
                ]),
                c1: Fq::from_raw_unchecked([
                    0x228109103250c9d0,
                    0x8a411ad149045812,
                    0xa9109e8f3041427e,
                    0xb07e9bc405608611,
                    0xfcd559cbe77bd8b8,
                    0x18d400b280d93e62
                ]),
            }
        );

        let mut fq2_test_3 = fq2_basic;
        fq2_test_3.frobenius_map(1);
        fq2_test_3.frobenius_map(1);
        assert_eq!(fq2_test_3, fq2_basic);

        let mut fq2_test_4 = fq2_basic;
        fq2_test_4.frobenius_map(2);
        assert_eq!(fq2_test_4, fq2_basic);
    }

    // #[test]
    // fn test_frobenius_map_conjugate() {
    //     let fq2_basic = Fq2 {
    //         c0: Fq::from_raw_unchecked([
    //             0x2d0078036923ffc7,
    //             0x11e59ea221a3b6d2,
    //             0x8b1a52e0a90f59ed,
    //             0xb966ce3bc2108b13,
    //             0xccc649c4b9532bf3,
    //             0xf8d295b2ded9dc,
    //         ]),
    //         c1: Fq::from_raw_unchecked([
    //             0x977df6efcdaee0db,
    //             0x946ae52d684fa7ed,
    //             0xbe203411c66fb3a5,
    //             0xb3f8afc0ee248cad,
    //             0x4e464dea5bcfd41e,
    //             0x12d1137b8a6a837,
    //         ]),
    //     };

    //     let mut fq2_test_2 = fq2_basic;
    //     fq2_test_2.frobenius_map_conjugate();
    //     assert_eq!(
    //         fq2_test_2,
    //         Fq2 {
    //             c0: Fq::from_raw_unchecked([
    //                 0x2d0078036923ffc7,
    //                 0x11e59ea221a3b6d2,
    //                 0x8b1a52e0a90f59ed,
    //                 0xb966ce3bc2108b13,
    //                 0xccc649c4b9532bf3,
    //                 0xf8d295b2ded9dc
    //             ]),
    //             c1: Fq::from_raw_unchecked([
    //                 0x228109103250c9d0,
    //                 0x8a411ad149045812,
    //                 0xa9109e8f3041427e,
    //                 0xb07e9bc405608611,
    //                 0xfcd559cbe77bd8b8,
    //                 0x18d400b280d93e62
    //             ]),
    //         }
    //     );

    //     let mut fq2_test_3 = fq2_basic;
    //     fq2_test_3.frobenius_map_conjugate();
    //     fq2_test_3.frobenius_map_conjugate();
    //     assert_eq!(fq2_test_3, fq2_basic);
    // }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fq2>("fq2".to_string());
    }

    #[test]
    fn test_serialization() {
        crate::tests::field::random_serialization_test::<Fq2>("fq2".to_string());
    }
}
