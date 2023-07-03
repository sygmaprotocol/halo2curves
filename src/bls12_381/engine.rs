#![allow(clippy::suspicious_arithmetic_impl)]
use crate::bls12_381::curve::*;
use crate::bls12_381::fq12::*;
use crate::bls12_381::fq2::*;
use crate::bls12_381::fq6::*;
use crate::bls12_381::fr::*;
use crate::pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};
use core::borrow::Borrow;
use core::iter::Sum;
use core::ops::{Add, Mul, MulAssign, Neg, Sub};
use ff::{Field, PrimeField};
use group::cofactor::CofactorCurveAffine;
use group::Group;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

pub const BLS_X: u64 = 0xd201_0000_0001_0000;
pub const BLS_X_IS_NEGATIVE: bool = true;

impl PairingCurveAffine for G1Affine {
    type Pair = G2Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        pairing(self, other)
    }
}

impl PairingCurveAffine for G2Affine {
    type Pair = G1Affine;
    type PairingResult = Gt;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        pairing(other, self)
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct Gt(pub(crate) Fq12);

impl std::fmt::Display for Gt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl ConstantTimeEq for Gt {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl ConditionallySelectable for Gt {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Gt(Fq12::conditional_select(&a.0, &b.0, choice))
    }
}

impl Eq for Gt {}
impl PartialEq for Gt {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl Gt {
    /// Returns the group identity, which is $1$.
    pub fn identity() -> Gt {
        Gt(Fq12::one())
    }

    /// Doubles this group element.
    pub fn double(&self) -> Gt {
        Gt(self.0.square())
    }
}

impl<'a> Neg for &'a Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        // The element is unitary, so we just conjugate.
        let mut u = self.0;
        u.conjugate();
        Gt(u)
    }
}

impl Neg for Gt {
    type Output = Gt;

    #[inline]
    fn neg(self) -> Gt {
        -&self
    }
}

impl<'a, 'b> Add<&'b Gt> for &'a Gt {
    type Output = Gt;

    #[inline]
    fn add(self, rhs: &'b Gt) -> Gt {
        Gt(self.0 * rhs.0)
    }
}

impl<'a, 'b> Sub<&'b Gt> for &'a Gt {
    type Output = Gt;

    #[inline]
    fn sub(self, rhs: &'b Gt) -> Gt {
        self + (-rhs)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Gt {
    type Output = Gt;

    fn mul(self, other: &'b Fr) -> Self::Output {
        let mut acc = Gt::identity();

        for bit in other
            .to_repr()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
            .skip(1)
        {
            acc = acc.double();
            acc = Gt::conditional_select(&acc, &(acc + self), bit);
        }

        acc
    }
}

use crate::{
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Gt, Gt);
impl_binops_multiplicative!(Gt, Fr);

impl<T> Sum<T> for Gt
where
    T: Borrow<Gt>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl Group for Gt {
    type Scalar = Fr;

    fn random(_: impl RngCore) -> Self {
        unimplemented!();
    }

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        unimplemented!();
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Self::identity())
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }
}

#[derive(Clone, Debug)]
pub struct G2Prepared {
    pub(crate) coeffs: Vec<(Fq2, Fq2, Fq2)>,
    pub(crate) infinity: bool,
}

impl G2Prepared {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl From<G2Affine> for G2Prepared {
    fn from(q: G2Affine) -> G2Prepared {
        struct Adder {
            cur: G2,
            base: G2Affine,
            coeffs: Vec<(Fq2, Fq2, Fq2)>,
        }

        impl MillerLoopDriver for Adder {
            type Output = ();

            fn doubling_step(&mut self, _: Self::Output) -> Self::Output {
                let coeffs = doubling_step(&mut self.cur);
                self.coeffs.push(coeffs);
            }
            fn addition_step(&mut self, _: Self::Output) -> Self::Output {
                let coeffs = addition_step(&mut self.cur, &self.base);
                self.coeffs.push(coeffs);
            }
            fn square_output(_: Self::Output) -> Self::Output {}
            fn conjugate(_: Self::Output) -> Self::Output {}
            fn one() -> Self::Output {}
        }

        let is_identity = q.is_identity();
        let q = G2Affine::conditional_select(&q, &G2Affine::generator(), is_identity);

        let mut adder = Adder {
            cur: G2::from(q),
            base: q,
            coeffs: Vec::with_capacity(68),
        };

        miller_loop_bls12_381(&mut adder);

        assert_eq!(adder.coeffs.len(), 68);

        G2Prepared {
            infinity: is_identity.into(),
            coeffs: adder.coeffs,
        }
    }
}

impl MillerLoopResult for Gt {
    type Gt = Self;
    fn final_exponentiation(&self) -> Gt {
        fn exp_by_x(f: &mut Fq12) {
            let x = BLS_X;
            let mut res = Fq12::one();
            for i in (0..64).rev() {
                res.cyclotomic_square();
                if ((x >> i) & 1) == 1 {
                    res.mul_assign(f);
                }
            }
            *f = res;
        }

        let r = self.0;
        let mut f1 = self.0;
        f1.conjugate();

        Gt(r.invert()
            .map(|mut f2| {
                let mut r = f1;
                r.mul_assign(&f2);
                f2 = r;
                r.frobenius_map(2);
                r.mul_assign(&f2);

                let mut fp = r;
                fp.frobenius_map(1);

                let mut fp2 = r;
                fp2.frobenius_map(2);
                let mut fp3 = fp2;
                fp3.frobenius_map(1);

                let mut fu = r;
                exp_by_x(&mut fu);

                let mut fu2 = fu;
                exp_by_x(&mut fu2);

                let mut fu3 = fu2;
                exp_by_x(&mut fu3);

                let mut y3 = fu;
                y3.frobenius_map(1);

                let mut fu2p = fu2;
                fu2p.frobenius_map(1);

                let mut fu3p = fu3;
                fu3p.frobenius_map(1);

                let mut y2 = fu2;
                y2.frobenius_map(2);

                let mut y0 = fp;
                y0.mul_assign(&fp2);
                y0.mul_assign(&fp3);

                let mut y1 = r;
                y1.conjugate();

                let mut y5 = fu2;
                y5.conjugate();

                y3.conjugate();

                let mut y4 = fu;
                y4.mul_assign(&fu2p);
                y4.conjugate();

                let mut y6 = fu3;
                y6.mul_assign(&fu3p);
                y6.conjugate();

                y6.cyclotomic_square();
                y6.mul_assign(&y4);
                y6.mul_assign(&y5);

                let mut t1 = y3;
                t1.mul_assign(&y5);
                t1.mul_assign(&y6);

                y6.mul_assign(&y2);

                t1.cyclotomic_square();
                t1.mul_assign(&y6);
                t1.cyclotomic_square();

                let mut t0 = t1;
                t0.mul_assign(&y1);

                t1.mul_assign(&y0);

                t0.cyclotomic_square();
                t0.mul_assign(&t1);

                t0
            })
            .unwrap())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MillerLoopResultBls12381(pub(crate) Fq12);

impl Default for MillerLoopResultBls12381 {
    fn default() -> Self {
        MillerLoopResultBls12381(Fq12::one())
    }
}

impl ConditionallySelectable for MillerLoopResultBls12381 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        MillerLoopResultBls12381(Fq12::conditional_select(&a.0, &b.0, choice))
    }
}

impl MillerLoopResultBls12381 {
    /// This performs a "final exponentiation" routine to convert the result
    /// of a Miller loop into an element of `Gt` with help of efficient squaring
    /// operation in the so-called `cyclotomic subgroup` of `Fq6` so that
    /// it can be compared with other elements of `Gt`.
    pub fn final_exponentiation_bls12_381(&self) -> Gt {
        #[must_use]
        fn fp4_square(a: Fq2, b: Fq2) -> (Fq2, Fq2) {
            let t0 = a.square();
            let t1 = b.square();
            let mut t2 = t1.mul_by_nonresidue_bls12_381();
            let c0 = t2 + t0;
            t2 = a + b;
            t2 = t2.square();
            t2 -= t0;
            let c1 = t2 - t1;

            (c0, c1)
        }

        // Adaptation of Algorithm 5.5.4, Guide to Pairing-Based Cryptography
        // Faster Squaring in the Cyclotomic Subgroup of Sixth Degree Extensions
        // https://eprint.iacr.org/2009/565.pdf
        #[must_use]
        fn cyclotomic_square(f: Fq12) -> Fq12 {
            let mut z0 = f.c0.c0;
            let mut z4 = f.c0.c1;
            let mut z3 = f.c0.c2;
            let mut z2 = f.c1.c0;
            let mut z1 = f.c1.c1;
            let mut z5 = f.c1.c2;

            let (t0, t1) = fp4_square(z0, z1);

            // For A
            z0 = t0 - z0;
            z0 = z0 + z0 + t0;

            z1 = t1 + z1;
            z1 = z1 + z1 + t1;

            let (mut t0, t1) = fp4_square(z2, z3);
            let (t2, t3) = fp4_square(z4, z5);

            // For C
            z4 = t0 - z4;
            z4 = z4 + z4 + t0;

            z5 = t1 + z5;
            z5 = z5 + z5 + t1;

            // For B
            t0 = t3.mul_by_nonresidue_bls12_381();
            z2 = t0 + z2;
            z2 = z2 + z2 + t0;

            z3 = t2 - z3;
            z3 = z3 + z3 + t2;

            Fq12 {
                c0: Fq6 {
                    c0: z0,
                    c1: z4,
                    c2: z3,
                },
                c1: Fq6 {
                    c0: z2,
                    c1: z1,
                    c2: z5,
                },
            }
        }

        #[must_use]
        fn cycolotomic_exp(f: Fq12) -> Fq12 {
            let x = BLS_X;
            let mut tmp = Fq12::one();
            let mut found_one = false;
            for i in (0..64).rev().map(|b| ((x >> b) & 1) == 1) {
                if found_one {
                    tmp = cyclotomic_square(tmp)
                } else {
                    found_one = i;
                }

                if i {
                    tmp *= f;
                }
            }

            tmp.conjugate_ret()
        }

        let mut f = self.0;
        let mut t0 = f;
        t0.frobenius_map(6);

        Gt(f.invert()
            .map(|mut t1| {
                let mut t2 = t0 * t1;
                t1 = t2;

                let mut t2_temp = t2;
                t2_temp.frobenius_map(2);
                t2 = t2_temp;

                t2 *= t1;
                t1 = cyclotomic_square(t2).conjugate_ret();
                let mut t3 = cycolotomic_exp(t2);
                let mut t4 = cyclotomic_square(t3);
                let mut t5 = t1 * t3;
                t1 = cycolotomic_exp(t5);
                t0 = cycolotomic_exp(t1);
                let mut t6 = cycolotomic_exp(t0);
                t6 *= t4;
                t4 = cycolotomic_exp(t6);
                t5 = t5.conjugate_ret();
                t4 *= t5 * t2;
                t5 = t2.conjugate_ret();
                t1 *= t2;

                let mut t1_temp = t1;
                t1_temp.frobenius_map(3);
                t1 = t1_temp;

                t6 *= t5;

                let mut t6_temp = t6;
                t6_temp.frobenius_map(1);
                t6 = t6_temp;

                t3 *= t0;

                let mut t3_temp = t3;
                t3_temp.frobenius_map(2);
                t3 = t3_temp;

                t3 *= t1;
                t3 *= t6;
                f = t3 * t4;

                f
            })
            // We unwrap() because `MillerLoopResult` can only be constructed
            // by a function within this crate, and we uphold the invariant
            // that the enclosed value is nonzero.
            .unwrap())
    }
}

pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Prepared)]) -> Gt {
    let mut pairs = vec![];
    for &(p, q) in terms {
        if !bool::from(p.is_identity()) && !q.is_zero() {
            pairs.push((p, q.coeffs.iter()));
        }
    }

    // Final steps of the line function on prepared coefficients
    fn ell(f: &mut Fq12, coeffs: &(Fq2, Fq2, Fq2), p: &G1Affine) {
        let mut c0 = coeffs.0;
        let mut c1 = coeffs.1;

        c0.c0.mul_assign(&p.y);
        c0.c1.mul_assign(&p.y);

        c1.c0.mul_assign(&p.x);
        c1.c1.mul_assign(&p.x);

        // Sparse multiplication in Fq12
        f.mul_by_034(&c0, &c1, &coeffs.2);
    }

    let mut f = Fq12::one();

    let mut found_one = false;
    for i in BitIterator::new(&[BLS_X >> 1]) {
        if !found_one {
            found_one = i;
            continue;
        }

        for &mut (p, ref mut coeffs) in &mut pairs {
            ell(&mut f, coeffs.next().unwrap(), p);
        }

        if i {
            for &mut (p, ref mut coeffs) in &mut pairs {
                ell(&mut f, coeffs.next().unwrap(), p);
            }
        }

        f.square();
    }

    for &mut (p, ref mut coeffs) in &mut pairs {
        ell(&mut f, coeffs.next().unwrap(), p);
    }

    if BLS_X_IS_NEGATIVE {
        f.conjugate();
    }

    Gt(f)
}

/// Computes $$\sum_{i=1}^n \textbf{ML}(a_i, b_i)$$ given a series of terms
/// $$(a_1, b_1), (a_2, b_2), ..., (a_n, b_n).$$
///
/// Requires the `alloc` and `pairing` crate features to be enabled.
pub fn multi_miller_loop_bls12_381(terms: &[(&G1Affine, &G2Prepared)]) -> MillerLoopResultBls12381 {
    struct Adder<'a, 'b, 'c> {
        terms: &'c [(&'a G1Affine, &'b G2Prepared)],
        index: usize,
    }

    impl<'a, 'b, 'c> MillerLoopDriver for Adder<'a, 'b, 'c> {
        type Output = Fq12;

        fn doubling_step(&mut self, mut f: Self::Output) -> Self::Output {
            let index = self.index;
            for term in self.terms {
                let either_identity = term.0.is_identity() | Choice::from(term.1.infinity as u8);

                let new_f = ell(f, &term.1.coeffs[index], term.0);
                f = Fq12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }
        fn addition_step(&mut self, mut f: Self::Output) -> Self::Output {
            let index = self.index;
            for term in self.terms {
                let either_identity = term.0.is_identity() | Choice::from(term.1.infinity as u8);

                let new_f = ell(f, &term.1.coeffs[index], term.0);
                f = Fq12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }
        fn square_output(f: Self::Output) -> Self::Output {
            f.square()
        }
        fn conjugate(f: Self::Output) -> Self::Output {
            f.conjugate_ret()
        }
        fn one() -> Self::Output {
            Fq12::one()
        }
    }

    let mut adder = Adder { terms, index: 0 };

    let tmp = miller_loop_bls12_381(&mut adder);

    MillerLoopResultBls12381(tmp)
}

pub fn pairing(g1: &G1Affine, g2: &G2Affine) -> Gt {
    let g2 = G2Prepared::from(*g2);
    let terms: &[(&G1Affine, &G2Prepared)] = &[(g1, &g2)];
    let u = multi_miller_loop(terms);
    u.final_exponentiation()
}

pub fn pairing_bls12_381(p: &G1Affine, q: &G2Affine) -> Gt {
    struct Adder {
        cur: G2,
        base: G2Affine,
        p: G1Affine,
    }

    impl MillerLoopDriver for Adder {
        type Output = Fq12;

        fn doubling_step(&mut self, f: Self::Output) -> Self::Output {
            let coeffs = doubling_step(&mut self.cur);
            ell(f, &coeffs, &self.p)
        }
        fn addition_step(&mut self, f: Self::Output) -> Self::Output {
            let coeffs = addition_step(&mut self.cur, &self.base);
            ell(f, &coeffs, &self.p)
        }
        fn square_output(f: Self::Output) -> Self::Output {
            f.square()
        }
        fn conjugate(f: Self::Output) -> Self::Output {
            f.conjugate_ret()
        }
        fn one() -> Self::Output {
            Fq12::one()
        }
    }

    let either_identity = p.is_identity() | q.is_identity();
    let p = G1Affine::conditional_select(p, &G1Affine::generator(), either_identity);
    let q = G2Affine::conditional_select(q, &G2Affine::generator(), either_identity);

    let mut adder = Adder {
        cur: G2::from(q),
        base: q,
        p,
    };

    let tmp = miller_loop_bls12_381(&mut adder);
    let tmp = MillerLoopResultBls12381(Fq12::conditional_select(
        &tmp,
        &Fq12::one(),
        either_identity,
    ));
    tmp.final_exponentiation_bls12_381()
}

trait MillerLoopDriver {
    type Output;

    fn doubling_step(&mut self, f: Self::Output) -> Self::Output;
    fn addition_step(&mut self, f: Self::Output) -> Self::Output;
    fn square_output(f: Self::Output) -> Self::Output;
    fn conjugate(f: Self::Output) -> Self::Output;
    fn one() -> Self::Output;
}

/// This is a "generic" implementation of the Miller loop to avoid duplicating code
/// structure elsewhere; instead, we'll write concrete instantiations of
/// `MillerLoopDriver` for whatever purposes we need (such as caching modes).
fn miller_loop_bls12_381<D: MillerLoopDriver>(driver: &mut D) -> D::Output {
    let mut f = D::one();

    let mut found_one = false;
    for i in (0..64).rev().map(|b| (((BLS_X >> 1) >> b) & 1) == 1) {
        if !found_one {
            found_one = i;
            continue;
        }

        f = driver.doubling_step(f);

        if i {
            f = driver.addition_step(f);
        }

        f = D::square_output(f);
    }

    f = driver.doubling_step(f);

    if BLS_X_IS_NEGATIVE {
        f = D::conjugate(f);
    }

    f
}

fn ell(f: Fq12, coeffs: &(Fq2, Fq2, Fq2), p: &G1Affine) -> Fq12 {
    let mut c0 = coeffs.0;
    let mut c1 = coeffs.1;

    c0.c0 *= p.y;
    c0.c1 *= p.y;

    c1.c0 *= p.x;
    c1.c1 *= p.x;

    f.mul_by_014_bls12_381(&coeffs.2, &c1, &c0)
}

fn addition_step(r: &mut G2, q: &G2Affine) -> (Fq2, Fq2, Fq2) {
    // Adaptation of Algorithm 27, https://eprint.iacr.org/2010/354.pdf
    let zsquared = r.z.square();
    let ysquared = q.y.square();
    let t0 = zsquared * q.x;
    let t1 = ((q.y + r.z).square() - ysquared - zsquared) * zsquared;
    let t2 = t0 - r.x;
    let t3 = t2.square();
    let t4 = t3 + t3;
    let t4 = t4 + t4;
    let t5 = t4 * t2;
    let t6 = t1 - r.y - r.y;
    let t9 = t6 * q.x;
    let t7 = t4 * r.x;
    r.x = t6.square() - t5 - t7 - t7;
    r.z = (r.z + t2).square() - zsquared - t3;
    let t10 = q.y + r.z;
    let t8 = (t7 - r.x) * t6;
    let t0 = r.y * t5;
    let t0 = t0 + t0;
    r.y = t8 - t0;
    let t10 = t10.square() - ysquared;
    let ztsquared = r.z.square();
    let t10 = t10 - ztsquared;
    let t9 = t9 + t9 - t10;
    let t10 = r.z + r.z;
    let t6 = -t6;
    let t1 = t6 + t6;

    (t10, t1, t9)
}

fn doubling_step(r: &mut G2) -> (Fq2, Fq2, Fq2) {
    // Adaptation of Algorithm 26, https://eprint.iacr.org/2010/354.pdf
    let tmp0 = r.x.square();
    let tmp1 = r.y.square();
    let tmp2 = tmp1.square();
    let tmp3 = (tmp1 + r.x).square() - tmp0 - tmp2;
    let tmp3 = tmp3 + tmp3;
    let tmp4 = tmp0 + tmp0 + tmp0;
    let tmp6 = r.x + tmp4;
    let tmp5 = tmp4.square();
    let zsquared = r.z.square();
    r.x = tmp5 - tmp3 - tmp3;
    r.z = (r.z + r.y).square() - tmp1 - zsquared;
    r.y = (tmp3 - r.x) * tmp4;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    r.y -= tmp2;
    let tmp3 = tmp4 * zsquared;
    let tmp3 = tmp3 + tmp3;
    let tmp3 = -tmp3;
    let tmp6 = tmp6.square() - tmp0 - tmp5;
    let tmp1 = tmp1 + tmp1;
    let tmp1 = tmp1 + tmp1;
    let tmp6 = tmp6 - tmp1;
    let tmp0 = r.z * zsquared;
    let tmp0 = tmp0 + tmp0;

    (tmp0, tmp3, tmp6)
}

#[derive(Clone, Debug)]
pub struct Bls12_381;

impl Engine for Bls12_381 {
    type Scalar = Fr;
    type G1 = G1;
    type G1Affine = G1Affine;
    type G2 = G2;
    type G2Affine = G2Affine;
    type Gt = Gt;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        pairing(p, q)
    }
}

impl MultiMillerLoop for Bls12_381 {
    type G2Prepared = G2Prepared;
    type Result = Gt;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        multi_miller_loop(terms)
    }
}

#[derive(Debug)]
pub struct BitIterator<E> {
    t: E,
    n: usize,
}

impl<E: AsRef<[u64]>> BitIterator<E> {
    pub fn new(t: E) -> Self {
        let n = t.as_ref().len() * 64;

        BitIterator { t, n }
    }
}

impl<E: AsRef<[u64]>> Iterator for BitIterator<E> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            let part = self.n / 64;
            let bit = self.n - (64 * part);

            Some(self.t.as_ref()[part] & (1 << bit) > 0)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bls12_381::fq::*;
    use crate::bls12_381::Fq6;

    use super::*;
    use pasta_curves::arithmetic::CurveExt;
    use pretty_assertions::assert_eq;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_double_g1() {
        {
            let tmp = G1::identity().double();
            assert!(bool::from(tmp.is_identity()));
            assert!(bool::from(tmp.is_on_curve()));
        }
        {
            let tmp = G1::generator().double();
            assert!(!bool::from(tmp.is_identity()));
            assert!(bool::from(tmp.is_on_curve()));

            assert_eq!(
                G1Affine::from(tmp),
                G1Affine {
                    x: Fq::from_raw_unchecked([
                        0x53e9_78ce_58a9_ba3c,
                        0x3ea0_583c_4f3d_65f9,
                        0x4d20_bb47_f001_2960,
                        0xa54c_664a_e5b2_b5d9,
                        0x26b5_52a3_9d7e_b21f,
                        0x0008_895d_26e6_8785,
                    ]),
                    y: Fq::from_raw_unchecked([
                        0x7011_0b32_9829_3940,
                        0xda33_c539_3f1f_6afc,
                        0xb86e_dfd1_6a5a_a785,
                        0xaec6_d1c9_e7b1_c895,
                        0x25cf_c2b5_22d1_1720,
                        0x0636_1c83_f8d0_9b15,
                    ]),
                    infinity: Choice::from(0u8),
                }
            );
        }
    }

    #[test]
    fn test_double_g2() {
        {
            let tmp = G2::identity().double();
            assert!(bool::from(tmp.is_identity()));
            assert!(bool::from(tmp.is_on_curve()));
        }
        {
            let tmp = G2::generator().double();
            assert!(!bool::from(tmp.is_identity()));
            assert!(bool::from(tmp.is_on_curve()));

            assert_eq!(
                G2Affine::from(tmp),
                G2Affine {
                    x: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0xe9d9_e2da_9620_f98b,
                            0x54f1_1993_46b9_7f36,
                            0x3db3_b820_376b_ed27,
                            0xcfdb_31c9_b0b6_4f4c,
                            0x41d7_c127_8635_4493,
                            0x0571_0794_c255_c064,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0xd6c1_d3ca_6ea0_d06e,
                            0xda0c_bd90_5595_489f,
                            0x4f53_52d4_3479_221d,
                            0x8ade_5d73_6f8c_97e0,
                            0x48cc_8433_925e_f70e,
                            0x08d7_ea71_ea91_ef81,
                        ]),
                    },
                    y: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x15ba_26eb_4b0d_186f,
                            0x0d08_6d64_b7e9_e01e,
                            0xc8b8_48dd_652f_4c78,
                            0xeecf_46a6_123b_ae4f,
                            0x255e_8dd8_b6dc_812a,
                            0x1641_42af_21dc_f93f,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0xf9b4_a1a8_9598_4db4,
                            0xd417_b114_cccf_f748,
                            0x6856_301f_c89f_086e,
                            0x41c7_7787_8931_e3da,
                            0x3556_b155_066a_2105,
                            0x00ac_f7d3_25cb_89cf,
                        ]),
                    },
                    infinity: Choice::from(0u8),
                }
            );
        }
    }

    // TODO Generalize pairing (from BN254) with BLS12-381
    // #[test]
    // fn test_pairing_1() {
    //     let g1 = G1::generator();
    //     let mut g2 = G2::generator();
    //     g2 = g2.double();
    //     let g1_affine = G1Affine::from(g1);
    //     let g2_affine = G2Affine::from(g2);
    //     let pair12 = Bls12_381::pairing(&g1_affine, &g2_affine);

    //     let mut g3 = G1::generator();
    //     let g4 = G2::generator();
    //     g3 = g3.double();
    //     let pair21 = Bls12_381::pairing(&G1Affine::from(g3), &G2Affine::from(g4));

    //     assert_eq!(pair12, pair21);
    // }

    #[test]
    fn test_pairing_1_bls12_381() {
        let g1 = G1::generator();
        let mut g2 = G2::generator();
        g2 = g2.double();
        let pair12 = pairing_bls12_381(&G1Affine::from(g1), &G2Affine::from(g2));

        let mut g3 = G1::generator();
        let g4 = G2::generator();
        g3 = g3.double();
        let pair21 = pairing_bls12_381(&G1Affine::from(g3), &G2Affine::from(g4));

        assert_eq!(pair12, pair21);
    }

    // TODO Generalize pairing (from BN254) with BLS12-381
    // #[test]
    // fn test_pairing_2() {
    //     let g1 = G1::generator();
    //     let mut g2 = G2::generator();
    //     g2 = g2.double().double();
    //     let pair12 = Bls12_381::pairing(&G1Affine::from(g1), &G2Affine::from(g2));

    //     let mut g1 = G1::generator();
    //     let mut g2 = G2::generator();
    //     g1 = g1.double();
    //     g2 = g2.double();
    //     let pair21 = Bls12_381::pairing(&G1Affine::from(g1), &G2Affine::from(g2));

    //     assert_eq!(pair12, pair21);
    // }

    #[test]
    fn test_pairing_2_bls12_381() {
        let g1 = G1::generator();
        let mut g2 = G2::generator();
        g2 = g2.double().double();
        let pair12 = pairing_bls12_381(&G1Affine::from(g1), &G2Affine::from(g2));

        let mut g1 = G1::generator();
        let mut g2 = G2::generator();
        g1 = g1.double();
        g2 = g2.double();
        let pair21 = pairing_bls12_381(&G1Affine::from(g1), &G2Affine::from(g2));

        assert_eq!(pair12, pair21);
    }

    #[test]
    fn test_pairing_3() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1000 {
            let a = Fr::random(&mut rng);
            let b = Fr::random(&mut rng);

            let mut g1 = G1::generator();
            g1.mul_assign(a);

            let mut g2 = G2::generator();
            g1.mul_assign(b);

            let pair_ab = Bls12_381::pairing(&G1Affine::from(g1), &G2Affine::from(g2));

            g1 = G1::generator();
            g1.mul_assign(b);

            g2 = G2::generator();
            g1.mul_assign(a);

            let pair_ba = Bls12_381::pairing(&G1Affine::from(g1), &G2Affine::from(g2));

            assert_eq!(pair_ab, pair_ba);
        }
    }

    #[test]
    fn test_pairing_3_bls12_381() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1000 {
            let a = Fr::random(&mut rng);
            let b = Fr::random(&mut rng);

            let mut g1 = G1::generator();
            g1.mul_assign(a);

            let mut g2 = G2::generator();
            g1.mul_assign(b);

            let pair_ab = pairing_bls12_381(&G1Affine::from(g1), &G2Affine::from(g2));

            g1 = G1::generator();
            g1.mul_assign(b);

            g2 = G2::generator();
            g1.mul_assign(a);

            let pair_ba = pairing_bls12_381(&G1Affine::from(g1), &G2Affine::from(g2));

            assert_eq!(pair_ab, pair_ba);
        }
    }

    // TODO Generalize pairing (from BN254) with BLS12-381
    // #[test]
    // fn test_pairing_against_relic() {
    //     let a = G1Affine::generator();
    //     let b = G2Affine::generator();

    //     let res = Bls12_381::pairing(&a, &b);
    //     println!("res: {:#?}", res);
    //     let prep = G2Prepared::from(b);
    //     let res_miller_loop = multi_miller_loop(&[(&a, &prep)]);
    //     println!("res_miller_loop: {:#?}", res_miller_loop);
    //     assert_eq!(res, res_miller_loop.final_exponentiation());

    //     assert_eq!(
    //         res.0,
    //         Fq12 {
    //             c0: Fq6 {
    //                 c0: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0x1972_e433_a01f_85c5,
    //                         0x97d3_2b76_fd77_2538,
    //                         0xc8ce_546f_c96b_cdf9,
    //                         0xcef6_3e73_66d4_0614,
    //                         0xa611_3427_8184_3780,
    //                         0x13f3_448a_3fc6_d825,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0xd263_31b0_2e9d_6995,
    //                         0x9d68_a482_f779_7e7d,
    //                         0x9c9b_2924_8d39_ea92,
    //                         0xf480_1ca2_e131_07aa,
    //                         0xa16c_0732_bdbc_b066,
    //                         0x083c_a4af_ba36_0478,
    //                     ])
    //                 },
    //                 c1: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0x59e2_61db_0916_b641,
    //                         0x2716_b6f4_b23e_960d,
    //                         0xc8e5_5b10_a0bd_9c45,
    //                         0x0bdb_0bd9_9c4d_eda8,
    //                         0x8cf8_9ebf_57fd_aac5,
    //                         0x12d6_b792_9e77_7a5e,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0x5fc8_5188_b0e1_5f35,
    //                         0x34a0_6e3a_8f09_6365,
    //                         0xdb31_26a6_e02a_d62c,
    //                         0xfc6f_5aa9_7d9a_990b,
    //                         0xa12f_55f5_eb89_c210,
    //                         0x1723_703a_926f_8889,
    //                     ])
    //                 },
    //                 c2: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0x9358_8f29_7182_8778,
    //                         0x43f6_5b86_11ab_7585,
    //                         0x3183_aaf5_ec27_9fdf,
    //                         0xfa73_d7e1_8ac9_9df6,
    //                         0x64e1_76a6_a64c_99b0,
    //                         0x179f_a78c_5838_8f1f,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0x672a_0a11_ca2a_ef12,
    //                         0x0d11_b9b5_2aa3_f16b,
    //                         0xa444_12d0_699d_056e,
    //                         0xc01d_0177_221a_5ba5,
    //                         0x66e0_cede_6c73_5529,
    //                         0x05f5_a71e_9fdd_c339,
    //                     ])
    //                 }
    //             },
    //             c1: Fq6 {
    //                 c0: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0xd30a_88a1_b062_c679,
    //                         0x5ac5_6a5d_35fc_8304,
    //                         0xd0c8_34a6_a81f_290d,
    //                         0xcd54_30c2_da37_07c7,
    //                         0xf0c2_7ff7_8050_0af0,
    //                         0x0924_5da6_e2d7_2eae,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0x9f2e_0676_791b_5156,
    //                         0xe2d1_c823_4918_fe13,
    //                         0x4c9e_459f_3c56_1bf4,
    //                         0xa3e8_5e53_b9d3_e3c1,
    //                         0x820a_121e_21a7_0020,
    //                         0x15af_6183_41c5_9acc,
    //                     ])
    //                 },
    //                 c1: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0x7c95_658c_2499_3ab1,
    //                         0x73eb_3872_1ca8_86b9,
    //                         0x5256_d749_4774_34bc,
    //                         0x8ba4_1902_ea50_4a8b,
    //                         0x04a3_d3f8_0c86_ce6d,
    //                         0x18a6_4a87_fb68_6eaa,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0xbb83_e71b_b920_cf26,
    //                         0x2a52_77ac_92a7_3945,
    //                         0xfc0e_e59f_94f0_46a0,
    //                         0x7158_cdf3_7860_58f7,
    //                         0x7cc1_061b_82f9_45f6,
    //                         0x03f8_47aa_9fdb_e567,
    //                     ])
    //                 },
    //                 c2: Fq2 {
    //                     c0: Fq::from_raw_unchecked([
    //                         0x8078_dba5_6134_e657,
    //                         0x1cd7_ec9a_4399_8a6e,
    //                         0xb1aa_599a_1a99_3766,
    //                         0xc9a0_f62f_0842_ee44,
    //                         0x8e15_9be3_b605_dffa,
    //                         0x0c86_ba0d_4af1_3fc2,
    //                     ]),
    //                     c1: Fq::from_raw_unchecked([
    //                         0xe80f_f2a0_6a52_ffb1,
    //                         0x7694_ca48_721a_906c,
    //                         0x7583_183e_03b0_8514,
    //                         0xf567_afdd_40ce_e4e2,
    //                         0x9a6d_96d2_e526_a5fc,
    //                         0x197e_9f49_861f_2242,
    //                     ])
    //                 }
    //             }
    //         }
    //     );
    // }

    #[test]
    fn test_pairing_against_relic_bls12_381() {
        let a = G1Affine::generator();
        let b = G2Affine::generator();

        let res = pairing_bls12_381(&a, &b);
        let prep = G2Prepared::from(b);
        let res_miller_loop = multi_miller_loop_bls12_381(&[(&a, &prep)]);
        assert_eq!(res, res_miller_loop.final_exponentiation_bls12_381());
        assert_eq!(
            res.0,
            Fq12 {
                c0: Fq6 {
                    c0: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x1972_e433_a01f_85c5,
                            0x97d3_2b76_fd77_2538,
                            0xc8ce_546f_c96b_cdf9,
                            0xcef6_3e73_66d4_0614,
                            0xa611_3427_8184_3780,
                            0x13f3_448a_3fc6_d825,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0xd263_31b0_2e9d_6995,
                            0x9d68_a482_f779_7e7d,
                            0x9c9b_2924_8d39_ea92,
                            0xf480_1ca2_e131_07aa,
                            0xa16c_0732_bdbc_b066,
                            0x083c_a4af_ba36_0478,
                        ])
                    },
                    c1: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x59e2_61db_0916_b641,
                            0x2716_b6f4_b23e_960d,
                            0xc8e5_5b10_a0bd_9c45,
                            0x0bdb_0bd9_9c4d_eda8,
                            0x8cf8_9ebf_57fd_aac5,
                            0x12d6_b792_9e77_7a5e,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0x5fc8_5188_b0e1_5f35,
                            0x34a0_6e3a_8f09_6365,
                            0xdb31_26a6_e02a_d62c,
                            0xfc6f_5aa9_7d9a_990b,
                            0xa12f_55f5_eb89_c210,
                            0x1723_703a_926f_8889,
                        ])
                    },
                    c2: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x9358_8f29_7182_8778,
                            0x43f6_5b86_11ab_7585,
                            0x3183_aaf5_ec27_9fdf,
                            0xfa73_d7e1_8ac9_9df6,
                            0x64e1_76a6_a64c_99b0,
                            0x179f_a78c_5838_8f1f,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0x672a_0a11_ca2a_ef12,
                            0x0d11_b9b5_2aa3_f16b,
                            0xa444_12d0_699d_056e,
                            0xc01d_0177_221a_5ba5,
                            0x66e0_cede_6c73_5529,
                            0x05f5_a71e_9fdd_c339,
                        ])
                    }
                },
                c1: Fq6 {
                    c0: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0xd30a_88a1_b062_c679,
                            0x5ac5_6a5d_35fc_8304,
                            0xd0c8_34a6_a81f_290d,
                            0xcd54_30c2_da37_07c7,
                            0xf0c2_7ff7_8050_0af0,
                            0x0924_5da6_e2d7_2eae,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0x9f2e_0676_791b_5156,
                            0xe2d1_c823_4918_fe13,
                            0x4c9e_459f_3c56_1bf4,
                            0xa3e8_5e53_b9d3_e3c1,
                            0x820a_121e_21a7_0020,
                            0x15af_6183_41c5_9acc,
                        ])
                    },
                    c1: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x7c95_658c_2499_3ab1,
                            0x73eb_3872_1ca8_86b9,
                            0x5256_d749_4774_34bc,
                            0x8ba4_1902_ea50_4a8b,
                            0x04a3_d3f8_0c86_ce6d,
                            0x18a6_4a87_fb68_6eaa,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0xbb83_e71b_b920_cf26,
                            0x2a52_77ac_92a7_3945,
                            0xfc0e_e59f_94f0_46a0,
                            0x7158_cdf3_7860_58f7,
                            0x7cc1_061b_82f9_45f6,
                            0x03f8_47aa_9fdb_e567,
                        ])
                    },
                    c2: Fq2 {
                        c0: Fq::from_raw_unchecked([
                            0x8078_dba5_6134_e657,
                            0x1cd7_ec9a_4399_8a6e,
                            0xb1aa_599a_1a99_3766,
                            0xc9a0_f62f_0842_ee44,
                            0x8e15_9be3_b605_dffa,
                            0x0c86_ba0d_4af1_3fc2,
                        ]),
                        c1: Fq::from_raw_unchecked([
                            0xe80f_f2a0_6a52_ffb1,
                            0x7694_ca48_721a_906c,
                            0x7583_183e_03b0_8514,
                            0xf567_afdd_40ce_e4e2,
                            0x9a6d_96d2_e526_a5fc,
                            0x197e_9f49_861f_2242,
                        ])
                    }
                }
            }
        );
    }

    // TODO Generalize pairing (from BN254) with BLS12-381
    // #[test]
    // fn random_bilinearity_tests() {
    //     let mut rng = XorShiftRng::from_seed([
    //         0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
    //         0xbc, 0xe5,
    //     ]);

    //     for _ in 0..1000 {
    //         let mut a = G1::generator();
    //         let ka = Fr::random(&mut rng);
    //         a.mul_assign(ka);

    //         let mut b = G2::generator();
    //         let kb = Fr::random(&mut rng);
    //         b.mul_assign(kb);

    //         let c = Fr::random(&mut rng);
    //         let d = Fr::random(&mut rng);

    //         let mut ac = a;
    //         ac.mul_assign(c);

    //         let mut ad = a;
    //         ad.mul_assign(d);

    //         let mut bc = b;
    //         bc.mul_assign(c);

    //         let mut bd = b;
    //         bd.mul_assign(d);

    //         let acbd = Bls12_381::pairing(&G1Affine::from(ac), &G2Affine::from(bd));
    //         let adbc = Bls12_381::pairing(&G1Affine::from(ad), &G2Affine::from(bc));

    //         let mut cd = c;
    //         cd.mul_assign(&d);

    //         cd *= Fr([1, 0, 0, 0]);

    //         let abcd = Gt(Bls12_381::pairing(&G1Affine::from(a), &G2Affine::from(b))
    //             .0
    //             .pow_vartime(cd.0));

    //         assert_eq!(acbd, adbc);
    //         assert_eq!(acbd, abcd);
    //     }
    // }

    #[test]
    fn random_bilinearity_tests_bls12_381() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut a = G1::generator();
            let ka = Fr::random(&mut rng);
            a.mul_assign(ka);

            let mut b = G2::generator();
            let kb = Fr::random(&mut rng);
            b.mul_assign(kb);

            let c = Fr::random(&mut rng);
            let d = Fr::random(&mut rng);

            let mut ac = a;
            ac.mul_assign(c);

            let mut ad = a;
            ad.mul_assign(d);

            let mut bc = b;
            bc.mul_assign(c);

            let mut bd = b;
            bd.mul_assign(d);

            let acbd = pairing_bls12_381(&G1Affine::from(ac), &G2Affine::from(bd));
            let adbc = pairing_bls12_381(&G1Affine::from(ad), &G2Affine::from(bc));

            let mut cd = c;
            cd.mul_assign(&d);

            cd *= Fr([1, 0, 0, 0]);

            let abcd = Gt(pairing_bls12_381(&G1Affine::from(a), &G2Affine::from(b))
                .0
                .pow_vartime(cd.0));

            assert_eq!(acbd, adbc);
            assert_eq!(acbd, abcd);
        }
    }

    // TODO Generalize pairing (from BN254) with BLS12-381
    // #[test]
    // fn test_bilinearity() {
    //     let a = Fr::from_raw([1, 2, 3, 4]).invert().unwrap().square();
    //     let b = Fr::from_raw([5, 6, 7, 8]).invert().unwrap().square();
    //     let c = a * b;

    //     let g = G1Affine::from(G1Affine::generator() * a);
    //     let h = G2Affine::from(G2Affine::generator() * b);
    //     let p = Bls12_381::pairing(&g, &h);

    //     assert!(p != Gt::identity());

    //     let expected = G1Affine::from(G1Affine::generator() * c);

    //     assert_eq!(p, Bls12_381::pairing(&expected, &G2Affine::generator()));
    //     assert_eq!(
    //         p,
    //         Bls12_381::pairing(&G1Affine::generator(), &G2Affine::generator()) * c
    //     );
    // }

    #[test]
    fn test_bilinearity_bls12_381() {
        let a = Fr::from_raw([1, 2, 3, 4]).invert().unwrap().square();
        let b = Fr::from_raw([5, 6, 7, 8]).invert().unwrap().square();
        let c = a * b;

        let g = G1Affine::from(G1Affine::generator() * a);
        let h = G2Affine::from(G2Affine::generator() * b);
        let p = pairing_bls12_381(&g, &h);

        assert!(p != Gt::identity());

        let expected = G1Affine::from(G1Affine::generator() * c);

        assert_eq!(p, pairing_bls12_381(&expected, &G2Affine::generator()));
        assert_eq!(
            p,
            pairing_bls12_381(&G1Affine::generator(), &G2Affine::generator()) * c
        );
    }

    #[test]
    pub fn engine_tests() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..10 {
            let a = G1Affine::from(G1::random(&mut rng));
            let b = G2Affine::from(G2::random(&mut rng));

            assert!(a.pairing_with(&b) == b.pairing_with(&a));
            assert!(a.pairing_with(&b) == Bls12_381::pairing(&a, &b));
        }

        for _ in 0..1000 {
            let z1 = G1Affine::identity();
            let z2 = G2Prepared::from(G2Affine::identity());

            let a = G1Affine::from(G1::random(&mut rng));
            let b = G2Prepared::from(G2Affine::from(G2::random(&mut rng)));
            let c = G1Affine::from(G1::random(&mut rng));
            let d = G2Prepared::from(G2Affine::from(G2::random(&mut rng)));

            assert_eq!(
                Fq12::one(),
                multi_miller_loop(&[(&z1, &b)]).final_exponentiation().0,
            );

            assert_eq!(
                Fq12::one(),
                multi_miller_loop(&[(&a, &z2)]).final_exponentiation().0,
            );

            assert_eq!(
                multi_miller_loop(&[(&z1, &b), (&c, &d)]).final_exponentiation(),
                multi_miller_loop(&[(&a, &z2), (&c, &d)]).final_exponentiation(),
            );

            assert_eq!(
                multi_miller_loop(&[(&a, &b), (&z1, &d)]).final_exponentiation(),
                multi_miller_loop(&[(&a, &b), (&c, &z2)]).final_exponentiation(),
            );
        }
    }

    #[test]
    pub fn engine_tests_bls12_381() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // for _ in 0..10 {
        //     let a = G1Affine::from(G1::random(&mut rng));
        //     let b = G2Affine::from(G2::random(&mut rng));

        //     assert!(a.pairing_with(&b) == b.pairing_with(&a));
        //     assert!(a.pairing_with(&b) == pairing_bls12_381(&a, &b));
        // }

        for _ in 0..1000 {
            let z1 = G1Affine::identity();
            let z2 = G2Prepared::from(G2Affine::identity());

            let a = G1Affine::from(G1::random(&mut rng));
            let b = G2Prepared::from(G2Affine::from(G2::random(&mut rng)));
            let c = G1Affine::from(G1::random(&mut rng));
            let d = G2Prepared::from(G2Affine::from(G2::random(&mut rng)));

            assert_eq!(
                Fq12::one(),
                multi_miller_loop_bls12_381(&[(&z1, &b)])
                    .final_exponentiation_bls12_381()
                    .0,
            );

            assert_eq!(
                Fq12::one(),
                multi_miller_loop_bls12_381(&[(&a, &z2)])
                    .final_exponentiation_bls12_381()
                    .0,
            );

            assert_eq!(
                multi_miller_loop_bls12_381(&[(&z1, &b), (&c, &d)])
                    .final_exponentiation_bls12_381(),
                multi_miller_loop_bls12_381(&[(&a, &z2), (&c, &d)])
                    .final_exponentiation_bls12_381(),
            );

            assert_eq!(
                multi_miller_loop_bls12_381(&[(&a, &b), (&z1, &d)])
                    .final_exponentiation_bls12_381(),
                multi_miller_loop_bls12_381(&[(&a, &b), (&c, &z2)])
                    .final_exponentiation_bls12_381(),
            );
        }
    }

    #[test]
    fn random_miller_loop_tests() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Exercise a double miller loop
        for _ in 0..1000 {
            let a = G1Affine::from(G1::random(&mut rng));
            let b = G2Affine::from(G2::random(&mut rng));
            let c = G1Affine::from(G1::random(&mut rng));
            let d = G2Affine::from(G2::random(&mut rng));

            let ab = Bls12_381::pairing(&a, &b);
            let cd = Bls12_381::pairing(&c, &d);

            let mut abcd = ab;
            abcd = Gt(abcd.0 * cd.0);

            let b = G2Prepared::from(b);
            let d = G2Prepared::from(d);

            let abcd_with_double_loop =
                multi_miller_loop(&[(&a, &b), (&c, &d)]).final_exponentiation();

            assert_eq!(abcd, abcd_with_double_loop);
        }
    }

    #[test]
    fn random_miller_loop_tests_bls12_381() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Exercise a double miller loop
        for _ in 0..1000 {
            let a = G1Affine::from(G1::random(&mut rng));
            let b = G2Affine::from(G2::random(&mut rng));
            let c = G1Affine::from(G1::random(&mut rng));
            let d = G2Affine::from(G2::random(&mut rng));

            let ab = pairing_bls12_381(&a, &b);
            let cd = pairing_bls12_381(&c, &d);

            let mut abcd = ab;
            abcd = Gt(abcd.0 * cd.0);

            let b = G2Prepared::from(b);
            let d = G2Prepared::from(d);

            let abcd_with_double_loop =
                multi_miller_loop_bls12_381(&[(&a, &b), (&c, &d)]).final_exponentiation_bls12_381();

            assert_eq!(abcd, abcd_with_double_loop);
        }
    }

    #[test]
    fn test_multi_miller_loop() {
        let a1 = G1Affine::generator();
        let b1 = G2Affine::generator();

        let a2 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([1, 2, 3, 4]).invert().unwrap().square(),
        );
        let b2 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([4, 2, 2, 4]).invert().unwrap().square(),
        );

        let a3 = G1Affine::identity();
        let b3 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([9, 2, 2, 4]).invert().unwrap().square(),
        );

        let a4 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([5, 5, 5, 5]).invert().unwrap().square(),
        );
        let b4 = G2Affine::identity();

        let a5 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([323, 32, 3, 1]).invert().unwrap().square(),
        );
        let b5 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([4, 2, 2, 9099]).invert().unwrap().square(),
        );

        let b1_prepared = G2Prepared::from(b1);
        let b2_prepared = G2Prepared::from(b2);
        let b3_prepared = G2Prepared::from(b3);
        let b4_prepared = G2Prepared::from(b4);
        let b5_prepared = G2Prepared::from(b5);

        let expected = Bls12_381::pairing(&a1, &b1)
            + Bls12_381::pairing(&a2, &b2)
            + Bls12_381::pairing(&a3, &b3)
            + Bls12_381::pairing(&a4, &b4)
            + Bls12_381::pairing(&a5, &b5);

        let test = multi_miller_loop(&[
            (&a1, &b1_prepared),
            (&a2, &b2_prepared),
            (&a3, &b3_prepared),
            (&a4, &b4_prepared),
            (&a5, &b5_prepared),
        ])
        .final_exponentiation();

        assert_eq!(expected, test);
    }

    #[test]
    fn test_multi_miller_loop_bls12_381() {
        let a1 = G1Affine::generator();
        let b1 = G2Affine::generator();

        let a2 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([1, 2, 3, 4]).invert().unwrap().square(),
        );
        let b2 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([4, 2, 2, 4]).invert().unwrap().square(),
        );

        let a3 = G1Affine::identity();
        let b3 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([9, 2, 2, 4]).invert().unwrap().square(),
        );

        let a4 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([5, 5, 5, 5]).invert().unwrap().square(),
        );
        let b4 = G2Affine::identity();

        let a5 = G1Affine::from(
            G1Affine::generator() * Fr::from_raw([323, 32, 3, 1]).invert().unwrap().square(),
        );
        let b5 = G2Affine::from(
            G2Affine::generator() * Fr::from_raw([4, 2, 2, 9099]).invert().unwrap().square(),
        );

        let b1_prepared = G2Prepared::from(b1);
        let b2_prepared = G2Prepared::from(b2);
        let b3_prepared = G2Prepared::from(b3);
        let b4_prepared = G2Prepared::from(b4);
        let b5_prepared = G2Prepared::from(b5);

        let expected = pairing_bls12_381(&a1, &b1)
            + pairing_bls12_381(&a2, &b2)
            + pairing_bls12_381(&a3, &b3)
            + pairing_bls12_381(&a4, &b4)
            + pairing_bls12_381(&a5, &b5);

        let test = multi_miller_loop_bls12_381(&[
            (&a1, &b1_prepared),
            (&a2, &b2_prepared),
            (&a3, &b3_prepared),
            (&a4, &b4_prepared),
            (&a5, &b5_prepared),
        ])
        .final_exponentiation_bls12_381();

        assert_eq!(expected, test);
    }

    #[test]
    fn test_bit_iterator() {
        let mut a = BitIterator::new([0xa953d79b83f6ab59, 0x6dea2059e200bd39]);
        let expected = "01101101111010100010000001011001111000100000000010111101001110011010100101010011110101111001101110000011111101101010101101011001";

        for e in expected.chars() {
            assert!(a.next().unwrap() == (e == '1'));
        }

        assert!(a.next().is_none());

        let expected = "1010010101111110101010000101101011101000011101110101001000011001100100100011011010001011011011010001011011101100110100111011010010110001000011110100110001100110011101101000101100011100100100100100001010011101010111110011101011000011101000111011011101011001";

        let mut a = BitIterator::new([
            0x429d5f3ac3a3b759,
            0xb10f4c66768b1c92,
            0x92368b6d16ecd3b4,
            0xa57ea85ae8775219,
        ]);

        for e in expected.chars() {
            assert!(a.next().unwrap() == (e == '1'));
        }

        assert!(a.next().is_none());
    }
}
