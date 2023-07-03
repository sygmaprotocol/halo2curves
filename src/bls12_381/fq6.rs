use super::fq::Fq;
use super::fq2::Fq2;
use core::ops::{Add, Mul, Neg, Sub};
use ff::Field;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct Fq6 {
    pub c0: Fq2,
    pub c1: Fq2,
    pub c2: Fq2,
}

impl ConditionallySelectable for Fq6 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fq6 {
            c0: Fq2::conditional_select(&a.c0, &b.c0, choice),
            c1: Fq2::conditional_select(&a.c1, &b.c1, choice),
            c2: Fq2::conditional_select(&a.c2, &b.c2, choice),
        }
    }
}

impl ConstantTimeEq for Fq6 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1) & self.c2.ct_eq(&other.c2)
    }
}

impl Neg for Fq6 {
    type Output = Fq6;

    #[inline]
    fn neg(self) -> Fq6 {
        -&self
    }
}

impl<'a> Neg for &'a Fq6 {
    type Output = Fq6;

    #[inline]
    fn neg(self) -> Fq6 {
        self.neg()
    }
}

impl<'a, 'b> Sub<&'b Fq6> for &'a Fq6 {
    type Output = Fq6;

    #[inline]
    fn sub(self, rhs: &'b Fq6) -> Fq6 {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fq6> for &'a Fq6 {
    type Output = Fq6;

    #[inline]
    fn add(self, rhs: &'b Fq6) -> Fq6 {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fq6> for &'a Fq6 {
    type Output = Fq6;

    #[inline]
    fn mul(self, rhs: &'b Fq6) -> Fq6 {
        self.mul(rhs)
    }
}

impl From<Fq2> for Fq6 {
    fn from(f: Fq2) -> Fq6 {
        Fq6 {
            c0: f,
            c1: Fq2::zero(),
            c2: Fq2::zero(),
        }
    }
}

use crate::{
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fq6, Fq6);
impl_binops_multiplicative!(Fq6, Fq6);

impl Fq6 {
    pub fn mul_assign(&mut self, other: &Self) {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        let mut c_c = self.c2;
        a_a *= &other.c0;
        b_b *= &other.c1;
        c_c *= &other.c2;

        let mut t1 = other.c1;
        t1 += &other.c2;
        {
            let mut tmp = self.c1;
            tmp += &self.c2;

            t1 *= &tmp;
            t1 -= &b_b;
            t1 -= &c_c;
            t1.mul_by_nonresidue();
            t1 += &a_a;
        }

        let mut t3 = other.c0;
        t3 += &other.c2;
        {
            let mut tmp = self.c0;
            tmp += &self.c2;

            t3 *= &tmp;
            t3 -= &a_a;
            t3 += &b_b;
            t3 -= &c_c;
        }

        let mut t2 = other.c0;
        t2 += &other.c1;
        {
            let mut tmp = self.c0;
            tmp += &self.c1;

            t2 *= &tmp;
            t2 -= &a_a;
            t2 -= &b_b;
            c_c.mul_by_nonresidue();
            t2 += &c_c;
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }

    pub fn square_assign(&mut self) {
        // s0 = a^2
        let mut s0 = self.c0;
        s0.square_assign();
        // s1 = 2ab
        let mut ab = self.c0;
        ab *= &self.c1;
        let mut s1 = ab;
        s1.double_assign();
        // s2 = (a - b + c)^2
        let mut s2 = self.c0;
        s2 -= &self.c1;
        s2 += &self.c2;
        s2.square_assign();
        // bc
        let mut bc = self.c1;
        bc *= &self.c2;
        // s3 = 2bc
        let mut s3 = bc;
        s3.double_assign();
        // s4 = c^2
        let mut s4 = self.c2;
        s4.square_assign();

        // new c0 = 2bc.mul_by_xi + a^2
        self.c0 = s3;
        self.c0.mul_by_nonresidue();
        // self.c0.mul_by_xi();
        self.c0 += &s0;

        // new c1 = (c^2).mul_by_xi + 2ab
        self.c1 = s4;
        self.c1.mul_by_nonresidue();
        // self.c1.mul_by_xi();
        self.c1 += &s1;

        // new c2 = 2ab + (a - b + c)^2 + 2bc - a^2 - c^2 = b^2 + 2ac
        self.c2 = s1;
        self.c2 += &s2;
        self.c2 += &s3;
        self.c2 -= &s0;
        self.c2 -= &s4;
    }

    pub fn double(&self) -> Self {
        Self {
            c0: self.c0.double(),
            c1: self.c1.double(),
            c2: self.c2.double(),
        }
    }

    pub fn double_assign(&mut self) {
        self.c0 = self.c0.double();
        self.c1 = self.c1.double();
        self.c2 = self.c2.double();
    }

    pub fn add(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
            c2: self.c2 + other.c2,
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
            c2: self.c2 - other.c2,
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
            c0: -self.c0,
            c1: -self.c1,
            c2: -self.c2,
        }
    }

    pub fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);
        self.c2.frobenius_map(power);

        self.c1.mul_assign(&FROBENIUS_COEFF_FQ6_C1[power % 6]);
        self.c2.mul_assign(&FROBENIUS_COEFF_FQ6_C2[power % 6]);
    }

    /// Alternative implementation of frobenius_map(), keeping here for reference
    /// Raises this element to p.
    // #[inline(always)]
    // pub fn frobenius_map_conjugate(&mut self) {
    //     self.c0.frobenius_map_conjugate();
    //     self.c1.frobenius_map_conjugate();
    //     self.c2.frobenius_map_conjugate();

    //     // c1 = c1 * (u + 1)^((p - 1) / 3)
    //     self.c1 *= Fq2 {
    //         c0: Fq::zero(),
    //         c1: Fq::from_raw_unchecked([
    //             0xcd03_c9e4_8671_f071,
    //             0x5dab_2246_1fcd_a5d2,
    //             0x5870_42af_d385_1b95,
    //             0x8eb6_0ebe_01ba_cb9e,
    //             0x03f9_7d6e_83d0_50d2,
    //             0x18f0_2065_5463_8741,
    //         ]),
    //     };

    //     // c2 = c2 * (u + 1)^((2p - 2) / 3)
    //     self.c2 *= Fq2 {
    //         c0: Fq::from_raw_unchecked([
    //             0x890d_c9e4_8675_45c3,
    //             0x2af3_2253_3285_a5d5,
    //             0x5088_0866_309b_7e2c,
    //             0xa20d_1b8c_7e88_1024,
    //             0x14e4_f04f_e2db_9068,
    //             0x14e5_6d3f_1564_853a,
    //         ]),
    //         c1: Fq::zero(),
    //     };
    // }

    /// Multiply by cubic nonresidue v.
    pub fn mul_by_nonresidue(&mut self) {
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1);
        swap(&mut self.c0, &mut self.c2);
        // c0, c1, c2 -> c2, c0, c1
        self.c0.mul_by_nonresidue();
    }

    /// Multiply by quadratic nonresidue v.
    pub fn mul_by_nonresidue_bls12_381(&self) -> Self {
        // Given a + bv + cv^2, this produces
        //     av + bv^2 + cv^3
        // but because v^3 = u + 1, we have
        //     c(u + 1) + av + v^2

        Fq6 {
            c0: self.c2.mul_by_nonresidue_bls12_381(),
            c1: self.c0,
            c2: self.c1,
        }
    }

    /// Multiply by cubic nonresidue v.
    pub fn mul_by_v(&mut self) {
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1);
        swap(&mut self.c0, &mut self.c2);

        self.c0.mul_by_xi();
    }

    pub fn mul_by_1(&mut self, c1: &Fq2) {
        let mut b_b = self.c1;
        b_b *= c1;

        let mut t1 = *c1;
        {
            let mut tmp = self.c1;
            tmp += &self.c2;

            t1 *= &tmp;
            t1 -= &b_b;
            t1.mul_by_nonresidue();
        }

        let mut t2 = *c1;
        {
            let mut tmp = self.c0;
            tmp += &self.c1;

            t2 *= &tmp;
            t2 -= &b_b;
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = b_b;
    }

    pub fn mul_by_1_bls12_381(&self, c1: &Fq2) -> Fq6 {
        Fq6 {
            c0: (self.c2 * c1).mul_by_nonresidue_bls12_381(),
            c1: self.c0 * c1,
            c2: self.c1 * c1,
        }
    }

    pub fn mul_by_01(&mut self, c0: &Fq2, c1: &Fq2) {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        a_a *= c0;
        b_b *= c1;

        let mut t1 = *c1;
        {
            let mut tmp = self.c1;
            tmp += &self.c2;

            t1 *= &tmp;
            t1 -= &b_b;
            t1.mul_by_nonresidue();
            t1 += &a_a;
        }

        let mut t3 = *c0;
        {
            let mut tmp = self.c0;
            tmp += &self.c2;

            t3 *= &tmp;
            t3 -= &a_a;
            t3 += &b_b;
        }

        let mut t2 = *c0;
        t2 += c1;
        {
            let mut tmp = self.c0;
            tmp += &self.c1;

            t2 *= &tmp;
            t2 -= &a_a;
            t2 -= &b_b;
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }

    pub fn mul_by_01_bls12_381(&self, c0: &Fq2, c1: &Fq2) -> Fq6 {
        let a_a = self.c0 * c0;
        let b_b = self.c1 * c1;

        let t1 = (self.c2 * c1).mul_by_nonresidue_bls12_381() + a_a;

        let t2 = (c0 + c1) * (self.c0 + self.c1) - a_a - b_b;

        let t3 = self.c2 * c0 + b_b;

        Fq6 {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }

    fn invert(&self) -> CtOption<Self> {
        let mut c0 = self.c2;
        c0.mul_by_nonresidue();
        c0 *= &self.c1;
        c0 = -c0;
        {
            let mut c0s = self.c0;
            c0s.square_assign();
            c0 += &c0s;
        }
        let mut c1 = self.c2;
        c1.square_assign();
        c1.mul_by_nonresidue();
        {
            let mut c01 = self.c0;
            c01 *= &self.c1;
            c1 -= &c01;
        }
        let mut c2 = self.c1;
        c2.square_assign();
        {
            let mut c02 = self.c0;
            c02 *= &self.c2;
            c2 -= &c02;
        }

        let mut tmp1 = self.c2;
        tmp1 *= &c1;
        let mut tmp2 = self.c1;
        tmp2 *= &c2;
        tmp1 += &tmp2;
        tmp1.mul_by_nonresidue();
        tmp2 = self.c0;
        tmp2 *= &c0;
        tmp1 += &tmp2;

        tmp1.invert().map(|t| {
            let mut tmp = Fq6 {
                c0: t,
                c1: t,
                c2: t,
            };
            tmp.c0 *= &c0;
            tmp.c1 *= &c1;
            tmp.c2 *= &c2;

            tmp
        })
    }
}

impl Field for Fq6 {
    fn random(mut rng: impl RngCore) -> Self {
        Fq6 {
            c0: Fq2::random(&mut rng),
            c1: Fq2::random(&mut rng),
            c2: Fq2::random(&mut rng),
        }
    }

    fn zero() -> Self {
        Fq6 {
            c0: Fq2::zero(),
            c1: Fq2::zero(),
            c2: Fq2::zero(),
        }
    }

    fn one() -> Self {
        Fq6 {
            c0: Fq2::one(),
            c1: Fq2::zero(),
            c2: Fq2::zero(),
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
        unimplemented!()
    }

    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }
}

pub const FROBENIUS_COEFF_FQ6_C1: [Fq2; 6] = [
    // Fq2(u + 1)**(((q^0) - 1) / 3)
    Fq2 {
        c0: Fq([
            0x760900000002fffd,
            0xebf4000bc40c0002,
            0x5f48985753c758ba,
            0x77ce585370525745,
            0x5c071a97a256ec6d,
            0x15f65ec3fa80e493,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((q^1) - 1) / 3)
    Fq2 {
        c0: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
        c1: Fq([
            0xcd03c9e48671f071,
            0x5dab22461fcda5d2,
            0x587042afd3851b95,
            0x8eb60ebe01bacb9e,
            0x3f97d6e83d050d2,
            0x18f0206554638741,
        ]),
    },
    // Fq2(u + 1)**(((q^2) - 1) / 3)
    Fq2 {
        c0: Fq([
            0x30f1361b798a64e8,
            0xf3b8ddab7ece5a2a,
            0x16a8ca3ac61577f7,
            0xc26a2ff874fd029b,
            0x3636b76660701c6e,
            0x51ba4ab241b6160,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((q^3) - 1) / 3)
    Fq2 {
        c0: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
        c1: Fq([
            0x760900000002fffd,
            0xebf4000bc40c0002,
            0x5f48985753c758ba,
            0x77ce585370525745,
            0x5c071a97a256ec6d,
            0x15f65ec3fa80e493,
        ]),
    },
    // Fq2(u + 1)**(((q^4) - 1) / 3)
    Fq2 {
        c0: Fq([
            0xcd03c9e48671f071,
            0x5dab22461fcda5d2,
            0x587042afd3851b95,
            0x8eb60ebe01bacb9e,
            0x3f97d6e83d050d2,
            0x18f0206554638741,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((q^5) - 1) / 3)
    Fq2 {
        c0: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
        c1: Fq([
            0x30f1361b798a64e8,
            0xf3b8ddab7ece5a2a,
            0x16a8ca3ac61577f7,
            0xc26a2ff874fd029b,
            0x3636b76660701c6e,
            0x51ba4ab241b6160,
        ]),
    },
];

pub const FROBENIUS_COEFF_FQ6_C2: [Fq2; 6] = [
    // Fq2(u + 1)**(((2q^0) - 2) / 3)
    Fq2 {
        c0: Fq([
            0x760900000002fffd,
            0xebf4000bc40c0002,
            0x5f48985753c758ba,
            0x77ce585370525745,
            0x5c071a97a256ec6d,
            0x15f65ec3fa80e493,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((2q^1) - 2) / 3)
    Fq2 {
        c0: Fq([
            0x890dc9e4867545c3,
            0x2af322533285a5d5,
            0x50880866309b7e2c,
            0xa20d1b8c7e881024,
            0x14e4f04fe2db9068,
            0x14e56d3f1564853a,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((2q^2) - 2) / 3)
    Fq2 {
        c0: Fq([
            0xcd03c9e48671f071,
            0x5dab22461fcda5d2,
            0x587042afd3851b95,
            0x8eb60ebe01bacb9e,
            0x3f97d6e83d050d2,
            0x18f0206554638741,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((2q^3) - 2) / 3)
    Fq2 {
        c0: Fq([
            0x43f5fffffffcaaae,
            0x32b7fff2ed47fffd,
            0x7e83a49a2e99d69,
            0xeca8f3318332bb7a,
            0xef148d1ea0f4c069,
            0x40ab3263eff0206,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((2q^4) - 2) / 3)
    Fq2 {
        c0: Fq([
            0x30f1361b798a64e8,
            0xf3b8ddab7ece5a2a,
            0x16a8ca3ac61577f7,
            0xc26a2ff874fd029b,
            0x3636b76660701c6e,
            0x51ba4ab241b6160,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
    // Fq2(u + 1)**(((2q^5) - 2) / 3)
    Fq2 {
        c0: Fq([
            0xecfb361b798dba3a,
            0xc100ddb891865a2c,
            0xec08ff1232bda8e,
            0xd5c13cc6f1ca4721,
            0x47222a47bf7b5c04,
            0x110f184e51c5f59,
        ]),
        c1: Fq([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
    },
];

#[cfg(test)]
mod test {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_fq6_mul_nonresidue() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let nqr = Fq6 {
            c0: Fq2::zero(),
            c1: Fq2::one(),
            c2: Fq2::zero(),
        };

        for _ in 0..1000 {
            let mut a = Fq6::random(&mut rng);
            let mut b = a;
            a.mul_by_nonresidue();
            b.mul_assign(&nqr);

            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_fq6_mul_by_1() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let c1 = Fq2::random(&mut rng);
            let mut a = Fq6::random(&mut rng);
            let mut b = a;

            a.mul_by_1(&c1);
            b.mul_assign(&Fq6 {
                c0: Fq2::zero(),
                c1,
                c2: Fq2::zero(),
            });

            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_fq6_mul_by_01() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let c0 = Fq2::random(&mut rng);
            let c1 = Fq2::random(&mut rng);
            let mut a = Fq6::random(&mut rng);
            let mut b = a;

            a.mul_by_01(&c0, &c1);
            b.mul_assign(&Fq6 {
                c0,
                c1,
                c2: Fq2::zero(),
            });

            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_squaring() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut a = Fq6::random(&mut rng);
            let mut b = a;
            b.mul_assign(&a);
            a.square_assign();
            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_frobenius() {
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

        let fq6_basic = Fq6 {
            c0: fq2_basic,
            c1: fq2_basic,
            c2: fq2_basic,
        };

        let mut fq6_test = fq6_basic;
        fq6_test.frobenius_map(0);
        assert_eq!(fq6_test, fq6_basic);

        let mut fq6_test = fq6_basic;
        fq6_test.frobenius_map(1);
        assert_ne!(fq6_test, fq6_basic);

        let mut fq6_test = fq6_basic;
        fq6_test.frobenius_map(6);
        assert_eq!(fq6_test, fq6_basic);
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
    //             0x228109103250c9d0,
    //             0x8a411ad149045812,
    //             0xa9109e8f3041427e,
    //             0xb07e9bc405608611,
    //             0xfcd559cbe77bd8b8,
    //             0x18d400b280d93e62,
    //         ]),
    //     };

    //     let fq6_basic = Fq6 {
    //         c0: fq2_basic,
    //         c1: fq2_basic,
    //         c2: fq2_basic,
    //     };

    //     let mut fq6_test = fq6_basic;
    //     fq6_test.frobenius_map_conjugate();
    //     fq6_test.frobenius_map_conjugate();
    //     fq6_test.frobenius_map_conjugate();
    //     fq6_test.frobenius_map_conjugate();
    //     fq6_test.frobenius_map_conjugate();
    //     fq6_test.frobenius_map_conjugate();
    //     assert_eq!(fq6_test, fq6_basic);

    //     let mut fq6_test = fq6_basic;
    //     fq6_test.frobenius_map_conjugate();
    //     assert_ne!(fq6_test, fq6_basic);
    // }

    // #[test]
    // fn test_frobenius_map_mix() {
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

    //     let fq6_basic = Fq6 {
    //         c0: fq2_basic,
    //         c1: fq2_basic,
    //         c2: fq2_basic,
    //     };

    //     let mut fq6_test_1 = fq6_basic;
    //     fq6_test_1.frobenius_map(1);
    //     let mut fq6_test_conjugate_1 = fq6_basic;
    //     fq6_test_conjugate_1.frobenius_map_conjugate();
    //     assert_eq!(fq6_test_1, fq6_test_conjugate_1);

    //     let mut fq6_test_1 = fq6_basic;
    //     fq6_test_1.frobenius_map(2);
    //     let mut fq6_test_conjugate_1 = fq6_basic;
    //     fq6_test_conjugate_1.frobenius_map_conjugate();
    //     fq6_test_conjugate_1.frobenius_map_conjugate();
    //     assert_eq!(fq6_test_1, fq6_test_conjugate_1);
    // }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fq6>("fq6".to_string());
    }
}
