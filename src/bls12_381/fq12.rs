use super::fq::Fq;
use super::fq2::Fq2;
use super::fq6::Fq6;
use core::ops::{Add, Mul, Neg, Sub};
use ff::Field;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct Fq12 {
    pub c0: Fq6,
    pub c1: Fq6,
}

impl ConditionallySelectable for Fq12 {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fq12 {
            c0: Fq6::conditional_select(&a.c0, &b.c0, choice),
            c1: Fq6::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl ConstantTimeEq for Fq12 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl Neg for Fq12 {
    type Output = Fq12;

    #[inline]
    fn neg(self) -> Fq12 {
        -&self
    }
}

impl<'a> Neg for &'a Fq12 {
    type Output = Fq12;

    #[inline]
    fn neg(self) -> Fq12 {
        self.neg()
    }
}

impl<'a, 'b> Sub<&'b Fq12> for &'a Fq12 {
    type Output = Fq12;

    #[inline]
    fn sub(self, rhs: &'b Fq12) -> Fq12 {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fq12> for &'a Fq12 {
    type Output = Fq12;

    #[inline]
    fn add(self, rhs: &'b Fq12) -> Fq12 {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fq12> for &'a Fq12 {
    type Output = Fq12;

    #[inline]
    fn mul(self, rhs: &'b Fq12) -> Fq12 {
        self.mul(rhs)
    }
}

use crate::{
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
};
impl_binops_additive!(Fq12, Fq12);
impl_binops_multiplicative!(Fq12, Fq12);

impl Fq12 {
    pub fn mul_assign(&mut self, other: &Self) {
        let t0 = self.c0 * other.c0;
        let mut t1 = self.c1 * other.c1;
        let t2 = other.c0 + other.c1;

        self.c1 += &self.c0;
        self.c1 *= &t2;
        self.c1 -= &t0;
        self.c1 -= &t1;

        t1.mul_by_nonresidue();
        self.c0 = t0 + t1;
    }

    pub fn square_assign(&mut self) {
        let mut ab = self.c0 * self.c1;

        let c0c1 = self.c0 + self.c1;

        let mut c0 = self.c1;
        c0.mul_by_nonresidue();
        c0 += &self.c0;
        c0 *= &c0c1;
        c0 -= &ab;
        self.c1 = ab;
        self.c1 += &ab;
        ab.mul_by_nonresidue();
        c0 -= &ab;
        self.c0 = c0;
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
            c0: self.c0 + other.c0,
            c1: self.c1 + other.c1,
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self {
            c0: self.c0 - other.c0,
            c1: self.c1 - other.c1,
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

    #[inline(always)]
    pub fn neg(&self) -> Self {
        Self {
            c0: -self.c0,
            c1: -self.c1,
        }
    }

    #[inline(always)]
    pub fn conjugate(&mut self) {
        self.c1 = -self.c1;
    }

    #[inline(always)]
    pub fn conjugate_ret(&self) -> Self {
        Self {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    pub fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);

        self.c1.c0.mul_assign(&FROBENIUS_COEFF_FQ12_C1[power % 12]);
        self.c1.c1.mul_assign(&FROBENIUS_COEFF_FQ12_C1[power % 12]);
        self.c1.c2.mul_assign(&FROBENIUS_COEFF_FQ12_C1[power % 12]);
    }

    /// Alternative implementation of frobenius_map(), keeping here for reference
    /// Raises this element to p.
    // #[inline(always)]
    // pub fn frobenius_map_conjugate(&mut self) {
    //     self.c0.frobenius_map_conjugate();
    //     self.c1.frobenius_map_conjugate();

    //     // c1 = c1 * (u + 1)^((p - 1) / 6)
    //     self.c1 *= Fq6::from(Fq2 {
    //         c0: Fq::from_raw_unchecked([
    //             0x0708_9552_b319_d465,
    //             0xc669_5f92_b50a_8313,
    //             0x97e8_3ccc_d117_228f,
    //             0xa35b_aeca_b2dc_29ee,
    //             0x1ce3_93ea_5daa_ce4d,
    //             0x08f2_220f_b0fb_66eb,
    //         ]),
    //         c1: Fq::from_raw_unchecked([
    //             0xb2f6_6aad_4ce5_d646,
    //             0x5842_a06b_fc49_7cec,
    //             0xcf48_95d4_2599_d394,
    //             0xc11b_9cba_40a8_e8d0,
    //             0x2e38_13cb_e5a0_de89,
    //             0x110e_efda_8884_7faf,
    //         ]),
    //     });
    // }

    pub fn mul_by_014(&mut self, c0: &Fq2, c1: &Fq2, c4: &Fq2) {
        let mut aa = self.c0;
        aa.mul_by_01(c0, c1);
        let mut bb = self.c1;
        bb.mul_by_1(c4);
        let o = c1 + c4;
        self.c1 += &self.c0;
        self.c1.mul_by_01(c0, &o);
        self.c1 -= &aa;
        self.c1 -= &bb;
        self.c0 = bb;
        self.c0.mul_by_nonresidue();
        self.c0 += &aa;
    }

    pub fn mul_by_014_bls12_381(&self, c0: &Fq2, c1: &Fq2, c4: &Fq2) -> Fq12 {
        let aa = self.c0.mul_by_01_bls12_381(c0, c1);
        let bb = self.c1.mul_by_1_bls12_381(c4);
        let o = c1 + c4;
        let c1 = self.c1 + self.c0;
        let c1 = c1.mul_by_01_bls12_381(c0, &o);
        let c1 = c1 - aa - bb;
        let c0 = bb;
        let c0 = c0.mul_by_nonresidue_bls12_381();
        let c0 = c0 + aa;

        Fq12 { c0, c1 }
    }

    pub fn mul_by_034(&mut self, c0: &Fq2, c3: &Fq2, c4: &Fq2) {
        let t0 = Fq6 {
            c0: self.c0.c0 * c0,
            c1: self.c0.c1 * c0,
            c2: self.c0.c2 * c0,
        };
        let mut t1 = self.c1;
        t1.mul_by_01(c3, c4);
        let o = c0 + c3;
        let mut t2 = self.c0 + self.c1;
        t2.mul_by_01(&o, c4);
        t2 -= t0;
        self.c1 = t2 - t1;
        t1.mul_by_nonresidue();
        self.c0 = t0 + t1;
    }

    pub fn invert(&self) -> CtOption<Self> {
        let mut c0s = self.c0;
        c0s.square_assign();
        let mut c1s = self.c1;
        c1s.square_assign();
        c1s.mul_by_nonresidue();
        c0s -= &c1s;

        c0s.invert().map(|t| {
            let mut tmp = Fq12 { c0: t, c1: t };
            tmp.c0.mul_assign(&self.c0);
            tmp.c1.mul_assign(&self.c1);
            tmp.c1 = tmp.c1.neg();

            tmp
        })
    }

    pub fn cyclotomic_square(&mut self) {
        fn fp4_square(c0: &mut Fq2, c1: &mut Fq2, a0: &Fq2, a1: &Fq2) {
            let t0 = a0.square();
            let t1 = a1.square();
            let mut t2 = t1;
            t2.mul_by_nonresidue();
            *c0 = t2 + t0;
            t2 = a0 + a1;
            t2.square_assign();
            t2 -= t0;
            *c1 = t2 - t1;
        }

        let mut t3 = Fq2::zero();
        let mut t4 = Fq2::zero();
        let mut t5 = Fq2::zero();
        let mut t6 = Fq2::zero();

        fp4_square(&mut t3, &mut t4, &self.c0.c0, &self.c1.c1);
        let mut t2 = t3 - self.c0.c0;
        t2.double_assign();
        self.c0.c0 = t2 + t3;

        t2 = t4 + self.c1.c1;
        t2.double_assign();
        self.c1.c1 = t2 + t4;

        fp4_square(&mut t3, &mut t4, &self.c1.c0, &self.c0.c2);
        fp4_square(&mut t5, &mut t6, &self.c0.c1, &self.c1.c2);

        t2 = t3 - self.c0.c1;
        t2.double_assign();
        self.c0.c1 = t2 + t3;
        t2 = t4 + self.c1.c2;
        t2.double_assign();
        self.c1.c2 = t2 + t4;
        t3 = t6;
        t3.mul_by_nonresidue();
        t2 = t3 + self.c1.c0;
        t2.double_assign();
        self.c1.c0 = t2 + t3;
        t2 = t5 - self.c0.c2;
        t2.double_assign();
        self.c0.c2 = t2 + t5;
    }
}

impl Field for Fq12 {
    fn random(mut rng: impl RngCore) -> Self {
        Fq12 {
            c0: Fq6::random(&mut rng),
            c1: Fq6::random(&mut rng),
        }
    }

    fn zero() -> Self {
        Fq12 {
            c0: Fq6::zero(),
            c1: Fq6::zero(),
        }
    }

    fn one() -> Self {
        Fq12 {
            c0: Fq6::one(),
            c1: Fq6::zero(),
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

// non_residue^((modulus^i-1)/6) for i=0,...,11
pub const FROBENIUS_COEFF_FQ12_C1: [Fq2; 12] = [
    // Fq2(u + 1)**(((q^0) - 1) / 6)
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
    // Fq2(u + 1)**(((q^1) - 1) / 6)
    Fq2 {
        c0: Fq([
            0x7089552b319d465,
            0xc6695f92b50a8313,
            0x97e83cccd117228f,
            0xa35baecab2dc29ee,
            0x1ce393ea5daace4d,
            0x8f2220fb0fb66eb,
        ]),
        c1: Fq([
            0xb2f66aad4ce5d646,
            0x5842a06bfc497cec,
            0xcf4895d42599d394,
            0xc11b9cba40a8e8d0,
            0x2e3813cbe5a0de89,
            0x110eefda88847faf,
        ]),
    },
    // Fq2(u + 1)**(((q^2) - 1) / 6)
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
    // Fq2(u + 1)**(((q^3) - 1) / 6)
    Fq2 {
        c0: Fq([
            0x3e2f585da55c9ad1,
            0x4294213d86c18183,
            0x382844c88b623732,
            0x92ad2afd19103e18,
            0x1d794e4fac7cf0b9,
            0xbd592fc7d825ec8,
        ]),
        c1: Fq([
            0x7bcfa7a25aa30fda,
            0xdc17dec12a927e7c,
            0x2f088dd86b4ebef1,
            0xd1ca2087da74d4a7,
            0x2da2596696cebc1d,
            0xe2b7eedbbfd87d2,
        ]),
    },
    // Fq2(u + 1)**(((q^4) - 1) / 6)
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
    // Fq2(u + 1)**(((q^5) - 1) / 6)
    Fq2 {
        c0: Fq([
            0x3726c30af242c66c,
            0x7c2ac1aad1b6fe70,
            0xa04007fbba4b14a2,
            0xef517c3266341429,
            0x95ba654ed2226b,
            0x2e370eccc86f7dd,
        ]),
        c1: Fq([
            0x82d83cf50dbce43f,
            0xa2813e53df9d018f,
            0xc6f0caa53c65e181,
            0x7525cf528d50fe95,
            0x4a85ed50f4798a6b,
            0x171da0fd6cf8eebd,
        ]),
    },
    // Fq2(u + 1)**(((q^6) - 1) / 6)
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
    // Fq2(u + 1)**(((q^7) - 1) / 6)
    Fq2 {
        c0: Fq([
            0xb2f66aad4ce5d646,
            0x5842a06bfc497cec,
            0xcf4895d42599d394,
            0xc11b9cba40a8e8d0,
            0x2e3813cbe5a0de89,
            0x110eefda88847faf,
        ]),
        c1: Fq([
            0x7089552b319d465,
            0xc6695f92b50a8313,
            0x97e83cccd117228f,
            0xa35baecab2dc29ee,
            0x1ce393ea5daace4d,
            0x8f2220fb0fb66eb,
        ]),
    },
    // Fq2(u + 1)**(((q^8) - 1) / 6)
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
    // Fq2(u + 1)**(((q^9) - 1) / 6)
    Fq2 {
        c0: Fq([
            0x7bcfa7a25aa30fda,
            0xdc17dec12a927e7c,
            0x2f088dd86b4ebef1,
            0xd1ca2087da74d4a7,
            0x2da2596696cebc1d,
            0xe2b7eedbbfd87d2,
        ]),
        c1: Fq([
            0x3e2f585da55c9ad1,
            0x4294213d86c18183,
            0x382844c88b623732,
            0x92ad2afd19103e18,
            0x1d794e4fac7cf0b9,
            0xbd592fc7d825ec8,
        ]),
    },
    // Fq2(u + 1)**(((q^10) - 1) / 6)
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
    // Fq2(u + 1)**(((q^11) - 1) / 6)
    Fq2 {
        c0: Fq([
            0x82d83cf50dbce43f,
            0xa2813e53df9d018f,
            0xc6f0caa53c65e181,
            0x7525cf528d50fe95,
            0x4a85ed50f4798a6b,
            0x171da0fd6cf8eebd,
        ]),
        c1: Fq([
            0x3726c30af242c66c,
            0x7c2ac1aad1b6fe70,
            0xa04007fbba4b14a2,
            0xef517c3266341429,
            0x95ba654ed2226b,
            0x2e370eccc86f7dd,
        ]),
    },
];

#[cfg(test)]
mod test {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_fq12_mul_by_014() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let c0 = Fq2::random(&mut rng);
            let c1 = Fq2::random(&mut rng);
            let c5 = Fq2::random(&mut rng);
            let mut a = Fq12::random(&mut rng);
            let mut b = a;

            a.mul_by_014(&c0, &c1, &c5);
            b.mul_assign(&Fq12 {
                c0: Fq6 {
                    c0,
                    c1,
                    c2: Fq2::zero(),
                },
                c1: Fq6 {
                    c0: Fq2::zero(),
                    c1: c5,
                    c2: Fq2::zero(),
                },
            });

            assert_eq!(a, b);
        }
    }

    #[test]
    fn test_fq12_mul_by_034() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let c0 = Fq2::random(&mut rng);
            let c3 = Fq2::random(&mut rng);
            let c4 = Fq2::random(&mut rng);
            let mut a = Fq12::random(&mut rng);
            let mut b = a;

            a.mul_by_034(&c0, &c3, &c4);
            b.mul_assign(&Fq12 {
                c0: Fq6 {
                    c0,
                    c1: Fq2::zero(),
                    c2: Fq2::zero(),
                },
                c1: Fq6 {
                    c0: c3,
                    c1: c4,
                    c2: Fq2::zero(),
                },
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
            let mut a = Fq12::random(&mut rng);
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

        let fq12_basic = Fq12 {
            c0: fq6_basic,
            c1: fq6_basic,
        };

        let mut fq12_test = fq12_basic;
        fq12_test.frobenius_map(0);
        assert_eq!(fq12_test, fq12_basic);

        let mut fq12_test_2 = fq12_basic;
        fq12_test_2.frobenius_map(12);
        assert_eq!(fq12_test_2, fq12_basic);
    }

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

    //     let fq12_basic = Fq12 {
    //         c0: fq6_basic,
    //         c1: fq6_basic,
    //     };

    //     let mut fq12_test_1 = fq12_basic;
    //     fq12_test_1.frobenius_map(1);
    //     let mut fq12_test_conjugate_1 = fq12_basic;
    //     fq12_test_conjugate_1.frobenius_map_conjugate();
    //     assert_eq!(fq12_test_1, fq12_test_conjugate_1);

    //     let mut fq12_test_1 = fq12_basic;
    //     fq12_test_1.frobenius_map(2);
    //     let mut fq12_test_conjugate_1 = fq12_basic;
    //     fq12_test_conjugate_1.frobenius_map_conjugate();
    //     fq12_test_conjugate_1.frobenius_map_conjugate();
    //     assert_eq!(fq12_test_1, fq12_test_conjugate_1);
    // }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fq12>("fq12".to_string());
    }
}
