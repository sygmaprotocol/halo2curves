#[macro_export]
macro_rules! field_common_fq {
    (
        $field:ident,
        $modulus:ident,
        $inv:ident,
        $modulus_str:ident,
        $two_inv:ident,
        $root_of_unity_inv:ident,
        $delta:ident,
        $zeta:ident,
        $r:ident,
        $r2:ident,
        $r3:ident
    ) => {
        impl $field {
            /// Returns zero, the additive identity.
            #[inline]
            pub const fn zero() -> $field {
                $field([0, 0, 0, 0, 0, 0])
            }

            /// Returns one, the multiplicative identity.
            #[inline]
            pub const fn one() -> $field {
                $r
            }

            // TODO [from_u512] Add support for BLS12-381
            fn from_u512(limbs: [u64; 8]) -> $field {
                let d0 = $field([limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5]]);
                let d1 = $field([limbs[6], limbs[7], 0, 0, 0, 0]);
                // Convert to Montgomery form
                d0 * $r2 + d1 * $r3
            }

            /// Constructs an element of `Fq` without checking that it is
            /// canonical.
            pub const fn from_raw_unchecked(limbs: [u64; 6]) -> $field {
                $field(limbs)
            }

            /// Convert a little-endian byte representation of a scalar into a `Fq`
            pub fn from_bytes(bytes: &[u8; 48]) -> CtOption<$field> {
                <Self as ff::PrimeField>::from_repr(FqBytes::from(*bytes))
            }

            // Converts an element of `Fq` into a byte representation in
            // little-endian byte order.
            pub fn to_bytes(&self) -> [u8; 48] {
                <Self as ff::PrimeField>::to_repr(self).slice
            }

            /// Returns whether or not this element is strictly lexicographically
            /// larger than its negation.
            pub fn lexicographically_largest(&self) -> Choice {
                // This can be determined by checking to see if the element is
                // larger than (p - 1) // 2. If we subtract by ((p - 1) // 2) + 1
                // and there is no underflow, then the element must be larger than
                // (p - 1) // 2.

                // First, because self is in Montgomery form we need to reduce it
                let tmp = $field::montgomery_reduce(
                    self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5], 0, 0, 0, 0,
                    0, 0,
                );

                let (_, borrow) = sbb(tmp.0[0], 0xdcff_7fff_ffff_d556, false);
                let (_, borrow) = sbb(tmp.0[1], 0x0f55_ffff_58a9_ffff, borrow);
                let (_, borrow) = sbb(tmp.0[2], 0xb398_6950_7b58_7b12, borrow);
                let (_, borrow) = sbb(tmp.0[3], 0xb23b_a5c2_79c2_895f, borrow);
                let (_, borrow) = sbb(tmp.0[4], 0x258d_d3db_21a5_d66b, borrow);
                let (_, borrow) = sbb(tmp.0[5], 0x0d00_88f5_1cbf_f34d, borrow);

                // If the element was smaller, the subtraction will underflow
                // producing a borrow value of 0xffff...ffff, otherwise it will
                // be zero. We create a Choice representing true if there was
                // overflow (and so this element is not lexicographically larger
                // than its negation) and then negate it.

                !Choice::from((borrow as u8) & 1)
            }
        }

        impl Group for $field {
            type Scalar = Self;

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

        impl fmt::Debug for $field {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let tmp = self.to_repr();
                write!(f, "0x")?;
                for &b in tmp.slice.iter().rev() {
                    write!(f, "{:02x}", b)?;
                }
                Ok(())
            }
        }

        impl Default for $field {
            #[inline]
            fn default() -> Self {
                Self::zero()
            }
        }

        impl From<bool> for $field {
            fn from(bit: bool) -> $field {
                if bit {
                    $field::one()
                } else {
                    $field::zero()
                }
            }
        }

        impl From<u64> for $field {
            fn from(val: u64) -> $field {
                $field([val, 0, 0, 0, 0, 0]) * $r2
            }
        }

        impl ConstantTimeEq for $field {
            fn ct_eq(&self, other: &Self) -> Choice {
                self.0[0].ct_eq(&other.0[0])
                    & self.0[1].ct_eq(&other.0[1])
                    & self.0[2].ct_eq(&other.0[2])
                    & self.0[3].ct_eq(&other.0[3])
                    & self.0[4].ct_eq(&other.0[4])
                    & self.0[5].ct_eq(&other.0[5])
            }
        }

        impl core::cmp::Ord for $field {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                let left = self.to_repr();
                let right = other.to_repr();
                left.slice
                    .iter()
                    .zip(right.slice.iter())
                    .rev()
                    .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                        core::cmp::Ordering::Equal => None,
                        res => Some(res),
                    })
                    .unwrap_or(core::cmp::Ordering::Equal)
            }
        }

        impl core::cmp::PartialOrd for $field {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl ConditionallySelectable for $field {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $field([
                    u64::conditional_select(&a.0[0], &b.0[0], choice),
                    u64::conditional_select(&a.0[1], &b.0[1], choice),
                    u64::conditional_select(&a.0[2], &b.0[2], choice),
                    u64::conditional_select(&a.0[3], &b.0[3], choice),
                    u64::conditional_select(&a.0[4], &b.0[4], choice),
                    u64::conditional_select(&a.0[5], &b.0[5], choice),
                ])
            }
        }

        impl<'a> Neg for &'a $field {
            type Output = $field;

            #[inline]
            fn neg(self) -> $field {
                self.neg()
            }
        }

        impl Neg for $field {
            type Output = $field;

            #[inline]
            fn neg(self) -> $field {
                -&self
            }
        }

        impl<'a, 'b> Sub<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn sub(self, rhs: &'b $field) -> $field {
                self.sub(rhs)
            }
        }

        impl<'a, 'b> Add<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn add(self, rhs: &'b $field) -> $field {
                self.add(rhs)
            }
        }

        impl<'a, 'b> Mul<&'b $field> for &'a $field {
            type Output = $field;

            #[inline]
            fn mul(self, rhs: &'b $field) -> $field {
                self.mul(rhs)
            }
        }

        impl From<[u64; 6]> for $field {
            fn from(digits: [u64; 6]) -> Self {
                Self::from_raw_unchecked(digits)
            }
        }

        impl From<$field> for [u64; 6] {
            fn from(elt: $field) -> [u64; 6] {
                // Turn into canonical form by computing
                // (a.R) / R = a
                #[cfg(feature = "asm")]
                let tmp = $field::montgomery_reduce(&[
                    elt.0[0], elt.0[1], elt.0[2], elt.0[3], elt.0[4], elt.0[5], 0, 0, 0, 0, 0, 0,
                ]);

                #[cfg(not(feature = "asm"))]
                let tmp = $field::montgomery_reduce_short(
                    elt.0[0], elt.0[1], elt.0[2], elt.0[3], elt.0[4], elt.0[5],
                );

                tmp.0
            }
        }

        impl From<$field> for FqBytes {
            fn from(value: $field) -> FqBytes {
                value.to_repr()
            }
        }

        impl<'a> From<&'a $field> for FqBytes {
            fn from(value: &'a $field) -> FqBytes {
                value.to_repr()
            }
        }

        impl From<$field> for i128 {
            fn from(value: $field) -> i128 {
                let tmp: [u64; 6] = value.into();
                if tmp[2] == 0 && tmp[3] == 0 {
                    i128::from(tmp[0]) | (i128::from(tmp[1]) << 64)
                } else {
                    // modulus - tmp
                    let (a0, borrow) = $modulus.0[0].overflowing_sub(tmp[0]);
                    let (a1, _) = sbb($modulus.0[1], tmp[1], borrow);

                    -(i128::from(a0) | (i128::from(a1) << 64))
                }
            }
        }

        impl FieldExt for $field {
            const MODULUS: &'static str = $modulus_str;
            const TWO_INV: Self = $two_inv;
            const ROOT_OF_UNITY_INV: Self = $root_of_unity_inv;
            const DELTA: Self = $delta;
            const ZETA: Self = $zeta;

            fn from_u128(v: u128) -> Self {
                $field::from_raw_unchecked([v as u64, (v >> 64) as u64, 0, 0, 0, 0])
            }

            /// Converts a 512-bit little endian integer into
            /// a `$field` by reducing by the modulus.
            fn from_bytes_wide(bytes: &[u8; 64]) -> $field {
                $field::from_u512([
                    u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
                    u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
                    u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
                    u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
                    u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
                    u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
                    u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
                    u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
                ])
            }

            fn get_lower_128(&self) -> u128 {
                let tmp = $field::montgomery_reduce_short(
                    self.0[0], self.0[1], self.0[2], self.0[3], self.0[4], self.0[5],
                );

                u128::from(tmp.0[0]) | (u128::from(tmp.0[1]) << 64)
            }
        }

        // Assume Fq is stored in a 48-byte (384-bit) object
        impl $crate::serde::SerdeObject for $field {
            fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
                debug_assert_eq!(bytes.len(), 48);
                let inner = [0, 8, 16, 24, 32, 40]
                    .map(|i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap()));
                Self(inner)
            }
            fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
                if bytes.len() != 48 {
                    return None;
                }
                let elt = Self::from_raw_bytes_unchecked(bytes);
                Self::is_less_than(&elt.0, &$modulus.0).then(|| elt)
            }
            fn to_raw_bytes(&self) -> Vec<u8> {
                let mut res = Vec::with_capacity(48);
                for limb in self.0.iter() {
                    res.extend_from_slice(&limb.to_le_bytes());
                }
                res
            }
            fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
                let inner = [(); 6].map(|_| {
                    let mut buf = [0; 8];
                    reader.read_exact(&mut buf).unwrap();
                    u64::from_le_bytes(buf)
                });
                Self(inner)
            }
            fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
                let mut inner = [0u64; 6];
                for limb in inner.iter_mut() {
                    let mut buf = [0; 8];
                    reader.read_exact(&mut buf)?;
                    *limb = u64::from_le_bytes(buf);
                }
                let elt = Self(inner);
                Self::is_less_than(&elt.0, &$modulus.0)
                    .then(|| elt)
                    .ok_or_else(|| {
                        std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "input number is not less than field modulus",
                        )
                    })
            }
            fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
                for limb in self.0.iter() {
                    writer.write_all(&limb.to_le_bytes())?;
                }
                Ok(())
            }
        }
    };
}

// Called in fq.rs: field_arithmetic_bls12_381!(Fq, MODULUS, INV, sparse);
#[macro_export]
macro_rules! field_arithmetic_bls12_381 {
    ($field:ident, $modulus:ident, $inv:ident, $field_type:ident) => {
        field_specific_bls12_381!($field, $modulus, $inv, $field_type);
        impl $field {
            /// Doubles this field element.
            #[inline]
            pub const fn double(&self) -> $field {
                self.add(self)
            }

            /// Squares this element.
            #[inline]
            pub const fn square(&self) -> $field {
                // Not sure why this 6 limbs adataion from 4 limbs isn't working
                // let r0;
                // let mut r1;
                // let mut r2;
                // let mut r3;
                // let mut r4;
                // let mut r5;
                // let mut r6;
                // let mut r7;
                // let mut r8;
                // let mut r9;
                // let mut r10;
                // let mut r11;
                // let mut carry;
                // let mut carry2;

                // (r1, carry) = self.0[0].widening_mul(self.0[1]);
                // (r2, carry) = self.0[0].carrying_mul(self.0[2], carry);
                // (r3, carry) = self.0[0].carrying_mul(self.0[3], carry);
                // (r4, carry) = self.0[0].carrying_mul(self.0[4], carry);
                // (r5, r6) = self.0[0].carrying_mul(self.0[5], carry);

                // (r3, carry) = macx(r3, self.0[1], self.0[2]);
                // (r4, carry) = mac(r4, self.0[1], self.0[3], carry);
                // (r5, carry) = mac(r5, self.0[1], self.0[4], carry);
                // (r6, r7) = mac(r6, self.0[1], self.0[5], carry);

                // (r5, carry) = macx(r5, self.0[2], self.0[3]);
                // (r6, carry) = mac(r6, self.0[2], self.0[4], carry);
                // (r7, r8) = mac(r7, self.0[2], self.0[5], carry);

                // (r7, carry) = macx(r7, self.0[3], self.0[4]);
                // (r8, r9) = mac(r8, self.0[3], self.0[5], carry);

                // (r9, r10) = macx(r9, self.0[4], self.0[5]);

                // r11 = r10 >> 63;
                // r10 = (r10 << 1) | (r9 >> 63);
                // r9 = (r9 << 1) | (r8 >> 63);
                // r8 = (r8 << 1) | (r7 >> 63);
                // r7 = (r7 << 1) | (r6 >> 63);
                // r6 = (r6 << 1) | (r5 >> 63);
                // r5 = (r5 << 1) | (r4 >> 63);
                // r4 = (r4 << 1) | (r3 >> 63);
                // r3 = (r3 << 1) | (r2 >> 63);
                // r2 = (r2 << 1) | (r1 >> 63);
                // r1 <<= 1;

                // (r0, carry) = self.0[0].widening_mul(self.0[0]);
                // (r1, carry2) = r1.overflowing_add(carry);
                // (r2, carry) = mac(r2, self.0[1], self.0[1], carry2 as u64);
                // (r3, carry2) = r3.overflowing_add(carry);
                // (r4, carry) = mac(r4, self.0[2], self.0[2], carry2 as u64);
                // (r5, carry2) = r5.overflowing_add(carry);
                // (r6, carry) = mac(r6, self.0[3], self.0[3], carry2 as u64);
                // (r7, carry2) = r7.overflowing_add(carry);
                // (r8, carry) = mac(r8, self.0[4], self.0[4], carry2 as u64);
                // (r9, carry2) = r9.overflowing_add(carry);
                // (r10, carry) = mac(r10, self.0[5], self.0[5], carry2 as u64);
                // r11 = r11.wrapping_add(carry);

                // $field::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)

                let (t1, carry) = mac(0, self.0[0], self.0[1], 0);
                let (t2, carry) = mac(0, self.0[0], self.0[2], carry);
                let (t3, carry) = mac(0, self.0[0], self.0[3], carry);
                let (t4, carry) = mac(0, self.0[0], self.0[4], carry);
                let (t5, t6) = mac(0, self.0[0], self.0[5], carry);

                let (t3, carry) = mac(t3, self.0[1], self.0[2], 0);
                let (t4, carry) = mac(t4, self.0[1], self.0[3], carry);
                let (t5, carry) = mac(t5, self.0[1], self.0[4], carry);
                let (t6, t7) = mac(t6, self.0[1], self.0[5], carry);

                let (t5, carry) = mac(t5, self.0[2], self.0[3], 0);
                let (t6, carry) = mac(t6, self.0[2], self.0[4], carry);
                let (t7, t8) = mac(t7, self.0[2], self.0[5], carry);

                let (t7, carry) = mac(t7, self.0[3], self.0[4], 0);
                let (t8, t9) = mac(t8, self.0[3], self.0[5], carry);

                let (t9, t10) = mac(t9, self.0[4], self.0[5], 0);

                let t11 = t10 >> 63;
                let t10 = (t10 << 1) | (t9 >> 63);
                let t9 = (t9 << 1) | (t8 >> 63);
                let t8 = (t8 << 1) | (t7 >> 63);
                let t7 = (t7 << 1) | (t6 >> 63);
                let t6 = (t6 << 1) | (t5 >> 63);
                let t5 = (t5 << 1) | (t4 >> 63);
                let t4 = (t4 << 1) | (t3 >> 63);
                let t3 = (t3 << 1) | (t2 >> 63);
                let t2 = (t2 << 1) | (t1 >> 63);
                let t1 = t1 << 1;

                let (t0, carry) = mac(0, self.0[0], self.0[0], 0);
                let (t1, carry) = adc_u64(t1, 0, carry);
                let (t2, carry) = mac(t2, self.0[1], self.0[1], carry);
                let (t3, carry) = adc_u64(t3, 0, carry);
                let (t4, carry) = mac(t4, self.0[2], self.0[2], carry);
                let (t5, carry) = adc_u64(t5, 0, carry);
                let (t6, carry) = mac(t6, self.0[3], self.0[3], carry);
                let (t7, carry) = adc_u64(t7, 0, carry);
                let (t8, carry) = mac(t8, self.0[4], self.0[4], carry);
                let (t9, carry) = adc_u64(t9, 0, carry);
                let (t10, carry) = mac(t10, self.0[5], self.0[5], carry);
                let (t11, _) = adc_u64(t11, 0, carry);

                Self::montgomery_reduce(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11)
            }

            /// Subtracts `rhs` from `self`, returning the result.
            #[inline]
            pub const fn sub(&self, rhs: &Self) -> Self {
                let (d0, borrow) = self.0[0].overflowing_sub(rhs.0[0]);
                let (d1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
                let (d2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
                let (d3, borrow) = sbb(self.0[3], rhs.0[3], borrow);
                let (d4, borrow) = sbb(self.0[4], rhs.0[4], borrow);
                let (d5, borrow) = sbb(self.0[5], rhs.0[5], borrow);

                let borrow = 0u64.wrapping_sub(borrow as u64);
                // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
                // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
                let (d0, carry) = d0.overflowing_add($modulus.0[0] & borrow);
                let (d1, carry) = adc(d1, $modulus.0[1] & borrow, carry);
                let (d2, carry) = adc(d2, $modulus.0[2] & borrow, carry);
                let (d3, carry) = adc(d3, $modulus.0[3] & borrow, carry);
                let (d4, carry) = adc(d4, $modulus.0[4] & borrow, carry);
                let (d5, _) = adc(d5, $modulus.0[5] & borrow, carry);
                $field([d0, d1, d2, d3, d4, d5])
            }

            /// Negates `self`.
            #[inline]
            pub const fn neg(&self) -> Self {
                if self.0[0] == 0
                    && self.0[1] == 0
                    && self.0[2] == 0
                    && self.0[3] == 0
                    && self.0[4] == 0
                    && self.0[5] == 0
                {
                    return $field([0, 0, 0, 0, 0, 0]);
                }
                // Subtract `self` from `MODULUS` to negate. Ignore the final
                // borrow because it cannot underflow; self is guaranteed to
                // be in the field.
                let (d0, borrow) = $modulus.0[0].overflowing_sub(self.0[0]);
                let (d1, borrow) = sbb($modulus.0[1], self.0[1], borrow);
                let (d2, borrow) = sbb($modulus.0[2], self.0[2], borrow);
                let (d3, borrow) = sbb($modulus.0[3], self.0[3], borrow);
                let (d4, borrow) = sbb($modulus.0[4], self.0[4], borrow);
                let d5 = $modulus.0[5] - (self.0[5] + borrow as u64);

                $field([d0, d1, d2, d3, d4, d5])
            }

            /// Montgomery reduce where last 6 registers are 0
            #[inline(always)]
            pub(crate) const fn montgomery_reduce_short(
                mut r0: u64,
                mut r1: u64,
                mut r2: u64,
                mut r3: u64,
                mut r4: u64,
                mut r5: u64,
            ) -> $field {
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
                let mut k;

                k = r0.wrapping_mul($inv);
                (_, r0) = macx(r0, k, $modulus.0[0]);
                (r1, r0) = mac(r1, k, $modulus.0[1], r0);
                (r2, r0) = mac(r2, k, $modulus.0[2], r0);
                (r3, r0) = mac(r3, k, $modulus.0[3], r0);
                (r4, r0) = mac(r4, k, $modulus.0[4], r0);
                (r5, r0) = mac(r5, k, $modulus.0[5], r0);

                k = r1.wrapping_mul($inv);
                (_, r1) = macx(r1, k, $modulus.0[0]);
                (r2, r1) = mac(r2, k, $modulus.0[1], r1);
                (r3, r1) = mac(r3, k, $modulus.0[2], r1);
                (r4, r1) = mac(r4, k, $modulus.0[3], r1);
                (r5, r1) = mac(r5, k, $modulus.0[4], r1);
                (r0, r1) = mac(r0, k, $modulus.0[5], r1);

                k = r2.wrapping_mul($inv);
                (_, r2) = macx(r2, k, $modulus.0[0]);
                (r3, r2) = mac(r3, k, $modulus.0[1], r2);
                (r4, r2) = mac(r4, k, $modulus.0[2], r2);
                (r5, r2) = mac(r5, k, $modulus.0[3], r2);
                (r0, r2) = mac(r0, k, $modulus.0[4], r2);
                (r1, r2) = mac(r1, k, $modulus.0[5], r2);

                k = r3.wrapping_mul($inv);
                (_, r3) = macx(r3, k, $modulus.0[0]);
                (r4, r3) = mac(r4, k, $modulus.0[1], r3);
                (r5, r3) = mac(r5, k, $modulus.0[2], r3);
                (r0, r3) = mac(r0, k, $modulus.0[3], r3);
                (r1, r3) = mac(r1, k, $modulus.0[4], r3);
                (r2, r3) = mac(r2, k, $modulus.0[5], r3);

                k = r4.wrapping_mul($inv);
                (_, r4) = macx(r4, k, $modulus.0[0]);
                (r5, r4) = mac(r5, k, $modulus.0[1], r4);
                (r0, r4) = mac(r0, k, $modulus.0[2], r4);
                (r1, r4) = mac(r1, k, $modulus.0[3], r4);
                (r2, r4) = mac(r2, k, $modulus.0[4], r4);
                (r3, r4) = mac(r3, k, $modulus.0[5], r4);

                k = r5.wrapping_mul($inv);
                (_, r5) = macx(r5, k, $modulus.0[0]);
                (r0, r5) = mac(r0, k, $modulus.0[1], r5);
                (r1, r5) = mac(r1, k, $modulus.0[2], r5);
                (r2, r5) = mac(r2, k, $modulus.0[3], r5);
                (r3, r5) = mac(r3, k, $modulus.0[4], r5);
                (r4, r5) = mac(r4, k, $modulus.0[5], r5);

                // Result may be within MODULUS of the correct value
                (&$field([r0, r1, r2, r3, r4, r5])).sub(&$modulus)
            }

            #[inline(always)]
            fn is_less_than(x: &[u64; 6], y: &[u64; 6]) -> bool {
                let (_, borrow) = x[0].overflowing_sub(y[0]);
                let (_, borrow) = x[1].borrowing_sub(y[1], borrow);
                let (_, borrow) = x[2].borrowing_sub(y[2], borrow);
                let (_, borrow) = x[3].borrowing_sub(y[3], borrow);
                let (_, borrow) = x[4].borrowing_sub(y[4], borrow);
                let (_, borrow) = x[5].borrowing_sub(y[5], borrow);
                borrow
            }
        }
    };
}

#[macro_export]
macro_rules! field_specific_bls12_381 {
    ($field:ident, $modulus:ident, $inv:ident, sparse) => {
        impl $field {
            /// Adds `rhs` to `self`, returning the result.
            #[inline]
            pub const fn add(&self, rhs: &Self) -> Self {
                let (d0, carry) = self.0[0].overflowing_add(rhs.0[0]);
                let (d1, carry) = self.0[1].carrying_add(rhs.0[1], carry);
                let (d2, carry) = self.0[2].carrying_add(rhs.0[2], carry);
                let (d3, carry) = self.0[3].carrying_add(rhs.0[3], carry);
                let (d4, carry) = self.0[4].carrying_add(rhs.0[4], carry);
                // sparse means that the sum won't overflow the top register
                let d5 = self.0[5] + rhs.0[5] + carry as u64;

                // Attempt to subtract the modulus, to ensure the value
                // is smaller than the modulus.
                (&$field([d0, d1, d2, d3, d4, d5])).sub(&$modulus)
            }

            /// Multiplies `rhs` by `self`, returning the result.
            #[inline]
            pub const fn mul(&self, rhs: &Self) -> $field {
                // When the highest bit in the top register of the modulus is 0 and the rest of the bits are not all 1, we can use an optimization from the gnark team: https://hackmd.io/@gnark/modular_multiplication

                // I think this is exactly the same as the previous `mul` implementation with `montgomery_reduce` at the end (where `montgomery_reduce` is slightly cheaper in "sparse" setting)
                // Maybe the use of mutable variables is slightly more efficient?
                let mut r0;
                let mut r1;
                let mut t0;
                let mut t1;
                let mut t2;
                let mut t3;
                let mut t4;
                let mut t5;
                let mut k;

                (t0, r0) = self.0[0].widening_mul(rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = self.0[0].carrying_mul(rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = self.0[0].carrying_mul(rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = self.0[0].carrying_mul(rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = self.0[0].carrying_mul(rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = self.0[0].carrying_mul(rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                (t0, r0) = macx(t0, self.0[1], rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = mac(t1, self.0[1], rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = mac(t2, self.0[1], rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = mac(t3, self.0[1], rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = mac(t4, self.0[1], rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = mac(t5, self.0[1], rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                (t0, r0) = macx(t0, self.0[2], rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = mac(t1, self.0[2], rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = mac(t2, self.0[2], rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = mac(t3, self.0[2], rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = mac(t4, self.0[2], rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = mac(t5, self.0[2], rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                (t0, r0) = macx(t0, self.0[3], rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = mac(t1, self.0[3], rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = mac(t2, self.0[3], rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = mac(t3, self.0[3], rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = mac(t4, self.0[3], rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = mac(t5, self.0[3], rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                (t0, r0) = macx(t0, self.0[4], rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = mac(t1, self.0[4], rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = mac(t2, self.0[4], rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = mac(t3, self.0[4], rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = mac(t4, self.0[4], rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = mac(t5, self.0[4], rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                (t0, r0) = macx(t0, self.0[5], rhs.0[0]);
                k = t0.wrapping_mul($inv);
                (_, r1) = macx(t0, k, $modulus.0[0]);
                (t1, r0) = mac(t1, self.0[5], rhs.0[1], r0);
                (t0, r1) = mac(t1, k, $modulus.0[1], r1);
                (t2, r0) = mac(t2, self.0[5], rhs.0[2], r0);
                (t1, r1) = mac(t2, k, $modulus.0[2], r1);
                (t3, r0) = mac(t3, self.0[5], rhs.0[3], r0);
                (t2, r1) = mac(t3, k, $modulus.0[3], r1);
                (t4, r0) = mac(t4, self.0[5], rhs.0[4], r0);
                (t3, r1) = mac(t4, k, $modulus.0[4], r1);
                (t5, r0) = mac(t5, self.0[5], rhs.0[5], r0);
                (t4, r1) = mac(t5, k, $modulus.0[5], r1);
                t5 = r0 + r1;

                // Result may be within MODULUS of the correct value
                (&$field([t0, t1, t2, t3, t4, t5])).sub(&$modulus)
            }

            #[allow(clippy::too_many_arguments)]
            #[inline(always)]
            pub(crate) const fn montgomery_reduce(
                r0: u64,
                mut r1: u64,
                mut r2: u64,
                mut r3: u64,
                mut r4: u64,
                mut r5: u64,
                mut r6: u64,
                mut r7: u64,
                mut r8: u64,
                mut r9: u64,
                mut r10: u64,
                mut r11: u64,
            ) -> $field {
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
                let mut k;
                let mut carry;
                let mut carry2;

                k = r0.wrapping_mul($inv);
                (_, carry) = macx(r0, k, $modulus.0[0]);
                (r1, carry) = mac(r1, k, $modulus.0[1], carry);
                (r2, carry) = mac(r2, k, $modulus.0[2], carry);
                (r3, carry) = mac(r3, k, $modulus.0[3], carry);
                (r4, carry) = mac(r4, k, $modulus.0[4], carry);
                (r5, carry) = mac(r5, k, $modulus.0[5], carry);
                (r6, carry2) = r6.overflowing_add(carry);

                k = r1.wrapping_mul($inv);
                (_, carry) = macx(r1, k, $modulus.0[0]);
                (r2, carry) = mac(r2, k, $modulus.0[1], carry);
                (r3, carry) = mac(r3, k, $modulus.0[2], carry);
                (r4, carry) = mac(r4, k, $modulus.0[3], carry);
                (r5, carry) = mac(r5, k, $modulus.0[4], carry);
                (r6, carry) = mac(r6, k, $modulus.0[5], carry);
                (r7, carry2) = adc(r7, carry, carry2);

                k = r2.wrapping_mul($inv);
                (_, carry) = macx(r2, k, $modulus.0[0]);
                (r3, carry) = mac(r3, k, $modulus.0[1], carry);
                (r4, carry) = mac(r4, k, $modulus.0[2], carry);
                (r5, carry) = mac(r5, k, $modulus.0[3], carry);
                (r6, carry) = mac(r6, k, $modulus.0[4], carry);
                (r7, carry) = mac(r7, k, $modulus.0[5], carry);
                (r8, carry2) = adc(r8, carry, carry2);

                k = r3.wrapping_mul($inv);
                (_, carry) = macx(r3, k, $modulus.0[0]);
                (r4, carry) = mac(r4, k, $modulus.0[1], carry);
                (r5, carry) = mac(r5, k, $modulus.0[2], carry);
                (r6, carry) = mac(r6, k, $modulus.0[3], carry);
                (r7, carry) = mac(r7, k, $modulus.0[4], carry);
                (r8, carry) = mac(r8, k, $modulus.0[5], carry);
                (r9, carry2) = adc(r9, carry, carry2);

                k = r4.wrapping_mul($inv);
                (_, carry) = macx(r4, k, $modulus.0[0]);
                (r5, carry) = mac(r5, k, $modulus.0[1], carry);
                (r6, carry) = mac(r6, k, $modulus.0[2], carry);
                (r7, carry) = mac(r7, k, $modulus.0[3], carry);
                (r8, carry) = mac(r8, k, $modulus.0[4], carry);
                (r9, carry) = mac(r9, k, $modulus.0[5], carry);
                (r10, carry2) = adc(r10, carry, carry2);

                k = r5.wrapping_mul($inv);
                (_, carry) = macx(r5, k, $modulus.0[0]);
                (r6, carry) = mac(r6, k, $modulus.0[1], carry);
                (r7, carry) = mac(r7, k, $modulus.0[2], carry);
                (r8, carry) = mac(r8, k, $modulus.0[3], carry);
                (r9, carry) = mac(r9, k, $modulus.0[4], carry);
                (r10, carry) = mac(r10, k, $modulus.0[5], carry);
                (r11, _) = adc(r11, carry, carry2);

                // Result may be within MODULUS of the correct value
                (&$field([r6, r7, r8, r9, r10, r11])).sub(&$modulus)
            }
        }
    };
    // below for `dense` doesn't get called currently
    ($field:ident, $modulus:ident, $inv:ident, dense) => {
        impl $field {
            /// Adds `rhs` to `self`, returning the result.
            #[inline]
            pub const fn add(&self, rhs: &Self) -> Self {
                let (d0, carry) = self.0[0].overflowing_add(rhs.0[0]);
                let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
                let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
                let (d3, carry) = adc(self.0[3], rhs.0[3], carry);
                let (d4, carry) = adc(self.0[4], rhs.0[4], carry);
                let (d5, carry) = adc(self.0[5], rhs.0[5], carry);

                // Attempt to subtract the modulus, to ensure the value
                // is smaller than the modulus.
                let (d0, borrow) = d0.overflowing_sub($modulus.0[0]);
                let (d1, borrow) = sbb(d1, $modulus.0[1], borrow);
                let (d2, borrow) = sbb(d2, $modulus.0[2], borrow);
                let (d3, borrow) = sbb(d3, $modulus.0[3], borrow);
                let (d4, borrow) = sbb(d4, $modulus.0[4], borrow);
                let (d5, borrow) = sbb(d5, $modulus.0[5], borrow);
                let borrow = (carry as u64).wrapping_sub(borrow as u64);

                let (d0, carry) = d0.overflowing_add($modulus.0[0] & borrow);
                let (d1, carry) = adc(d1, $modulus.0[1] & borrow, carry);
                let (d2, carry) = adc(d2, $modulus.0[2] & borrow, carry);
                let (d3, carry) = adc(d3, $modulus.0[3] & borrow, carry);
                let (d4, carry) = adc(d4, $modulus.0[4] & borrow, carry);
                let (d5, _) = adc(d5, $modulus.0[5] & borrow, carry);

                $field([d0, d1, d2, d3, d4, d5])
            }

            /// Multiplies `rhs` by `self`, returning the result.
            #[inline]
            pub const fn mul(&self, rhs: &Self) -> $field {
                // Schoolbook multiplication

                let (r0, carry) = mac(0, self.0[0], rhs.0[0], 0);
                let (r1, carry) = mac(0, self.0[0], rhs.0[1], carry);
                let (r2, carry) = mac(0, self.0[0], rhs.0[2], carry);
                let (r3, carry) = mac(0, self.0[0], rhs.0[3], carry);
                let (r4, carry) = mac(0, self.0[0], rhs.0[4], carry);
                let (r5, r6) = mac(0, self.0[0], rhs.0[5], carry);

                let (r1, carry) = mac(r1, self.0[1], rhs.0[0], 0);
                let (r2, carry) = mac(r2, self.0[1], rhs.0[1], carry);
                let (r3, carry) = mac(r3, self.0[1], rhs.0[2], carry);
                let (r4, carry) = mac(r4, self.0[1], rhs.0[3], carry);
                let (r5, carry) = mac(r5, self.0[1], rhs.0[4], carry);
                let (r6, r7) = mac(r6, self.0[1], rhs.0[5], carry);

                let (r2, carry) = mac(r2, self.0[2], rhs.0[0], 0);
                let (r3, carry) = mac(r3, self.0[2], rhs.0[1], carry);
                let (r4, carry) = mac(r4, self.0[2], rhs.0[2], carry);
                let (r5, carry) = mac(r5, self.0[2], rhs.0[4], carry);
                let (r6, carry) = mac(r6, self.0[2], rhs.0[5], carry);
                let (r7, r8) = mac(r7, self.0[2], rhs.0[5], carry);

                let (r3, carry) = mac(r3, self.0[3], rhs.0[0], 0);
                let (r4, carry) = mac(r4, self.0[3], rhs.0[1], carry);
                let (r5, carry) = mac(r5, self.0[3], rhs.0[2], carry);
                let (r6, carry) = mac(r5, self.0[3], rhs.0[3], carry);
                let (r7, carry) = mac(r5, self.0[3], rhs.0[4], carry);
                let (r8, r9) = mac(r6, self.0[3], rhs.0[5], carry);

                let (r4, carry) = mac(r4, self.0[4], rhs.0[0], 0);
                let (r5, carry) = mac(r5, self.0[4], rhs.0[1], carry);
                let (r6, carry) = mac(r6, self.0[4], rhs.0[2], carry);
                let (r7, carry) = mac(r7, self.0[4], rhs.0[3], carry);
                let (r8, carry) = mac(r8, self.0[4], rhs.0[4], carry);
                let (r9, r10) = mac(r9, self.0[4], rhs.0[5], carry);

                let (r5, carry) = mac(r5, self.0[5], rhs.0[0], 0);
                let (r6, carry) = mac(r6, self.0[5], rhs.0[1], carry);
                let (r7, carry) = mac(r7, self.0[5], rhs.0[2], carry);
                let (r8, carry) = mac(r8, self.0[5], rhs.0[3], carry);
                let (r9, carry) = mac(r9, self.0[5], rhs.0[4], carry);
                let (r10, r11) = mac(r10, self.0[5], rhs.0[5], carry);

                $field::montgomery_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)
            }

            #[allow(clippy::too_many_arguments)]
            #[inline(always)]
            pub(crate) const fn montgomery_reduce(
                r0: u64,
                mut r1: u64,
                mut r2: u64,
                mut r3: u64,
                mut r4: u64,
                mut r5: u64,
                mut r6: u64,
                mut r7: u64,
            ) -> Self {
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
                let mut k;
                let mut carry;
                let mut carry2;

                k = r0.wrapping_mul($inv);
                (_, carry) = macx(r0, k, $modulus.0[0]);
                (r1, carry) = mac(r1, k, $modulus.0[1], carry);
                (r2, carry) = mac(r2, k, $modulus.0[2], carry);
                (r3, carry) = mac(r3, k, $modulus.0[3], carry);
                (r4, carry) = mac(r4, k, $modulus.0[4], carry);
                (r5, carry) = mac(r5, k, $modulus.0[5], carry);
                (r6, carry2) = r6.overflowing_add(carry);

                k = r1.wrapping_mul($inv);
                (_, carry) = k.carrying_mul($modulus.0[0], r1);
                (r2, carry) = mac(r2, k, $modulus.0[1], carry);
                (r3, carry) = mac(r3, k, $modulus.0[2], carry);
                (r4, carry) = mac(r4, k, $modulus.0[3], carry);
                (r5, carry) = mac(r5, k, $modulus.0[4], carry);
                (r6, carry) = mac(r6, k, $modulus.0[5], carry);
                (r7, carry2) = adc(r7, carry, carry2);

                k = r2.wrapping_mul($inv);
                (_, carry) = macx(r2, k, $modulus.0[0]);
                (r3, carry) = mac(r3, k, $modulus.0[1], carry);
                (r4, carry) = mac(r4, k, $modulus.0[2], carry);
                (r5, carry) = mac(r5, k, $modulus.0[3], carry);
                (r6, carry) = mac(r6, k, $modulus.0[4], carry);
                (r7, carry) = mac(r7, k, $modulus.0[5], carry);
                (r8, carry2) = adc(r8, carry, carry2);

                k = r3.wrapping_mul($inv);
                (_, carry) = macx(r3, k, $modulus.0[0]);
                (r4, carry) = mac(r4, k, $modulus.0[1], carry);
                (r5, carry) = mac(r5, k, $modulus.0[2], carry);
                (r6, carry) = mac(r6, k, $modulus.0[3], carry);
                (r7, carry) = mac(r7, k, $modulus.0[4], carry);
                (r8, carry) = mac(r8, k, $modulus.0[5], carry);
                (r9, carry2) = adc(r9, carry, carry2);

                k = r4.wrapping_mul($inv);
                (_, carry) = macx(r4, k, $modulus.0[0]);
                (r5, carry) = mac(r5, k, $modulus.0[1], carry);
                (r6, carry) = mac(r6, k, $modulus.0[2], carry);
                (r7, carry) = mac(r7, k, $modulus.0[3], carry);
                (r8, carry) = mac(r8, k, $modulus.0[4], carry);
                (r9, carry) = mac(r9, k, $modulus.0[5], carry);
                (r10, carry2) = adc(r10, carry, carry2);

                k = r5.wrapping_mul($inv);
                (_, carry) = macx(r5, k, $modulus.0[0]);
                (r6, carry) = mac(r6, k, $modulus.0[1], carry);
                (r7, carry) = mac(r7, k, $modulus.0[2], carry);
                (r8, carry) = mac(r8, k, $modulus.0[3], carry);
                (r9, carry) = mac(r9, k, $modulus.0[4], carry);
                (r10, carry) = mac(r10, k, $modulus.0[5], carry);
                (r11, carry2) = adc(r11, carry, carry2);

                // Result may be within MODULUS of the correct value
                let mut borrow;
                (r6, borrow) = r6.overflowing_sub($modulus.0[0]);
                (r7, borrow) = sbb(r7, $modulus.0[1], borrow);
                (r8, borrow) = sbb(r8, $modulus.0[2], borrow);
                (r9, borrow) = sbb(r9, $modulus.0[3], borrow);
                (r10, borrow) = sbb(r10, $modulus.0[4], borrow);
                (r11, borrow) = sbb(r11, $modulus.0[5], borrow);
                let borrow = (carry2 as u64).wrapping_sub(borrow as u64);

                (r6, carry2) = r6.overflowing_add($modulus.0[0] & borrow);
                (r7, carry2) = adc(r7, $modulus.0[1] & borrow, carry2);
                (r8, carry2) = adc(r8, $modulus.0[2] & borrow, carry2);
                (r9, carry2) = adc(r9, $modulus.0[3] & borrow, carry2);
                (r10, carry2) = adc(r10, $modulus.0[4] & borrow, carry2);
                (r11, _) = adc(r11, $modulus.0[5] & borrow, carry2);
                $field([r6, r7, r8, r9, r10, r11])
            }
        }
    };
}
