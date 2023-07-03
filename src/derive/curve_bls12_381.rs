#[macro_export]
macro_rules! new_curve_impl_bls12_381 {
    (($($privacy:tt)*),
    $name:ident,
    $name_affine:ident,
    $name_compressed:ident,
    $compressed_size:expr,
    $base:ident,
    $scalar:ident,
    $generator:expr,
    $constant_b:expr,
    $curve_id:literal,
    ) => {

        #[derive(Copy, Clone, Debug, Serialize, Deserialize)]
        $($privacy)* struct $name {
            pub x: $base,
            pub y: $base,
            pub z: $base,
        }

        #[derive(Copy, Clone)]
        $($privacy)* struct $name_affine {
            pub x: $base,
            pub y: $base,
            pub infinity: Choice,
        }

        #[derive(Copy, Clone, Hash)]
        $($privacy)* struct $name_compressed([u8; $compressed_size]);

        impl $name {
            pub fn generator() -> Self {
                let generator = $name_affine::generator();
                Self {
                    x: generator.x,
                    y: generator.y,
                    z: $base::one(),
                }
            }

            const fn curve_constant_b() -> $base {
                $name_affine::curve_constant_b()
            }
        }

        impl $name_affine {
            pub fn generator() -> Self {
                Self {
                    x: $generator.0,
                    y: $generator.1,
                    infinity: Choice::from(0u8),
                }
            }

            const fn curve_constant_b() -> $base {
                $constant_b
            }

            pub fn random(mut rng: impl RngCore) -> Self {
                loop {
                    let x = $base::random(&mut rng);
                    let ysign = (rng.next_u32() % 2) as u8;

                    let x3 = x.square() * x;
                    let y = (x3 + $name::curve_constant_b()).sqrt();
                    if let Some(y) = Option::<$base>::from(y) {
                        let sign = y.to_bytes()[0] & 1;
                        let y = if ysign ^ sign == 0 { y } else { -y };

                        let p = $name_affine {
                            x,
                            y,
                            infinity: 0.into(),
                        };


                        use $crate::group::cofactor::CofactorGroup;
                        let p = p.to_curve();
                        return p.clear_cofactor().to_affine()
                    }
                }
            }
        }

        // Compressed

        impl std::fmt::Debug for $name_compressed {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                self.0[..].fmt(f)
            }
        }

        impl Default for $name_compressed {
            fn default() -> Self {
                $name_compressed([0; $compressed_size])
            }
        }

        impl AsRef<[u8]> for $name_compressed {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }

        impl AsMut<[u8]> for $name_compressed {
            fn as_mut(&mut self) -> &mut [u8] {
                &mut self.0
            }
        }


        // Jacobian implementations

        impl<'a> From<&'a $name_affine> for $name {
            fn from(p: &'a $name_affine) -> $name {
                p.to_curve()
            }
        }

        impl From<$name_affine> for $name {
            fn from(p: $name_affine) -> $name {
                p.to_curve()
            }
        }

        impl Default for $name {
            fn default() -> $name {
                $name::identity()
            }
        }

        impl subtle::ConstantTimeEq for $name {
            fn ct_eq(&self, other: &Self) -> Choice {
                let x1 = self.x * other.z;
                let x2 = other.x * self.z;

                let y1 = self.y * other.z;
                let y2 = other.y * self.z;

                let self_is_zero = self.is_identity();
                let other_is_zero = other.is_identity();

                (self_is_zero & other_is_zero) // Both point at infinity
                            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
                // Neither point at infinity, coordinates are the same
            }

        }

        impl subtle::ConditionallySelectable for $name {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $name {
                    x: $base::conditional_select(&a.x, &b.x, choice),
                    y: $base::conditional_select(&a.y, &b.y, choice),
                    z: $base::conditional_select(&a.z, &b.z, choice),
                }
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.ct_eq(other).into()
            }
        }

        impl cmp::Eq for $name {}

        impl CurveExt for $name {

            type ScalarExt = $scalar;
            type Base = $base;
            type AffineExt = $name_affine;

            const CURVE_ID: &'static str = $curve_id;

            fn endo(&self) -> Self {
                self.endomorphism_base()
            }

            fn jacobian_coordinates(&self) -> ($base, $base, $base) {
               (self.x, self.y, self.z)
            }


            fn hash_to_curve<'a>(_: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a> {
                unimplemented!();
            }

            fn is_on_curve(&self) -> Choice {
                (self.y.square() * self.z).ct_eq(&(self.x.square() * self.x + self.z.square() * self.z * $name::curve_constant_b()))
                | self.z.is_zero()
            }

            fn b() -> Self::Base {
                $name::curve_constant_b()
            }

            fn a() -> Self::Base {
                Self::Base::zero()
            }

            fn new_jacobian(x: Self::Base, y: Self::Base, z: Self::Base) -> CtOption<Self> {
                let p = $name { x, y, z };
                CtOption::new(p, p.is_on_curve())
            }
        }

        impl group::Curve for $name {

            type AffineRepr = $name_affine;

            /// Converts a batch of `G1Projective` elements into `G1Affine` elements. This
            /// function will panic if `p.len() != q.len()`.
            fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
                assert_eq!(p.len(), q.len());

                let mut acc = $base::one();
                for (p, q) in p.iter().zip(q.iter_mut()) {
                    // We use the `x` field of $name_affine to store the product
                    // of previous z-coordinates seen.
                    q.x = acc;

                    // We will end up skipping all identities in p
                    acc = $base::conditional_select(&(acc * p.z), &acc, p.is_identity());
                }

                // This is the inverse, as all z-coordinates are nonzero and the ones
                // that are not are skipped.
                acc = acc.invert().unwrap();

                for (p, q) in p.iter().rev().zip(q.iter_mut().rev()) {
                    let skip = p.is_identity();

                    // Compute tmp = 1/z
                    let tmp = q.x * acc;

                    // Cancel out z-coordinate in denominator of `acc`
                    acc = $base::conditional_select(&(acc * p.z), &acc, skip);

                    // Set the coordinates to the correct value
                    q.x = p.x * tmp;
                    q.y = p.y * tmp;
                    q.infinity = Choice::from(0u8);

                    *q = $name_affine::conditional_select(&q, &$name_affine::identity(), skip);
                }
            }

            fn to_affine(&self) -> Self::AffineRepr {
                let zinv = self.z.invert().unwrap_or($base::zero());
                let x = self.x * zinv;
                let y = self.y * zinv;

                let tmp = $name_affine {
                    x,
                    y,
                    infinity: Choice::from(0u8),
                };

                $name_affine::conditional_select(&tmp, &$name_affine::identity(), zinv.is_zero())
            }
        }

        impl group::Group for $name {  // G1, G2
            type Scalar = $scalar;

            fn random(mut rng: impl RngCore) -> Self {
                $name_affine::random(&mut rng).to_curve()
            }

            fn double(&self) -> Self {
                let t0 = self.y.square();
                let z3 = t0 + t0;
                let z3 = z3 + z3;
                let z3 = z3 + z3;
                let t1 = self.y * self.z;
                let t2 = self.z.square();
                let t2 = $name::mul_by_3b(t2);
                let x3 = t2 * z3;
                let y3 = t0 + t2;
                let z3 = t1 * z3;
                let t1 = t2 + t2;
                let t2 = t1 + t2;
                let t0 = t0 - t2;
                let y3 = t0 * y3;
                let y3 = x3 + y3;
                let t1 = self.x * self.y;
                let x3 = t0 * t1;
                let x3 = x3 + x3;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&tmp, &$name::identity(), self.is_identity())
            }

            fn generator() -> Self {
                $name::generator()
            }

            fn identity() -> Self {
                Self {
                    x: $base::zero(),
                    y: $base::one(),
                    z: $base::zero(),
                }
            }

            fn is_identity(&self) -> Choice {
                self.z.is_zero()
            }
        }

        impl GroupEncoding for $name { // G1
            type Repr = $name_compressed;

            fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
                $name_affine::from_bytes(bytes).map(Self::from)
            }

            fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
                $name_affine::from_bytes(bytes).map(Self::from)
            }

            fn to_bytes(&self) -> Self::Repr {
                $name_affine::from(self).to_bytes()  // G1Affine
            }
        }

        impl $crate::serde::SerdeObject for $name {
            fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
                debug_assert_eq!(bytes.len(), 3 * $base::size());
                let [x, y, z] = [0, 1, 2]
                    .map(|i| $base::from_raw_bytes_unchecked(&bytes[i * $base::size()..(i + 1) * $base::size()]));
                Self { x, y, z }
            }
            fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
                if bytes.len() != 3 * $base::size() {
                    return None;
                }
                let [x, y, z] =
                    [0, 1, 2].map(|i| $base::from_raw_bytes(&bytes[i * $base::size()..(i + 1) * $base::size()]));
                x.zip(y).zip(z).and_then(|((x, y), z)| {
                    let res = Self { x, y, z };
                    // Check that the point is on the curve.
                    bool::from(res.is_on_curve()).then(|| res)
                })
            }
            fn to_raw_bytes(&self) -> Vec<u8> {
                let mut res = Vec::with_capacity(3 * $base::size());
                Self::write_raw(self, &mut res).unwrap();
                res
            }
            fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
                let [x, y, z] = [(); 3].map(|_| $base::read_raw_unchecked(reader));
                Self { x, y, z }
            }
            fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
                let x = $base::read_raw(reader)?;
                let y = $base::read_raw(reader)?;
                let z = $base::read_raw(reader)?;
                Ok(Self { x, y, z })
            }
            fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
                self.x.write_raw(writer)?;
                self.y.write_raw(writer)?;
                self.z.write_raw(writer)
            }
        }

        impl group::prime::PrimeGroup for $name {}

        impl group::prime::PrimeCurve for $name {
            type Affine = $name_affine;
        }

        impl group::cofactor::CofactorCurve for $name {
            type Affine = $name_affine;
        }

        impl Group for $name {
            type Scalar = $scalar;

            fn group_zero() -> Self {
                Self::identity()
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

        // Affine implementations

        impl std::fmt::Debug for $name_affine {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                if self.is_identity().into() {
                    write!(f, "Infinity")
                } else {
                    write!(f, "({:?}, {:?})", self.x, self.y)
                }
            }
        }

        impl<'a> From<&'a $name> for $name_affine {
            fn from(p: &'a $name) -> $name_affine {
                p.to_affine()
            }
        }

        impl From<$name> for $name_affine {
            fn from(p: $name) -> $name_affine {
                p.to_affine()
            }
        }

        impl Default for $name_affine {
            fn default() -> $name_affine {
                $name_affine::identity()
            }
        }

        impl subtle::ConstantTimeEq for $name_affine {
            fn ct_eq(&self, other: &Self) -> Choice {
                // The only cases in which two points are equal are
                // 1. infinity is set on both
                // 2. infinity is not set on both, and their coordinates are equal

                (self.infinity & other.infinity)
                    | ((!self.infinity)
                        & (!other.infinity)
                        & self.x.ct_eq(&other.x)
                        & self.y.ct_eq(&other.y))
            }
        }

        impl subtle::ConditionallySelectable for $name_affine {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                $name_affine {
                    x: $base::conditional_select(&a.x, &b.x, choice),
                    y: $base::conditional_select(&a.y, &b.y, choice),
                    infinity: Choice::conditional_select(&a.infinity, &b.infinity, choice),
                }
            }
        }

        impl cmp::Eq for $name_affine {}

        impl cmp::PartialEq for $name_affine {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                bool::from(self.ct_eq(other))
            }
        }

        impl group::GroupEncoding for $name_affine {
            type Repr = $name_compressed;

            fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {

                Self::from_compressed(&bytes.0)
            }

            fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
                Self::from_bytes(bytes)
            }

            fn to_bytes(&self) -> Self::Repr {
                $name_compressed(self.to_compressed())
            }
        }

        // TODO [serde] Add support for BLS12-381
        // impl $crate::serde::SerdeObject for $name_affine {
        //     fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        //         debug_assert_eq!(bytes.len(), 2 * $base::size());
        //         let [x, y] =
        //             [0, $base::size()].map(|i| $base::from_raw_bytes_unchecked(&bytes[i..i + $base::size()]));
        //         Self { x, y }
        //     }
        //     fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        //         if bytes.len() != 2 * $base::size() {
        //             return None;
        //         }
        //         let [x, y] = [0, $base::size()].map(|i| $base::from_raw_bytes(&bytes[i..i + $base::size()]));
        //         x.zip(y).and_then(|(x, y)| {
        //             let res = Self { x, y };
        //             // Check that the point is on the curve.
        //             bool::from(res.is_on_curve()).then(|| res)
        //         })
        //     }
        //     fn to_raw_bytes(&self) -> Vec<u8> {
        //         let mut res = Vec::with_capacity(2 * $base::size());
        //         Self::write_raw(self, &mut res).unwrap();
        //         res
        //     }
        //     fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        //         let [x, y] = [(); 2].map(|_| $base::read_raw_unchecked(reader));
        //         Self { x, y }
        //     }
        //     fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        //         let x = $base::read_raw(reader)?;
        //         let y = $base::read_raw(reader)?;
        //         Ok(Self { x, y })
        //     }
        //     fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        //         self.x.write_raw(writer)?;
        //         self.y.write_raw(writer)
        //     }
        // }

        impl group::prime::PrimeCurveAffine for $name_affine {
            type Curve = $name;
            type Scalar = $scalar;


            fn generator() -> Self {
                $name_affine::generator()
            }

            fn identity() -> Self {
                Self {
                    x: $base::zero(),
                    y: $base::one(),
                    infinity: Choice::from(1u8),
                }
            }

            fn is_identity(&self) -> Choice {
                self.infinity
            }

            fn to_curve(&self) -> Self::Curve {
                $name {
                    x: self.x,
                    y: self.y,
                    z: $base::conditional_select(&$base::one(), &$base::zero(), self.infinity),
                }
            }
        }

        impl group::cofactor::CofactorCurveAffine for $name_affine {
            type Curve = $name;
            type Scalar = $scalar;

            fn identity() -> Self {
                <Self as group::prime::PrimeCurveAffine>::identity()
            }

            fn generator() -> Self {
                <Self as group::prime::PrimeCurveAffine>::generator()
            }

            fn is_identity(&self) -> Choice {
                <Self as group::prime::PrimeCurveAffine>::is_identity(self)
            }

            fn to_curve(&self) -> Self::Curve {
                <Self as group::prime::PrimeCurveAffine>::to_curve(self)
            }
        }


        impl CurveAffine for $name_affine {
            type ScalarExt = $scalar;
            type Base = $base;
            type CurveExt = $name;

            fn is_on_curve(&self) -> Choice {
                // y^2 - x^3 - ax ?= b
                (self.y.square() - self.x.square() * self.x).ct_eq(&$name::curve_constant_b())
                    | self.infinity
            }

            fn coordinates(&self) -> CtOption<Coordinates<Self>> {
                Coordinates::from_xy( self.x, self.y )
            }

            fn from_xy(x: Self::Base, y: Self::Base) -> CtOption<Self> {
                let p = $name_affine {
                    x, y, infinity: Choice::from(0u8),
                };
                CtOption::new(p, p.is_on_curve())
            }

            fn a() -> Self::Base {
                Self::Base::zero()
            }

            fn b() -> Self::Base {
                $name::curve_constant_b()
            }
        }


        impl_binops_additive!($name, $name);
        impl_binops_additive!($name, $name_affine);
        impl_binops_additive_specify_output!($name_affine, $name_affine, $name);
        impl_binops_additive_specify_output!($name_affine, $name, $name);
        impl_binops_multiplicative!($name, $scalar);
        impl_binops_multiplicative_mixed!($name_affine, $scalar, $name);

        impl<'a> Neg for &'a $name {
            type Output = $name;

            fn neg(self) -> $name {
                $name {
                    x: self.x,
                    y: -self.y,
                    z: self.z,
                }
            }
        }

        impl Neg for $name {
            type Output = $name;

            fn neg(self) -> $name {
                -&self
            }
        }

        impl<T> Sum<T> for $name
        where
            T: core::borrow::Borrow<$name>,
        {
            fn sum<I>(iter: I) -> Self
            where
                I: Iterator<Item = T>,
            {
                iter.fold(Self::identity(), |acc, item| acc + item.borrow())
            }
        }

        impl<'a, 'b> Add<&'a $name> for &'b $name {
            type Output = $name;

            fn add(self, rhs: &'a $name) -> $name {
                let t0 = self.x * rhs.x;
                let t1 = self.y * rhs.y;
                let t2 = self.z * rhs.z;
                let t3 = self.x + self.y;
                let t4 = rhs.x + rhs.y;
                let t3 = t3 * t4;
                let t4 = t0 + t1;
                let t3 = t3 - t4;
                let t4 = self.y + self.z;
                let x3 = rhs.y + rhs.z;
                let t4 = t4 * x3;
                let x3 = t1 + t2;
                let t4 = t4 - x3;
                let x3 = self.x + self.z;
                let y3 = rhs.x + rhs.z;
                let x3 = x3 * y3;
                let y3 = t0 + t2;
                let y3 = x3 - y3;
                let x3 = t0 + t0;
                let t0 = x3 + t0;
                let t2 = $name::mul_by_3b(t2);
                let z3 = t1 + t2;
                let t1 = t1 - t2;
                let y3 = $name::mul_by_3b(y3);
                let x3 = t4 * y3;
                let t2 = t3 * t1;
                let x3 = t2 - x3;
                let y3 = y3 * t0;
                let t1 = t1 * z3;
                let y3 = t1 + y3;
                let t0 = t0 * t3;
                let z3 = z3 * t4;
                let z3 = z3 + t0;

                $name {
                    x: x3,
                    y: y3,
                    z: z3,
                }
            }
        }

        impl<'a, 'b> Add<&'a $name_affine> for &'b $name {
            type Output = $name;

            fn add(self, rhs: &'a $name_affine) -> $name {
                // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf
                let t0 = self.x * rhs.x;
                let t1 = self.y * rhs.y;
                let t3 = rhs.x + rhs.y;
                let t4 = self.x + self.y;
                let t3 = t3 * t4;
                let t4 = t0 + t1;
                let t3 = t3 - t4;
                let t4 = rhs.y * self.z;
                let t4 = t4 + self.y;
                let y3 = rhs.x * self.z;
                let y3 = y3 + self.x;
                let x3 = t0 + t0;
                let t0 = x3 + t0;
                let t2 = $name::mul_by_3b(self.z);
                let z3 = t1 + t2;
                let t1 = t1 - t2;
                let y3 = $name::mul_by_3b(y3);
                let x3 = t4 * y3;
                let t2 = t3 * t1;
                let x3 = t2 - x3;
                let y3 = y3 * t0;
                let t1 = t1 * z3;
                let y3 = t1 + y3;
                let t0 = t0 * t3;
                let z3 = z3 * t4;
                let z3 = z3 + t0;

                let tmp = $name {
                    x: x3,
                    y: y3,
                    z: z3,
                };

                $name::conditional_select(&tmp, self, rhs.is_identity())
            }
        }

        impl<'a, 'b> Sub<&'a $name> for &'b $name {
            type Output = $name;

            fn sub(self, other: &'a $name) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Sub<&'a $name_affine> for &'b $name {
            type Output = $name;

            fn sub(self, other: &'a $name_affine) -> $name {
                self + (-other)
            }
        }



        #[allow(clippy::suspicious_arithmetic_impl)]
        impl<'a, 'b> Mul<&'b $scalar> for &'a $name {
            type Output = $name;

            // This is a simple double-and-add implementation of point
            // multiplication, moving from most significant to least
            // significant bit of the scalar.

            fn mul(self, other: &'b $scalar) -> Self::Output {
                let mut acc = $name::identity();
                let other = other.to_bytes();
                for bit in other
                    // .to_repr()
                    .iter()
                    .rev()
                    .flat_map(|byte| (0..8).rev().map(move |i| Choice::from((byte >> i) & 1u8)))
                    .skip(1)
                {
                    acc = acc.double();
                    acc = $name::conditional_select(&acc, &(acc + self), bit);
                }
                acc
            }
        }

        impl<'a> Neg for &'a $name_affine {
            type Output = $name_affine;

            fn neg(self) -> $name_affine {
                $name_affine {
                    x: self.x,
                    y: $base::conditional_select(&-self.y, &$base::one(), self.infinity),
                    infinity: self.infinity,
                }
            }
        }

        impl Neg for $name_affine {
            type Output = $name_affine;

            fn neg(self) -> $name_affine {
                -&self
            }
        }

        impl<'a, 'b> Add<&'a $name> for &'b $name_affine {
            type Output = $name;

            fn add(self, rhs: &'a $name) -> $name {
                rhs + self
            }
        }

        impl<'a, 'b> Add<&'a $name_affine> for &'b $name_affine {
            type Output = $name;

            fn add(self, rhs: &'a $name_affine) -> $name {
                if bool::from(self.is_identity()) {
                    rhs.to_curve()
                } else if bool::from(rhs.is_identity()) {
                    self.to_curve()
                } else {
                    if self.x == rhs.x {
                        if self.y == rhs.y {
                            self.to_curve().double()
                        } else {
                            $name::identity()
                        }
                    } else {
                        let h = rhs.x - self.x;
                        let hh = h.square();
                        let i = hh + hh;
                        let i = i + i;
                        let j = h * i;
                        let r = rhs.y - self.y;
                        let r = r + r;
                        let v = self.x * i;
                        let x3 = r.square() - j - v - v;
                        let j = self.y * j;
                        let j = j + j;
                        let y3 = r * (v - x3) - j;
                        let z3 = h + h;

                        $name {
                            x: x3, y: y3, z: z3
                        }
                    }
                }
            }
        }

        impl<'a, 'b> Sub<&'a $name_affine> for &'b $name_affine {
            type Output = $name;

            fn sub(self, other: &'a $name_affine) -> $name {
                self + (-other)
            }
        }

        impl<'a, 'b> Sub<&'a $name> for &'b $name_affine {
            type Output = $name;

            fn sub(self, other: &'a $name) -> $name {
                self + (-other)
            }
        }

        #[allow(clippy::suspicious_arithmetic_impl)]
        impl<'a, 'b> Mul<&'b $scalar> for &'a $name_affine {
            type Output = $name;

            fn mul(self, other: &'b $scalar) -> Self::Output {
                // need to convert from $name_affine to $name
                $name::from(self) * other
            }
        }
    };
}
