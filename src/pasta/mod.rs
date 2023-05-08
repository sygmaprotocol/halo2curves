use crate::arithmetic::sbb;
use crate::serde::SerdeObject;
use ff::PrimeField;
pub use pasta_curves::{arithmetic::CurveExt, pallas, vesta, Ep, EpAffine, Eq, EqAffine, Fp, Fq};
use std::convert::TryInto;

impl crate::CurveAffineExt for EpAffine {
    fn batch_add<const COMPLETE: bool, const LOAD_POINTS: bool>(
        _: &mut [Self],
        _: &[u32],
        _: usize,
        _: usize,
        _: &[Self],
        _: &[u32],
    ) {
        unimplemented!();
    }
}

impl crate::CurveAffineExt for EqAffine {
    fn batch_add<const COMPLETE: bool, const LOAD_POINTS: bool>(
        _: &mut [Self],
        _: &[u32],
        _: usize,
        _: usize,
        _: &[Self],
        _: &[u32],
    ) {
        unimplemented!();
    }
}

/// Lexicographic comparison of Montgomery forms.
#[inline(always)]
const fn is_less_than(x: &[u64; 4], y: &[u64; 4]) -> bool {
    let (_, borrow) = sbb(x[0], y[0], 0);
    let (_, borrow) = sbb(x[1], y[1], borrow);
    let (_, borrow) = sbb(x[2], y[2], borrow);
    let (_, borrow) = sbb(x[3], y[3], borrow);
    borrow >> 63 == 1
}

const FP_SIZE: usize = 32;
const FQ_SIZE: usize = 32;

struct AccessibleFp(pub [u64; 4]);

impl From<AccessibleFp> for Fp {
    fn from(fp: AccessibleFp) -> Fp {
        let scalar = unsafe { std::mem::transmute::<AccessibleFp, Fp>(fp) };
        scalar
    }
}

impl From<Fp> for AccessibleFp {
    fn from(scalar: Fp) -> AccessibleFp {
        let fp = unsafe { std::mem::transmute::<Fp, AccessibleFp>(scalar) };
        fp
    }
}

impl SerdeObject for Fp {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), FP_SIZE);
        let inner = [0, 8, 16, 24].map(|i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap()));
        Fp::from(AccessibleFp(inner))
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != FP_SIZE {
            return None;
        }
        let elt = Self::from_raw_bytes_unchecked(bytes);
        Some(elt)
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        // The transmute is the only way to get access to the internal array.
        // Note that this is safe as long as the underlying array length is the same
        // and the types contained are the same too.
        let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&self) };
        let mut res = Vec::with_capacity(FP_SIZE);
        for limb in limbs.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let inner = [(); 4].map(|_| {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf).unwrap();
            u64::from_le_bytes(buf)
        });

        Fp::from(AccessibleFp(inner))
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut inner = [0u64; 4];
        for limb in inner.iter_mut() {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf)?;
            *limb = u64::from_le_bytes(buf);
        }

        let elt = Fp::from(AccessibleFp(inner));
        unsafe {
            is_less_than(&inner, &std::mem::transmute_copy(&Fp::MODULUS))
                .then(|| elt)
                .ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "input number is not less than field modulus",
                    )
                })
        }
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&self) };
        for limb in limbs {
            writer.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }
}

struct AccessibleFq(pub [u64; 4]);

impl From<AccessibleFq> for Fq {
    fn from(fq: AccessibleFq) -> Fq {
        let scalar = unsafe { std::mem::transmute::<AccessibleFq, Fq>(fq) };
        scalar
    }
}

impl From<Fq> for AccessibleFq {
    fn from(scalar: Fq) -> AccessibleFq {
        let fq = unsafe { std::mem::transmute::<Fq, AccessibleFq>(scalar) };
        fq
    }
}

impl SerdeObject for Fq {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), FQ_SIZE);
        let inner = [0, 8, 16, 24].map(|i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap()));
        Fq::from(AccessibleFq(inner))
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != FQ_SIZE {
            return None;
        }
        let elt = Self::from_raw_bytes_unchecked(bytes);
        Some(elt)
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        // The transmute is the only way to get access to the internal array.
        // Note that this is safe as long as the underlying array length is the same
        // and the types contained are the same too.
        let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&self) };
        let mut res = Vec::with_capacity(FQ_SIZE);
        for limb in limbs.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let inner = [(); 4].map(|_| {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf).unwrap();
            u64::from_le_bytes(buf)
        });

        Fq::from(AccessibleFq(inner))
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut inner = [0u64; 4];
        for limb in inner.iter_mut() {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf)?;
            *limb = u64::from_le_bytes(buf);
        }

        let elt = Fq::from(AccessibleFq(inner));
        unsafe {
            is_less_than(&inner, &std::mem::transmute_copy(&Fq::MODULUS))
                .then(|| elt)
                .ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "input number is not less than field modulus",
                    )
                })
        }
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let limbs: [u64; 4] = unsafe { std::mem::transmute_copy(&self) };
        for limb in limbs {
            writer.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }
}

struct AccessiblePallasPoint {
    pub x: Fp,
    pub y: Fp,
    pub z: Fp,
}

impl From<pallas::Point> for AccessiblePallasPoint {
    fn from(p: pallas::Point) -> AccessiblePallasPoint {
        let point = unsafe { std::mem::transmute::<pallas::Point, AccessiblePallasPoint>(p) };
        point
    }
}

impl From<AccessiblePallasPoint> for pallas::Point {
    fn from(ap: AccessiblePallasPoint) -> pallas::Point {
        let p = unsafe { std::mem::transmute::<AccessiblePallasPoint, pallas::Point>(ap) };
        p
    }
}

impl SerdeObject for pallas::Point {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), 3 * FP_SIZE);
        let [x, y, z] =
            [0, 1, 2].map(|i| Fp::from_raw_bytes_unchecked(&bytes[i * FP_SIZE..(i + 1) * FP_SIZE]));

        Self::from(AccessiblePallasPoint { x, y, z })
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 3 * FP_SIZE {
            return None;
        }
        let [x, y, z] =
            [0, 1, 2].map(|i| Fp::from_raw_bytes(&bytes[i * FP_SIZE..(i + 1) * FP_SIZE]));
        x.zip(y).zip(z).and_then(|((x, y), z)| {
            let res = Self::from(AccessiblePallasPoint { x, y, z });
            // Check that the point is on the curve.
            bool::from(res.is_on_curve()).then(|| res)
        })
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(3 * FP_SIZE);
        Self::write_raw(self, &mut res).unwrap();
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let [x, y, z] = [(); 3].map(|_| Fp::read_raw_unchecked(reader));

        Self::from(AccessiblePallasPoint { x, y, z })
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let x = Fp::read_raw(reader)?;
        let y = Fp::read_raw(reader)?;
        let z = Fp::read_raw(reader)?;
        Ok(Self::from(AccessiblePallasPoint { x, y, z }))
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let p = AccessiblePallasPoint::from(*self);
        p.x.write_raw(writer)?;
        p.y.write_raw(writer)?;
        p.z.write_raw(writer)
    }
}

struct AccessibleVestaPoint {
    pub x: Fp,
    pub y: Fp,
    pub z: Fp,
}

impl From<vesta::Point> for AccessibleVestaPoint {
    fn from(p: vesta::Point) -> AccessibleVestaPoint {
        let point = unsafe { std::mem::transmute::<vesta::Point, AccessibleVestaPoint>(p) };
        point
    }
}

impl From<AccessibleVestaPoint> for vesta::Point {
    fn from(ap: AccessibleVestaPoint) -> vesta::Point {
        let p = unsafe { std::mem::transmute::<AccessibleVestaPoint, vesta::Point>(ap) };
        p
    }
}

impl SerdeObject for vesta::Point {
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), 3 * FP_SIZE);
        let [x, y, z] =
            [0, 1, 2].map(|i| Fp::from_raw_bytes_unchecked(&bytes[i * FP_SIZE..(i + 1) * FP_SIZE]));

        Self::from(AccessibleVestaPoint { x, y, z })
    }
    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 3 * FP_SIZE {
            return None;
        }
        let [x, y, z] =
            [0, 1, 2].map(|i| Fp::from_raw_bytes(&bytes[i * FP_SIZE..(i + 1) * FP_SIZE]));
        x.zip(y).zip(z).and_then(|((x, y), z)| {
            let res = Self::from(AccessibleVestaPoint { x, y, z });
            // Check that the point is on the curve.
            bool::from(res.is_on_curve()).then(|| res)
        })
    }
    fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(3 * FP_SIZE);
        Self::write_raw(self, &mut res).unwrap();
        res
    }
    fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let [x, y, z] = [(); 3].map(|_| Fp::read_raw_unchecked(reader));

        Self::from(AccessibleVestaPoint { x, y, z })
    }
    fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let x = Fp::read_raw(reader)?;
        let y = Fp::read_raw(reader)?;
        let z = Fp::read_raw(reader)?;
        Ok(Self::from(AccessibleVestaPoint { x, y, z }))
    }
    fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let p = AccessibleVestaPoint::from(*self);
        p.x.write_raw(writer)?;
        p.y.write_raw(writer)?;
        p.z.write_raw(writer)
    }
}
