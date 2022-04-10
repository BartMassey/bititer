use std::marker::PhantomData;

use num::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Msb0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lsb0;

pub trait BitOrder {
    fn indices<T: PrimInt>() -> Box<dyn Iterator<Item = usize>>;
}

impl BitOrder for Msb0 {
    fn indices<T: PrimInt>() -> Box<dyn Iterator<Item = usize>> {
        let tsize = 8 * std::mem::size_of::<T>();
        Box::new((0..tsize).rev())
    }
}

impl BitOrder for Lsb0 {
    fn indices<T: PrimInt>() -> Box<dyn Iterator<Item = usize>> {
        let tsize = 8 * std::mem::size_of::<T>();
        Box::new(0..tsize)
    }
}

#[derive(Debug, Clone)]
pub struct BitIter<T, I, O> {
    cur: T,
    ncur: usize,
    rest: I,
    order: PhantomData<O>,
}

impl<T, I, O> BitIter<T, I, O>
where
    T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize>,
    I: Iterator<Item = T>,
    O: BitOrder,
{
    pub fn new(rest: I) -> Self {
        Self {
            cur: zero::<T>(),
            ncur: 0,
            rest,
            order: PhantomData,
        }
    }
}

impl<T, I> Iterator for BitIter<T, I, Msb0>
where
    T: PrimInt + std::ops::ShlAssign<usize>,
    I: Iterator<Item = T>,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        let tsize = 8 * std::mem::size_of::<T>();
        if self.ncur == 0 {
            self.cur = self.rest.next()?;
            self.ncur = tsize;
        }
        let top = tsize - 1;
        let mask = one::<T>() << top;
        let bit = mask & self.cur != num::zero();
        self.cur <<= 1;
        self.ncur -= 1;
        Some(bit)
    }
}

impl<T, I> Iterator for BitIter<T, I, Lsb0>
where
    T: PrimInt + std::ops::ShrAssign<usize>,
    I: Iterator<Item = T>,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        let tsize = 8 * std::mem::size_of::<T>();
        if self.ncur == 0 {
            self.cur = self.rest.next()?;
            self.ncur = tsize;
        }
        let bit = one::<T>() & self.cur != zero();
        self.cur >>= 1;
        self.ncur -= 1;
        Some(bit)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn to_bits<T: PrimInt, O: BitOrder>(v: &[T]) -> Vec<bool> {
        let mut result = Vec::new();
        for val in v {
            for i in O::indices::<T>() {
                result.push((one::<T>() << i) & *val != zero::<T>());
            }
        }
        result
    }

    fn test_one_lsb0<T>(v: Vec<T>)
    where
        T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize>,
    {
        let bits = to_bits::<T, Lsb0>(&v);
        let vbits = v.into_iter();
        for (b0, b1) in <BitIter<_, _, Lsb0>>::new(vbits).zip(bits.into_iter()) {
            assert_eq!(b0, b1);
        }
    }

    fn test_one_msb0<T>(v: Vec<T>)
    where
        T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize>,
    {
        let bits = to_bits::<T, Msb0>(&v);
        let vbits = v.into_iter();
        for (b0, b1) in <BitIter<_, _, Msb0>>::new(vbits).zip(bits.into_iter()) {
            assert_eq!(b0, b1);
        }
    }

    #[test]
    fn test_bititer() {
        let v: Vec<u8> = Vec::new();
        test_one_lsb0(v);
        let v: Vec<u8> = Vec::new();
        test_one_msb0(v);

        let r_msb = [false, false, false, true, false, false, true, false];
        let r_lsb = [false, true, false, false, true, false, false, false];
        let l_msb: Vec<bool> = <BitIter<_, _, Msb0>>::new(vec![0x12_u8].into_iter()).collect();
        let l_lsb: Vec<bool> = <BitIter<_, _, Lsb0>>::new(vec![0x12_u8].into_iter()).collect();
        assert_eq!(l_msb, r_msb);
        assert_eq!(l_lsb, r_lsb);

        test_one_msb0(vec![0x12_u8, 0x34]);
        test_one_lsb0(vec![0x12_u8, 0x34]);
        test_one_msb0(vec![0x1234_u16, 0x5678]);
        test_one_lsb0(vec![0x1234_u16, 0x5678]);
        test_one_msb0(vec![-0x1234_i16, -0x5678]);
        test_one_lsb0(vec![-0x1234_i16, -0x5678]);
    }
}
