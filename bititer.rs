use num::*;

#[derive(Debug, Clone, Copy)]
pub enum BitOrder {
    Msb0,
    Lsb0,
}

#[derive(Debug, Clone)]
pub struct BitIter<T, I> {
    order: BitOrder,
    cur: T,
    ncur: usize,
    rest: I,
}

impl<T, I> BitIter<T, I>
where
    T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize>,
    I: Iterator<Item = T>,
{
    pub fn new(rest: I, order: BitOrder) -> Self {
        Self {
            order,
            cur: zero::<T>(),
            ncur: 0,
            rest,
        }
    }
}


impl<T, I> Iterator for BitIter<T, I>
where
    T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize>,
    I: Iterator<Item = T>,
{
    type Item = bool;
    
    fn next(&mut self) -> Option<Self::Item> {
        let tsize = 8 * std::mem::size_of::<T>();
        if self.ncur == 0 {
            self.cur = self.rest.next()?;
            self.ncur = tsize;
        }
        match self.order {
            BitOrder::Msb0 => {
                let top = tsize - 1;
                let mask = one::<T>() << top;
                let bit = mask & self.cur != num::zero();
                self.cur <<= 1;
                self.ncur -= 1;
                Some(bit)
            }
            BitOrder::Lsb0 => {
                let bit = one::<T>() & self.cur != zero();
                self.cur >>= 1;
                self.ncur -= 1;
                Some(bit)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn to_bits<T: PrimInt>(v: &[T], order: BitOrder) -> Vec<bool> {
        let tsize = 8 * std::mem::size_of::<T>();
        let mut result = Vec::new();
        let iter: Vec<usize> = match order {
            BitOrder::Lsb0 => (0..tsize).collect(),
            BitOrder::Msb0 => (0..tsize).rev().collect(),
        };
        for val in v {
            for i in &iter {
                result.push((one::<T>() << *i) & *val != zero::<T>());
            }
        }
        result
    }

    fn test_one<T>(v: Vec<T>, order: BitOrder)
    where T: PrimInt + std::ops::ShlAssign<usize> + std::ops::ShrAssign<usize> {
        let bits = to_bits(&v, order);
        for (b0, b1) in BitIter::new(v.into_iter(), order).zip(bits.into_iter()) {
            assert_eq!(b0, b1);
        }
    }

    #[test]
    fn test_bititer() {
        let v: Vec<u8> = Vec::new();
        test_one(v, BitOrder::Msb0);

        let r_msb = [false, false, false, true, false, false, true, false];
        let r_lsb = [false, true, false, false, true, false, false, false];
        let l_msb: Vec<bool> = BitIter::new(
            vec![0x12_u8].into_iter(),
            BitOrder::Msb0,
        ).collect();
        let l_lsb: Vec<bool> = BitIter::new(
            vec![0x12_u8].into_iter(),
            BitOrder::Lsb0,
        ).collect();
        assert_eq!(l_msb, r_msb);
        assert_eq!(l_lsb, r_lsb);

        test_one(vec![0x12_u8, 0x34], BitOrder::Msb0);
        test_one(vec![0x12_u8, 0x34], BitOrder::Lsb0);
        test_one(vec![0x1234_u16, 0x5678], BitOrder::Msb0);
        test_one(vec![0x1234_u16, 0x5678], BitOrder::Lsb0);
        test_one(vec![-0x1234_i16, -0x5678], BitOrder::Msb0);
        test_one(vec![-0x1234_i16, -0x5678], BitOrder::Lsb0);
    }
}
