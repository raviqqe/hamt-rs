use std::mem::size_of;

const NUM_BITS: usize = size_of::<u32>() * 8;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bitmap(u32);

impl Bitmap {
    pub fn new() -> Self {
        Bitmap(0)
    }

    pub fn get(&self, i: u8) -> bool {
        self.0 & (1 << i) != 0
    }

    pub fn set(&self, i: u8) -> Self {
        Bitmap(self.0 | (1 << i))
    }

    pub fn unset(&self, i: u8) -> Self {
        Bitmap(self.0 & !(1 << i))
    }

    pub fn size(&self) -> u8 {
        let mut b = self.0;
        let mut s: u8 = 0;

        for _ in 0..NUM_BITS {
            s += (b & 1) as u8;
            b = b >> 1;
        }

        s
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        Bitmap::new();
    }

    #[test]
    fn get() {
        let b = Bitmap::new();

        assert_eq!(b.get(0), false);
        assert_eq!(b.get(1), false);
        assert_eq!(b.get(2), false);
        assert_eq!(b.get(31), false);
        assert_eq!(b.set(0).get(0), true);
        assert_eq!(b.set(1).get(0), false);
        assert_eq!(b.set(1).get(1), true);
        assert_eq!(b.set(2).get(2), true);
    }

    #[test]
    fn set() {
        let b = Bitmap::new();

        assert_eq!(b.set(0), Bitmap(1));
        assert_eq!(b.set(1), Bitmap(2));
        assert_eq!(b.set(2), Bitmap(4));
    }

    #[test]
    fn unset() {
        let b = Bitmap::new();

        assert_eq!(b.set(0).unset(0), Bitmap(0));
        assert_eq!(b.set(1).unset(1), Bitmap(0));
        assert_eq!(b.set(0).set(1).unset(0), Bitmap(2));
        assert_eq!(b.set(0).set(1).unset(1), Bitmap(1));
    }

    #[test]
    fn size() {
        let b = Bitmap::new();

        assert_eq!(b.size(), 0);
        assert_eq!(b.set(0).size(), 1);
        assert_eq!(b.set(1).size(), 1);
        assert_eq!(b.set(0).set(1).size(), 2);
        assert_eq!(b.set(31).size(), 1);
    }
}
