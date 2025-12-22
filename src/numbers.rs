//! The point of this module is to define a generic number type so that we can try out different number types without refactoring. I'm most interested in arbitrary size integers so that we can represent arbitrarily large orders (megaminx) but that would come with a performance penalty since we lose the Copy implementation.
use std::{
    cmp::Ordering,
    fmt::{Debug, Display},
    iter::{Product, Sum},
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
    str::FromStr,
};

use bnum::{
    cast::As,
    types::{I512, U512},
};

/// Signed
pub struct I;
/// Unsigned
pub struct U;

/// A signed or unsigned integer
///
/// This is an opaque big integer type, intended to represent orders of puzzles and values of registers since those can get huge.
///
/// This is currently implemented as a 512 bit integer.
pub struct Int<Signed> {
    value: I512,
    phantom: PhantomData<Signed>,
}

impl<Signed> Int<Signed> {
    /// Returns `true` if the value is zero and `false` otherwise
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.value == I512::ZERO
    }

    #[must_use]
    pub fn zero() -> Int<Signed> {
        Int {
            value: I512::ZERO,
            phantom: PhantomData,
        }
    }

    #[must_use]
    pub fn one() -> Int<Signed> {
        Int {
            value: I512::ONE,
            phantom: PhantomData,
        }
    }

    #[must_use]
    pub fn abs_diff<Signed2>(&self, other: &Int<Signed2>) -> Int<U> {
        Int {
            value: self.value.abs_diff(other.value).cast_signed(),
            phantom: PhantomData,
        }
    }

    fn from_inner(value: I512) -> Int<Signed> {
        Int {
            value,
            phantom: PhantomData,
        }
    }

    #[cfg(test)]
    #[must_use]
    pub fn to_u64(&self) -> u64 {
        use bnum::cast::As;

        self.value.as_()
    }

    #[cfg(test)]
    #[must_use]
    pub fn to_i64(&self) -> i64 {
        use bnum::cast::As;

        self.value.as_()
    }
}

impl Int<I> {
    #[must_use]
    pub fn signum(&self) -> i8 {
        self.value.signum().as_()
    }

    #[must_use]
    pub fn abs(self) -> Int<U> {
        Int {
            value: self.value.abs(),
            phantom: PhantomData,
        }
    }
}

impl<Signed> Clone for Int<Signed> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Signed> Copy for Int<Signed> {}

impl<Signed> Debug for Int<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", core::any::type_name::<Signed>(), self)
    }
}

impl<Signed> Display for Int<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.value, f)
    }
}

pub struct NumberOutOfRange<Signed> {
    value: Int<Signed>,
    number_ty: &'static str,
    min: Int<I>,
    max: Int<I>,
}

impl<Signed> Debug for NumberOutOfRange<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl<Signed> Display for NumberOutOfRange<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "The number {} is out of range for values of type {} that must be between {} and {}.",
            self.value, self.number_ty, self.min, self.max
        )
    }
}

pub struct ParseIntError<Signed> {
    err: bnum::errors::ParseIntError,
    phantom: PhantomData<Signed>,
}

fn map_err<Signed>(err: bnum::errors::ParseIntError) -> ParseIntError<Signed> {
    ParseIntError {
        err,
        phantom: PhantomData,
    }
}

impl<Signed> Debug for ParseIntError<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.err, f)
    }
}

impl<Signed> Display for ParseIntError<Signed> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.err, f)
    }
}

impl FromStr for Int<I> {
    type Err = ParseIntError<I>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_inner(s.trim().parse().map_err(map_err)?))
    }
}

impl FromStr for Int<U> {
    type Err = ParseIntError<U>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let num: U512 = s.trim().parse().map_err(map_err)?;
        let num: I512 = num.to_string().parse().map_err(map_err)?;

        Ok(Self::from_inner(num))
    }
}

impl From<Int<U>> for Int<I> {
    fn from(value: Int<U>) -> Self {
        Int::from_inner(value.value)
    }
}

macro_rules! from {
    (unsigned $ty: ty) => {
        impl<Signed> From<$ty> for Int<Signed> {
            fn from(value: $ty) -> Self {
                Int::from_inner(I512::from(value))
            }
        }
    };

    (signed $ty: ty) => {
        impl From<$ty> for Int<I> {
            fn from(value: $ty) -> Self {
                Int::from_inner(I512::from(value))
            }
        }
    };
}

from!(unsigned u64);
from!(unsigned u32);
from!(unsigned u16);
from!(unsigned u8);
from!(unsigned usize);
from!(signed i64);
from!(signed i32);
from!(signed i16);
from!(signed i8);
from!(signed isize);

macro_rules! try_from {
    ($ty: ty) => {
        impl<Signed> TryFrom<Int<Signed>> for $ty {
            type Error = NumberOutOfRange<Signed>;

            fn try_from(value: Int<Signed>) -> Result<Self, Self::Error> {
                if value < Int::<I>::from(<$ty>::MIN) || value > Int::<I>::from(<$ty>::MAX) {
                    return Err(NumberOutOfRange {
                        value,
                        number_ty: core::any::type_name::<$ty>(),
                        min: Int::from(<$ty>::MIN),
                        max: Int::from(<$ty>::MAX),
                    });
                }

                Ok(bnum::cast::As::as_(value.value))
            }
        }
    };
}

try_from!(u64);
try_from!(u32);
try_from!(u16);
try_from!(u8);
try_from!(usize);
try_from!(i64);
try_from!(i32);
try_from!(i16);
try_from!(i8);
try_from!(isize);

macro_rules! impl_signed_variants {
    ($op: ident, $name: ident, $op_assign: ident, $name_assign: ident, |$a: ident, $b: ident| signed $signed_code: expr, unsigned $unsigned_code: expr) => {
        impl<Signed> $op<Int<I>> for Int<Signed> {
            type Output = Int<I>;

            fn $name(self, rhs: Int<I>) -> Int<I> {
                let $a = self.value;
                let $b = rhs.value;
                Int::from_inner($signed_code)
            }
        }

        impl $op<Int<U>> for Int<I> {
            type Output = Int<I>;

            fn $name(self, rhs: Int<U>) -> Int<I> {
                let $a = self.value;
                let $b = rhs.value;
                Int::from_inner($signed_code)
            }
        }

        impl $op<Int<U>> for Int<U> {
            type Output = Int<U>;

            fn $name(self, rhs: Int<U>) -> Int<U> {
                let $a = self.value;
                let $b = rhs.value;
                Int::from_inner($unsigned_code)
            }
        }

        impl<Signed> $op_assign<Int<I>> for Int<Signed> {
            fn $name_assign(&mut self, rhs: Int<I>) {
                let $a = self.value;
                let $b = rhs.value;
                self.value = $signed_code;
            }
        }

        impl $op_assign<Int<U>> for Int<I> {
            fn $name_assign(&mut self, rhs: Int<U>) {
                let $a = self.value;
                let $b = rhs.value;
                self.value = $signed_code;
            }
        }

        impl $op_assign<Int<U>> for Int<U> {
            fn $name_assign(&mut self, rhs: Int<U>) {
                let $a = self.value;
                let $b = rhs.value;
                self.value = $unsigned_code;
            }
        }
    };
}

impl_signed_variants!(Add, add, AddAssign, add_assign, |a, b| signed a + b, unsigned a + b);
impl_signed_variants!(Mul, mul, MulAssign, mul_assign, |a, b| signed a * b, unsigned a * b);
impl_signed_variants!(Sub, sub, SubAssign, sub_assign, |a, b| signed a - b, unsigned {
    let v = a - b;

    assert!(v >= I512::ZERO, "Attempted to subtract with underflow!");

    v
});

// Euclidean division and remainder are more reasonable defaults for what we're doing

impl_signed_variants!(Div, div, DivAssign, div_assign, |a, b| signed a.div_euclid(b), unsigned a / b);

// Euclidean remainder always gives a nonnegative value, so always return unsigned

impl<Signed> Rem<Int<I>> for Int<Signed> {
    type Output = Int<U>;
    fn rem(self, rhs: Int<I>) -> Int<U> {
        Int::from_inner(self.value.rem_euclid(rhs.value))
    }
}
impl Rem<Int<U>> for Int<I> {
    type Output = Int<U>;
    fn rem(self, rhs: Int<U>) -> Int<U> {
        Int::from_inner(self.value.rem_euclid(rhs.value))
    }
}
impl Rem<Int<U>> for Int<U> {
    type Output = Int<U>;
    fn rem(self, rhs: Int<U>) -> Int<U> {
        Int::from_inner(self.value % rhs.value)
    }
}
impl<Signed> RemAssign<Int<I>> for Int<Signed> {
    fn rem_assign(&mut self, rhs: Int<I>) {
        self.value = self.value.rem_euclid(rhs.value);
    }
}
impl RemAssign<Int<U>> for Int<I> {
    fn rem_assign(&mut self, rhs: Int<U>) {
        self.value = self.value.rem_euclid(rhs.value);
    }
}
impl RemAssign<Int<U>> for Int<U> {
    fn rem_assign(&mut self, rhs: Int<U>) {
        self.value = self.value % rhs.value;
    }
}

impl<SignedA, SignedB> PartialEq<Int<SignedA>> for Int<SignedB> {
    fn eq(&self, other: &Int<SignedA>) -> bool {
        self.value == other.value
    }
}

impl<Signed> Eq for Int<Signed> {}

impl<Signed> core::hash::Hash for Int<Signed> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<SignedA, SignedB> PartialOrd<Int<SignedA>> for Int<SignedB> {
    fn partial_cmp(&self, other: &Int<SignedA>) -> Option<Ordering> {
        Some(self.value.cmp(&other.value))
    }
}

impl<Signed> Ord for Int<Signed> {
    fn cmp(&self, other: &Int<Signed>) -> Ordering {
        self.value.cmp(&other.value)
    }
}

impl<Signed> Neg for Int<Signed> {
    type Output = Int<I>;

    fn neg(self) -> Int<I> {
        Int {
            value: -self.value,
            phantom: PhantomData,
        }
    }
}

impl Sum for Int<U> {
    fn sum<V: Iterator<Item = Self>>(iter: V) -> Self {
        let mut accumulator = Int::<U>::zero();

        for item in iter {
            accumulator += item;
        }

        accumulator
    }
}

impl Sum for Int<I> {
    fn sum<V: Iterator<Item = Self>>(iter: V) -> Self {
        let mut accumulator = Int::<I>::zero();

        for item in iter {
            accumulator += item;
        }

        accumulator
    }
}

impl Product for Int<U> {
    fn product<V: Iterator<Item = Self>>(iter: V) -> Self {
        let mut accumulator = Int::<U>::zero();

        for item in iter {
            accumulator *= item;
        }

        accumulator
    }
}

impl Product for Int<I> {
    fn product<V: Iterator<Item = Self>>(iter: V) -> Self {
        let mut accumulator = Int::<I>::zero();

        for item in iter {
            accumulator *= item;
        }

        accumulator
    }
}

/// Calculate the GCD of two numbers
#[must_use]
pub fn gcd(mut a: Int<U>, mut b: Int<U>) -> Int<U> {
    loop {
        if b.is_zero() {
            return a;
        }

        let rem = a % b;
        a = b;
        b = rem;
    }
}

/// Calculate the LCM of two numbers
///
/// # Panics
///
/// Panics if either number is zero.
#[must_use]
pub fn lcm(a: Int<U>, b: Int<U>) -> Int<U> {
    assert!(!a.is_zero());
    assert!(!b.is_zero());

    b / gcd(a, b) * a
}

/// Calculate the LCM of a list of numbers
pub fn lcm_iter(values: impl Iterator<Item = Int<U>>) -> Int<U> {
    values.fold(Int::one(), lcm)
}

/// Calculate the GCD of two numbers as well as the coefficients of Bézout's identity
#[must_use]
pub fn extended_euclid(mut a: Int<U>, mut b: Int<U>) -> ((Int<I>, Int<I>), Int<U>) {
    let mut a_coeffs = (Int::<I>::one(), Int::<I>::zero());
    let mut b_coeffs = (Int::<I>::zero(), Int::<I>::one());

    loop {
        if b.is_zero() {
            return (a_coeffs, a);
        }

        let to_sub = a / b;
        let new_coeffs = (
            a_coeffs.0 - b_coeffs.0 * to_sub,
            a_coeffs.1 - b_coeffs.1 * to_sub,
        );
        let rem = a - b * to_sub;
        a = b;
        a_coeffs = b_coeffs;
        b = rem;
        b_coeffs = new_coeffs;
    }
}

// Implementation based on https://math.stackexchange.com/questions/1644677/what-to-do-if-the-modulus-is-not-coprime-in-the-chinese-remainder-theorem
/// Calculate the chinese remainder theorem over a list of tuples of remainders with moduli. The return value is bounded by the LCM of the moduli.
///
/// For each `(k, m) ∈ conditions`, the return value is congruent to `k mod m`.
///
/// This is a generalization of the CRT that supports moduli that aren't coprime. Because of this, a value that satifies all of the conditions is not guaranteed. If the conditions contradict each other, the function will return `None`.
///
/// If any of the conditions give `None`, the function will stop and return `None`.
pub fn chinese_remainder_theorem(
    mut conditions: impl Iterator<Item = Option<(Int<U>, Int<U>)>>,
) -> Option<Int<U>> {
    let (mut prev_remainder, mut prev_modulus) = match conditions.next() {
        Some(Some(condition)) => condition,
        Some(None) => return None,
        None => return Some(Int::<U>::zero()),
    };

    for cond in conditions {
        let (remainder, modulus) = cond?;

        let (coeffs, gcd) = extended_euclid(prev_modulus, modulus);

        let diff = if remainder > prev_remainder {
            remainder - prev_remainder
        } else {
            prev_remainder - remainder
        };

        if !(diff % gcd).is_zero() {
            return None;
        }

        let λ = diff / gcd;

        let x = if remainder > prev_remainder {
            remainder - modulus * coeffs.1 * λ
        } else {
            prev_remainder - prev_modulus * coeffs.0 * λ
        };

        let new_modulus = lcm(prev_modulus, modulus);

        prev_remainder = x % new_modulus;
        prev_modulus = new_modulus;
    }

    Some(prev_remainder)
}

#[cfg(test)]
mod tests {
    use crate::numbers::{Int, U, chinese_remainder_theorem, extended_euclid, gcd, lcm};

    #[test]
    fn lcm_and_gcd() {
        let lcm_int = |a: u64, b: u64| lcm(Int::from(a), Int::from(b)).to_u64();
        let gcd_int = |a: u64, b: u64| gcd(Int::from(a), Int::from(b)).to_u64();
        let extended_euclid_int = |a: u64, b: u64| {
            let ((x, y), z) = extended_euclid(Int::from(a), Int::from(b));
            assert_eq!(Int::<U>::from(a) * x + Int::<U>::from(b) * y, z);
            z.to_u64()
        };

        assert_eq!(gcd_int(3, 5), 1);
        assert_eq!(gcd_int(3, 6), 3);
        assert_eq!(gcd_int(4, 6), 2);

        assert_eq!(extended_euclid_int(3, 5), 1);
        assert_eq!(extended_euclid_int(3, 6), 3);
        assert_eq!(extended_euclid_int(4, 6), 2);

        assert_eq!(lcm_int(3, 5), 15);
        assert_eq!(lcm_int(3, 6), 6);
        assert_eq!(lcm_int(4, 6), 12);
    }

    fn crt_int(v: impl IntoIterator<Item = (u64, u64)>) -> Option<u64> {
        chinese_remainder_theorem(
            v.into_iter()
                .map(|(a, b)| Some((Int::from(a), Int::from(b)))),
        )
        .map(|v| v.to_u64())
    }

    #[test]
    fn crt() {
        assert_eq!(crt_int([(2, 3), (1, 2)]), Some(5));
        assert_eq!(crt_int([(3, 4), (1, 2)]), Some(3));
        assert_eq!(crt_int([(3, 4), (1, 2), (3, 5), (4, 7)]), Some(123));
        assert_eq!(crt_int([(2, 4), (1, 2)]), None);
    }
}
