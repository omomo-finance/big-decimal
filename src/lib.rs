use borsh::{BorshDeserialize, BorshSerialize};
use near_sdk::borsh::maybestd::io::Write;

use near_sdk::json_types::U128;
use near_sdk::serde::{Deserialize, Serialize, Serializer};
use num_traits::cast::ToPrimitive;
use std::cmp::{max_by, min_by, Ordering};
use std::fmt::{Display, Formatter};
use std::ops::{Add, Div, Mul, Sub};
use std::str::FromStr;

uint::construct_uint!(
    pub struct U384(6);
);

///  Precision for num value in calculations
pub const NUM_DECIMALS: u32 = 24;
/// Precision with which we return the value in f64
pub const ACCURACY: u128 = 10000u128;

/// List internal errors
const PARSE_INT_ERROR: &str = "Parse int error";

/// BigDecimal struct for work with large numbers,
/// self.0 value,
/// self.1 num_decimal
/// # Examples
/// BigDecimal(2,10) = 2 * 10_u128.pow(10)
#[derive(Copy, Clone)]
pub struct BigDecimal(U384, u32);

impl Default for BigDecimal {
    fn default() -> Self {
        BigDecimal::zero()
    }
}

impl BigDecimal {
    /// # Examples
    ///
    /// Basic usage:
    /// let num: u128 = 33
    /// let res: BigDecimal = BigDecimal::from_ratio(num).round_u128();
    /// res = 33
    pub fn round_u128(&self) -> u128 {
        let a = self.0 / U384::from(10_u128.pow(self.1));
        ((a * U384::from(10_u128.pow(self.1))) / U384::from(10u128.pow(self.1))).as_u128()
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let num: u128 = 33
    /// let res: BigDecimal = BigDecimal::from_ratio(num).f64();
    /// res = 33.0
    #[cfg(not(target_arch = "wasm32-unknown-unknown"))]
    pub fn f64(&self) -> f64 {
        let base = self.0.as_u128() / 10_u128.pow(NUM_DECIMALS);
        let dec =
            (self.0 * U384::from(ACCURACY) - U384::from(self.0.as_u128() * ACCURACY)).as_u128();
        let mut dec_f64: f64 = 0.0;
        if dec > 0 {
            dec_f64 = dec.to_f64().unwrap() / (ACCURACY * 10_u128.pow(NUM_DECIMALS)) as f64;
        }
        base.to_f64().unwrap() + dec_f64
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let num: u128 = 66
    /// let res: BigDecimal = BigDecimal::from(num).round_mul_u128(2);
    /// res = 132
    pub fn round_mul_u128(&self, rhs: u128) -> u128 {
        let a = self.0 / U384::from(10_u128.pow(self.1));
        ((a * U384::from(rhs) * U384::from(10u128.pow(self.1))) / U384::from(10u128.pow(self.1)))
            .as_u128()
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let num: u128 = 66
    /// let res: BigDecimal = BigDecimal::from(num).round_mul_u128(2);
    /// res = 132
    pub fn div_u128(&self, rhs: u128) -> BigDecimal {
        Self(self.0 / U384::from(rhs), self.1)
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let zero = BigDecimal::zero()
    pub fn zero() -> Self {
        Self(U384::zero(), NUM_DECIMALS)
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let one: BigDecimal = BigDecimal::one()
    /// one = 10u128.pow(24)
    pub fn one() -> Self {
        Self(U384::from(10_u128.pow(NUM_DECIMALS)), NUM_DECIMALS)
    }

    /// # Examples
    ///
    /// Basic usage:
    /// let num: u128 = 45
    /// let bd: BigDecimal = BigDecimal::from(num).pow(2)
    /// bd = 2025
    pub fn pow(&self, mut exponent: u64) -> Self {
        let mut x = self.0 / U384::from(10_u128.pow(self.1));
        while exponent != 0 {
            exponent >>= 1;
            if exponent != 0 {
                x = x * x;
            }
        }
        Self(x * U384::from(10_u128.pow(self.1)), self.1)
    }
}

impl Display for BigDecimal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let a = self.0 / U384::from(10_u128.pow(self.1));
        let b = (self.0 - a * U384::from(10_u128.pow(self.1))).as_u128();
        if b > 0 {
            write!(f, "{}", format!("{}.{:024}", a, b).trim_end_matches('0'))
        } else {
            write!(f, "{}", a)
        }
    }
}

#[cfg(not(target_arch = "wasm32-unknown-unknown"))]
impl std::fmt::Debug for BigDecimal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl PartialEq<Self> for BigDecimal {
    fn eq(&self, other: &Self) -> bool {
        self.0 .0 == other.0 .0
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from_str("1000")
/// num = 1000
#[cfg(not(target_arch = "wasm32-unknown-unknown"))]
impl FromStr for BigDecimal {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let dot_pos = s.find('.');
        let (int, dec) = if let Some(dot_pos) = dot_pos {
            (
                &s[..dot_pos],
                format!("{:0<24}", &s[dot_pos + 1..])
                    .parse()
                    .map_err(|_| PARSE_INT_ERROR)?,
            )
        } else {
            (s, 0u128)
        };
        let int = U384::from(int.parse::<u128>().unwrap());
        if dec >= 10_u128.pow(24) {
            return Err(String::from("The decimal part is too large"));
        }
        Ok(Self(
            int * U384::from(10_u128.pow(24)) + U384::from(dec),
            NUM_DECIMALS,
        ))
    }
}

impl Serialize for BigDecimal {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> Deserialize<'de> for BigDecimal {
    fn deserialize<D>(
        deserializer: D,
    ) -> Result<Self, <D as near_sdk::serde::Deserializer<'de>>::Error>
    where
        D: near_sdk::serde::Deserializer<'de>,
    {
        let s: String = Deserialize::deserialize(deserializer)?;
        Self::from_str(&s).map_err(near_sdk::serde::de::Error::custom)
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(1000_u128)
/// num = 1000
impl From<u128> for BigDecimal {
    fn from(a: u128) -> Self {
        Self(U384::from(a) * U384::from(10_u128.pow(24)), NUM_DECIMALS)
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(1000_u64)
/// num = 1000
impl From<u64> for BigDecimal {
    fn from(a: u64) -> Self {
        Self(U384::from(a) * U384::from(10_u128.pow(24)), NUM_DECIMALS)
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(1000_u32)
/// num = 1000
impl From<u32> for BigDecimal {
    fn from(a: u32) -> Self {
        Self(U384::from(a) * U384::from(10_u128.pow(24)), NUM_DECIMALS)
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(1000_i32)
/// num = 1000
impl From<i32> for BigDecimal {
    fn from(a: i32) -> Self {
        Self(U384::from(a) * U384::from(10_u128.pow(24)), NUM_DECIMALS)
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(U128(1000))
/// num = 1000_U128
impl From<U128> for BigDecimal {
    fn from(low_u128: U128) -> Self {
        Self(
            U384::from(low_u128.0) * U384::from(10_u128.pow(24)),
            NUM_DECIMALS,
        )
    }
}

/// # Examples
///
/// Basic usage:
/// let num: BigDecimal = BigDecimal::from(U128(1000))
/// let res: U128 = U128::from(num)
/// res = 1000_U128
impl From<BigDecimal> for U128 {
    fn from(bd: BigDecimal) -> Self {
        Self(bd.0.low_u128() / 10_u128.pow(bd.1))
    }
}

impl Add for BigDecimal {
    type Output = Self;

    fn add(self, rhs: BigDecimal) -> Self::Output {
        Self(self.0 + rhs.0, NUM_DECIMALS)
    }
}

impl Sub for BigDecimal {
    type Output = Self;

    fn sub(self, rhs: BigDecimal) -> Self::Output {
        Self(self.0 - rhs.0, NUM_DECIMALS)
    }
}

impl Mul for BigDecimal {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(
            self.0 * rhs.0 + U384::from(10_u128.pow(self.1) / 2) / U384::from(10_u128.pow(self.1)),
            NUM_DECIMALS,
        )
    }
}

impl Div for BigDecimal {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Self(
            self.0 * U384::from(10_u128.pow(self.1)) + U384::from(10_u128.pow(self.1) / 2) / rhs.0,
            NUM_DECIMALS,
        )
    }
}

impl PartialOrd for BigDecimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Eq for BigDecimal {}

impl Ord for BigDecimal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }

    fn max(self, other: Self) -> Self
    where
        Self: Sized,
    {
        max_by(self, other, Ord::cmp)
    }

    fn min(self, other: Self) -> Self
    where
        Self: Sized,
    {
        min_by(self, other, Ord::cmp)
    }

    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Sized,
    {
        assert!(min <= max);
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
    }
}

impl BorshSerialize for BigDecimal {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        BorshSerialize::serialize(&self.0 .0, writer)
    }
}

impl BorshDeserialize for BigDecimal {
    fn deserialize(buf: &mut &[u8]) -> std::io::Result<Self> {
        Ok(Self(
            U384(BorshDeserialize::deserialize(buf)?),
            NUM_DECIMALS,
        ))
    }
}

#[cfg(test)]
mod test {
    use crate::BigDecimal;
    use near_sdk::json_types::U128;
    use std::str::FromStr;

    fn get_expect_value() -> u128 {
        33_u128
    }

    #[test]
    fn to_u128_test() {
        let value = 33;
        let bd: BigDecimal = BigDecimal::from(value);
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn to_f64_test() {
        let value = 33;
        let bd: BigDecimal = BigDecimal::from(value);
        assert_eq!(bd.f64(), get_expect_value() as f64);
    }

    #[test]
    fn round_mul_u128_test() {
        let value = 17;
        let res = BigDecimal::from(value).round_mul_u128(value);
        assert_eq!(res, BigDecimal::from(value).pow(2).round_u128());
    }

    #[test]
    fn div_u128_test() {
        let value = 66;
        let res = BigDecimal::from(value).div_u128(2);
        assert_eq!(res.round_u128(), get_expect_value());
    }

    #[test]
    fn zero_test() {
        let zero: BigDecimal = BigDecimal::zero();
        assert_eq!(zero, BigDecimal::from(0));
    }

    #[test]
    fn one_test() {
        assert_eq!(format!("{}", BigDecimal::one()), 1.to_string());
        assert_eq!(BigDecimal::one().round_u128(), 1);
    }

    #[test]
    fn pow_test() {
        let value = 22_u128;
        let bd: BigDecimal = BigDecimal::from(value).pow(2);
        assert_eq!(bd.round_u128(), 484);
    }

    #[test]
    fn display_test() {
        let value = 33;
        let bd: BigDecimal = BigDecimal::from(value);
        assert_eq!(format!("{}", bd), format!("{}", get_expect_value()));
    }

    #[test]
    fn debug_test() {
        let value = 33;
        let bd: BigDecimal = BigDecimal::from(value);
        assert_eq!(format!("{:?}", bd), format!("{}", get_expect_value()));
    }

    #[test]
    fn from_str_test() {
        let value = "33";
        let bd = BigDecimal::from_str(value).unwrap();
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn from_u128_test() {
        let value: u128 = 33;
        let bd = BigDecimal::from(value);
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn from_u64_test() {
        let value: u64 = 33;
        let bd = BigDecimal::from(value);
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn from_u32_test() {
        let value: u32 = 33;
        let bd = BigDecimal::from(value);
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn from_i32_test() {
        let value: i32 = 33;
        let bd = BigDecimal::from(value);
        assert_eq!(bd.round_u128(), get_expect_value());
    }

    #[test]
    fn from_U128_test() {
        let value = U128(33);
        let res = BigDecimal::from(value);
        assert_eq!(res, BigDecimal::from(get_expect_value()));
        assert_eq!(res.round_u128(), get_expect_value());
    }

    #[test]
    fn to_U128_test() {
        let value = 33;
        let res = BigDecimal::from(value);
        assert_eq!(U128::from(res), U128(get_expect_value()));
    }
}
