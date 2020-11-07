//! Manipulations and data types that represent polynomial.

#![warn(bad_style)]
#![warn(missing_docs)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused)]
#![warn(unused_extern_crates)]
#![warn(unused_import_braces)]
#![warn(unused_qualifications)]
#![warn(unused_results)]

extern crate num_traits;
extern crate alga;

use num_traits::{One, Zero, PrimInt};
use std::ops::{Add, Mul, Div, Neg, Sub, AddAssign, SubAssign, MulAssign, DivAssign};
use std::{cmp, fmt};
use alga::general::*;

/// Polynomial expression
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Polynomial<T> {
    data: Vec<T>,
}

// New implementations from fork: Implement alga traits

impl<T: Ring> Identity<Additive> for Polynomial<T> {
    fn identity() -> Self {
        <Self as One>::one()
    }
}
impl<T: Ring> AbstractMagma<Additive> for Polynomial<T> {
    fn operate(&self, right: &Self) -> Self {
        self + right
    }
}
impl<T: Ring> AbstractSemigroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractMonoid<Additive> for Polynomial<T> {}
impl<T: Ring> TwoSidedInverse<Additive> for Polynomial<T> {
    fn two_sided_inverse(&self) -> Self {
        -self
    }
}
impl<T: Ring> AbstractQuasigroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractLoop<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractGroup<Additive> for Polynomial<T> {}
impl<T: Ring> AbstractGroupAbelian<Additive> for Polynomial<T> {}
impl<T: Ring> Identity<Multiplicative> for Polynomial<T> {
    fn identity() -> Self {
        <Self as Zero>::zero()
    }
}
impl<T: Ring> AbstractMagma<Multiplicative> for Polynomial<T> {
    fn operate(&self, right: &Self) -> Self {
        self * right
    }
}
impl<T: Ring> AbstractSemigroup<Multiplicative> for Polynomial<T> {}
impl<T: Ring> AbstractMonoid<Multiplicative> for Polynomial<T> {}
impl<T: Ring> AbstractRing<Additive, Multiplicative> for Polynomial<T> {}
// impl<T: Ring> Ring for Polynomial<T> {} // (implicit)

impl<T: Zero> Polynomial<T> {
    /// Creates new `Polynomial`.
    ///
    /// ```rust
    /// use polynomial::Polynomial;
    /// let poly = Polynomial::new(vec![1, 2, 3]);
    /// assert_eq!("1+2*x+3*x^2", poly.pretty("x"));
    /// ```
    #[inline]
    pub fn new(mut data: Vec<T>) -> Polynomial<T> {
        while let Some(true) = data.last().map(|x| x.is_zero()) {
            let _ = data.pop();
        }
        Polynomial { data }
    }
}

impl<T: Zero + One + Clone> Polynomial<T> {
    /// Evaluates the polynomial value.
    ///
    /// ```rust
    /// use polynomial::Polynomial;
    /// let poly = Polynomial::new(vec![1, 2, 3]);
    /// assert_eq!(1, poly.eval(0));
    /// assert_eq!(6, poly.eval(1));
    /// assert_eq!(17, poly.eval(2));
    /// ```
    #[inline]
    pub fn eval(&self, x: T) -> T {
        let mut sum: T = Zero::zero();
        let mut x_n: T = One::one();
        for n in self.data.iter() {
            sum = sum + n.clone() * x_n.clone();
            x_n = x_n * x.clone();
        }
        sum
    }
}

impl<T> Polynomial<T> {
    /// Gets the slice of internal data.
    #[inline]
    pub fn data(&self) -> &[T] {
        &self.data
    }

    /// Gets the degree of the polynomial.
    #[inline]
    pub fn degree(&self) -> usize {
        if self.data.len() == 0 {
            0
        } else {
            self.data.len() - 1
        }
    }
    
    /// Multiply the polynomial by a constant
    pub fn mul_constant<V: Mul<T> + Clone>(self, constant: V) -> Polynomial<<V as Mul<T>>::Output> {
        Polynomial {
            data: self.data.into_iter()
                .map(|val| constant.clone() * val)
                .collect()
        }
    }

    /// Divide the polynomial by a constant
    pub fn div_constant<V: Clone>(self, constant: V) -> Polynomial<<T as Div<V>>::Output> 
    where T: Div<V> {
        Polynomial {
            data: self.data.into_iter()
                .map(|val| val / constant.clone())
                .collect()
        }
    }

    /// Add a constant to the polynomial
    pub fn add_constant<V>(mut self, constant: V) -> Polynomial<T>
    where T: AddAssign<V> {
        let l = self.data.len();
        self.data[l - 1] += constant;
        self
    }
}

impl<T: Clone> Polynomial<T> {
    /// Add a constant to a reference to the polynomial
    pub fn add_constant_ref<V>(&self, constant: V) -> Polynomial<T> 
    where T: AddAssign<V> {
        let mut data = self.data.clone();
        data[self.data.len() - 1] += constant;
        Polynomial { data }
    }
    
    /// Multiply a reference to the polynomial by a constant
    pub fn mul_constant_ref<V: Mul<T> + Clone>(&self, constant: V) -> Polynomial<<V as Mul<T>>::Output> {
        Polynomial {
            data: self.data.iter()
                .cloned()
                .map(|val| constant.clone() * val)
                .collect()
        }
    }

    /// Divide a reference to the polynomial by a constant
    pub fn div_constant_ref<V: Clone>(&self, constant: V) -> Polynomial<<T as Div<V>>::Output>
    where T: Div<V>
    {
        Polynomial {
            data: self.data.iter()
                .cloned()
                .map(|val| val / constant.clone())
                .collect()
        }
    }
}

impl<T: Clone + Zero + Eq> Polynomial<T> {
    /// Get the leading coefficient of the polynomial.
    pub fn lc(&self) -> T {
        self.data.iter()
            .find(|&val| *val != Zero::zero())
            .cloned()
            .unwrap_or(Zero::zero())
    }
}

impl<T: Clone + EuclideanDomain + Zero> Polynomial<T> {
    /// Get the content (gcd of coefficients) of the polynomial.
    pub fn cont(&self) -> T {
        if self.data.len() == 0 {
            return Zero::zero();
        }
        if self.data.len() == 1 {
            return self.data[0].clone();
        }
        let mut result = self.data[0].clone();
        for i in 1..self.data.len() {
            result = gcd(result, self.data[i].clone());
        }
        result
    }
}

impl<T> Polynomial<T>
where
    T: Zero + One + Eq + Neg<Output = T> + Ord + fmt::Display + Clone,
{
    /// Pretty prints the polynomial.
    pub fn pretty(&self, x: &str) -> String {
        if self.is_zero() {
            return "0".to_string();
        }

        let one = One::one();
        let mut s = Vec::new();
        for (i, n) in self.data.iter().enumerate() {
            // output n*x^i / -n*x^i
            if n.is_zero() {
                continue;
            }

            let term = if i.is_zero() {
                n.to_string()
            } else if i == 1 {
                if (*n) == one {
                    x.to_string()
                } else if (*n) == -one.clone() {
                    format!("-{}", x)
                } else {
                    format!("{}*{}", n.to_string(), x)
                }
            } else {
                if (*n) == one {
                    format!("{}^{}", x, i)
                } else if (*n) == -one.clone() {
                    format!("-{}^{}", x, i)
                } else {
                    format!("{}*{}^{}", n.to_string(), x, i)
                }
            };

            if s.len() > 0 && (*n) > Zero::zero() {
                s.push("+".to_string());
            }
            s.push(term);
        }

        s.concat()
    }
}

impl<'a, T> Neg for Polynomial<T>
where
    T: Neg + Zero + Clone,
    <T as Neg>::Output: Zero,
{
    type Output = Polynomial<<T as Neg>::Output>;

    #[inline]
    fn neg(self) -> Polynomial<<T as Neg>::Output> {
        -&self
    }
}

impl<'a, T> Neg for &'a Polynomial<T>
where
    T: Neg + Zero + Clone,
    <T as Neg>::Output: Zero,
{
    type Output = Polynomial<<T as Neg>::Output>;

    #[inline]
    fn neg(self) -> Polynomial<<T as Neg>::Output> {
        Polynomial::new(self.data.iter().map(|x| -x.clone()).collect())
    }
}

macro_rules! forward_val_val_binop {
    (impl $imp:ident, $method:ident) => {
        impl<Lhs, Rhs> $imp<Polynomial<Rhs>> for Polynomial<Lhs>
        where
            Lhs: Zero + $imp<Rhs> + Clone,
            Rhs: Zero + Clone,
            <Lhs as $imp<Rhs>>::Output: Zero,
        {
            type Output = Polynomial<<Lhs as $imp<Rhs>>::Output>;

            #[inline]
            fn $method(self, other: Polynomial<Rhs>) -> Polynomial<<Lhs as $imp<Rhs>>::Output> {
                (&self).$method(&other)
            }
        }
    };
}

macro_rules! forward_ref_val_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, Lhs, Rhs> $imp<Polynomial<Rhs>> for &'a Polynomial<Lhs>
        where
            Lhs: Zero + $imp<Rhs> + Clone,
            Rhs: Zero + Clone,
            <Lhs as $imp<Rhs>>::Output: Zero,
        {
            type Output = Polynomial<<Lhs as $imp<Rhs>>::Output>;

            #[inline]
            fn $method(self, other: Polynomial<Rhs>) -> Polynomial<<Lhs as $imp<Rhs>>::Output> {
                self.$method(&other)
            }
        }
    };
}

macro_rules! forward_val_ref_binop {
    (impl $imp:ident, $method:ident) => {
        impl<'a, Lhs, Rhs> $imp<&'a Polynomial<Rhs>> for Polynomial<Lhs>
        where
            Lhs: Zero + $imp<Rhs> + Clone,
            Rhs: Zero + Clone,
            <Lhs as $imp<Rhs>>::Output: Zero,
        {
            type Output = Polynomial<<Lhs as $imp<Rhs>>::Output>;

            #[inline]
            fn $method(self, other: &Polynomial<Rhs>) -> Polynomial<<Lhs as $imp<Rhs>>::Output> {
                (&self).$method(other)
            }
        }
    };
}

macro_rules! forward_all_binop {
    (impl $imp:ident, $method:ident) => {
        forward_val_val_binop!(impl $imp, $method);
        forward_ref_val_binop!(impl $imp, $method);
        forward_val_ref_binop!(impl $imp, $method);
    };
}

forward_all_binop!(impl Add, add);

impl<'a, 'b, Lhs, Rhs> Add<&'b Polynomial<Rhs>> for &'a Polynomial<Lhs>
where
    Lhs: Zero + Add<Rhs> + Clone,
    Rhs: Zero + Clone,
    <Lhs as Add<Rhs>>::Output: Zero,
{
    type Output = Polynomial<<Lhs as Add<Rhs>>::Output>;

    fn add(self, other: &Polynomial<Rhs>) -> Polynomial<<Lhs as Add<Rhs>>::Output> {
        let max_len = cmp::max(self.data.len(), other.data.len());
        let min_len = cmp::min(self.data.len(), other.data.len());

        let mut sum = Vec::with_capacity(max_len);
        for i in 0..min_len {
            sum.push(self.data[i].clone() + other.data[i].clone());
        }

        if self.data.len() <= other.data.len() {
            for i in min_len..max_len {
                sum.push(num_traits::zero::<Lhs>() + other.data[i].clone());
            }
        } else {
            for i in min_len..max_len {
                sum.push(self.data[i].clone() + num_traits::zero::<Rhs>());
            }
        }

        Polynomial::new(sum)
    }
}

impl<T> AddAssign<Polynomial<T>> for Polynomial<T>
where
    T: Zero + Add<T, Output=T> + Clone,
    <T as Add<T>>::Output: Zero,
{
    fn add_assign(&mut self, other: Polynomial<T>) {
        *self = self.clone() + other
    }
}

forward_all_binop!(impl Sub, sub);

impl<'a, 'b, Lhs, Rhs> Sub<&'b Polynomial<Rhs>> for &'a Polynomial<Lhs>
where
    Lhs: Zero + Sub<Rhs> + Clone,
    Rhs: Zero + Clone,
    <Lhs as Sub<Rhs>>::Output: Zero,
{
    type Output = Polynomial<<Lhs as Sub<Rhs>>::Output>;

    fn sub(self, other: &Polynomial<Rhs>) -> Polynomial<<Lhs as Sub<Rhs>>::Output> {
        let min_len = cmp::min(self.data.len(), other.data.len());
        let max_len = cmp::max(self.data.len(), other.data.len());

        let mut sub = Vec::with_capacity(max_len);
        for i in 0..min_len {
            sub.push(self.data[i].clone() - other.data[i].clone());
        }
        if self.data.len() <= other.data.len() {
            for i in min_len..max_len {
                sub.push(num_traits::zero::<Lhs>() - other.data[i].clone())
            }
        } else {
            for i in min_len..max_len {
                sub.push(self.data[i].clone() - num_traits::zero::<Rhs>())
            }
        }
        Polynomial::new(sub)
    }
}

impl<T> SubAssign<Polynomial<T>> for Polynomial<T>
where
    T: Zero + Sub<T, Output=T> + Clone,
    <T as Sub<T>>::Output: Zero,
{
    fn sub_assign(&mut self, other: Polynomial<T>) {
        *self = self.clone() - other
    }
}

forward_all_binop!(impl Mul, mul);

impl<'a, 'b, Lhs, Rhs> Mul<&'b Polynomial<Rhs>> for &'a Polynomial<Lhs>
where
    Lhs: Zero + Mul<Rhs> + Clone,
    Rhs: Zero + Clone,
    <Lhs as Mul<Rhs>>::Output: Zero,
{
    type Output = Polynomial<<Lhs as Mul<Rhs>>::Output>;

    fn mul(self, other: &Polynomial<Rhs>) -> Polynomial<<Lhs as Mul<Rhs>>::Output> {
        if self.is_zero() || other.is_zero() {
            return Polynomial::new(vec![]);
        }

        let slen = self.data.len();
        let olen = other.data.len();
        let prod = (0..slen + olen - 1)
            .map(|i| {
                let mut p = num_traits::zero::<<Lhs as Mul<Rhs>>::Output>();
                let kstart = cmp::max(olen, i + 1) - olen;
                let kend = cmp::min(slen, i + 1);
                for k in kstart..kend {
                    p = p + self.data[k].clone() * other.data[i - k].clone();
                }
                p
            })
            .collect();
        Polynomial::new(prod)
    }
}

impl<T> MulAssign<Polynomial<T>> for Polynomial<T>
where
    T: Zero + Mul<T, Output=T> + Clone,
    <T as Mul<T>>::Output: Zero,
{
    fn mul_assign(&mut self, other: Polynomial<T>) {
        *self = self.clone() * other
    }
}

impl<T: Zero + Clone> Zero for Polynomial<T> {
    #[inline]
    fn zero() -> Polynomial<T> {
        Polynomial { data: vec![] }
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.data.is_empty()
    }
}

impl<T: Zero + One + Clone> One for Polynomial<T> {
    #[inline]
    fn one() -> Polynomial<T> {
        Polynomial {
            data: vec![One::one()],
        }
    }
}

/// Elements of a Euclidean Domain are elements of a ring with a division algorithm and GCD
/// EuclideanDomain can be implemented for Fields with gcd 1 to work with certain algorithms
pub trait EuclideanDomain: Ring + ClosedDiv {
    /// Returns the modulus of two elements from the division algorithm
    fn modulus(self, other: Self) -> Self;
    /// Take the gcd of two elements
    fn gcd(self, other: Self) -> Self;
    /// Take a multiplicative power of an element (using exponentiation by squaring algorithm)
    fn pow(mut self, mut power: u32) -> Self {
        // https://en.wikipedia.org/wiki/Exponentiation_by_squaring
        if power == 0 {
            return Self::one();
        }
        let mut y = Self::one();
        while power > 1 {
            if power & 1 == 0 {
                self = self.clone() * self.clone();
                power >>= 1;
            } else {
                y = self.clone() * y;
                self = self.clone() * self.clone();
                power = (power - 1) >> 1;
            }
        }
        self * y
    }
    /// Optional: Helpful when displaying and debugging
    fn is_positive(&self) -> Option<bool> {
        None
    }
    /// Optional: Helpful when displaying and debugging
    fn is_negative(&self) -> Option<bool> {
        None
    }
    
    /// Returns if an element is a unit in the Euclidean Domain
    fn is_unit(&self) -> bool {
        // Check if self has a mult. inverse in our ED
        //              vvv  gives only the quotient
        self.clone() * (Self::one() / self.clone()) == Self::one()
    }

}

impl<T: Ring + ClosedDiv + PrimInt> EuclideanDomain for T {
    fn modulus(self, other: Self) -> Self {
        self % other
    }

    fn gcd(mut self, mut b: Self) -> Self {
        if self < b {
            std::mem::swap(&mut self, &mut b);
        }
        while !b.is_zero() {
            self = self.modulus(b);
            std::mem::swap(&mut self, &mut b);
        }
        self
    }

    fn is_positive(&self) -> Option<bool> {
        Some(self > &Self::zero())
    }

    fn is_negative(&self) -> Option<bool> {
        Some(self < &Self::zero())
    }
}

/// Computes the GCD of two elements of a EuclideanDomain
pub fn gcd<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    a.gcd(b)
}

/// Computes the LCM of two elements of a EuclideanDomain
pub fn lcm<Int: EuclideanDomain>(a: Int, b: Int) -> Int {
    // quick optimization
    if a == b {
        a
    } else {
        a.clone() * b.clone() / gcd(a, b)
    }
}

// From fork: Pseudo division algorithm

/// Compute the pseudo-division of two polynomials. Algorithm 3.1.2 from the book.
pub fn pseudo_div<T: EuclideanDomain + Eq + Clone>(a_poly: Polynomial<T>, b_poly: Polynomial<T>) -> (Polynomial<T>, Polynomial<T>)
{
    // TODO: Fix this
    assert!(a_poly.degree() >= b_poly.degree());

    if b_poly.degree() == 0 {
        return (a_poly, Polynomial::zero());
    }
    let mut q = Polynomial::zero();
    let mut e = a_poly.degree() - b_poly.degree() + 1;
    let mut r = a_poly;

    let d = b_poly.lc();

    while r.degree() >= b_poly.degree() {
        let x_degr_minus_degd = {
            let deg = r.degree() - b_poly.degree();
            let mut v = vec![T::zero(); deg];
            let mut x = vec![T::one()];
            x.append(&mut v);
            Polynomial {data: x}
        };
        let s = x_degr_minus_degd.mul_constant(r.lc());
        q = q.mul_constant(d.clone()) + s.clone();
        r = r.mul_constant(d.clone()) - b_poly.clone() * s.clone();
        if e != 0 {
            e = e - 1;
        }
    }

    (q.mul_constant(d.clone().pow(e as u32)), r.mul_constant(d.clone().pow(e as u32)))
}

/// Compute the gcd and bezout coefficients
pub fn extended_gcd<T: EuclideanDomain + Eq + Clone>(a_poly: Polynomial<T>, b_poly: Polynomial<T>) -> (Polynomial<T>, Polynomial<T>, Polynomial<T>) {
    // TODO: Fix this
    assert!(a_poly.degree() >= b_poly.degree());

    let mut r_prev = a_poly;
    let mut r = b_poly;
    let mut s_prev = Polynomial { data: vec![One::one()] };
    let mut s = Polynomial { data: vec![Zero::zero()] };
    let mut t_prev = Polynomial { data: vec![Zero::zero()] };
    let mut t = Polynomial { data: vec![One::one()] };

    while r.degree() != 0 {
        let (q, _) = pseudo_div(r_prev.clone(), r.clone());
        let d = r.lc();
        let e = r_prev.degree() - r.degree() + 1;
        let new_r = r_prev.mul_constant_ref(d.clone().pow(e as u32)) - q.clone() * r.clone();
        let new_s = s_prev.mul_constant_ref(d.clone().pow(e as u32)) - q.clone() * s.clone();
        let new_t = t_prev.mul_constant_ref(d.clone().pow(e as u32)) - q.clone() * t.clone();
        r_prev = r.clone();
        r = new_r;
        s_prev = s.clone();
        s = new_s;
        t_prev = t.clone();
        t = new_t;
    }
    
    // (u, v, gcd)
    (s, t, r)
}

/// Compute the resultant of two polynomials
pub fn resultant<T: EuclideanDomain + Eq + Clone>(a_poly: Polynomial<T>, b_poly: Polynomial<T>) -> T {
    // TODO: Fix this
    assert!(a_poly.degree() >= b_poly.degree());

    let a = a_poly.cont();
    let b = b_poly.cont();
    let mut a_poly = a_poly.div_constant(a.clone());
    let mut b_poly = b_poly.div_constant(b.clone());
    let mut g = T::one();
    let mut h = T::one();
    let mut s = T::one();
    let t = a.pow(b_poly.degree() as u32) * b.pow(a_poly.degree() as u32);
    if a_poly.degree() % 2 == 1 && b_poly.degree() % 2 == 1 {
        s = -s;
    }
    loop {
        let delta = a_poly.degree() - b_poly.degree();
        let (_q, r) = pseudo_div(a_poly.clone(), b_poly.clone());
        a_poly = b_poly;
        b_poly = r.div_constant(g.clone() * h.clone().pow(delta as u32));
        g = a_poly.lc();
        h = h.clone().pow(1 - delta as u32) * g.clone().pow(delta as u32);
        if b_poly.degree() == 0 {
            h = h.clone().pow(1 - a_poly.degree() as u32) * b_poly.lc().pow(a_poly.degree() as u32);
            return s * t * h;
        }
    }
}

impl<T> Div<Polynomial<T>> for Polynomial<T>
where
    T: EuclideanDomain + Clone + Eq
{
    type Output = Polynomial<T>;

    fn div(self, other: Polynomial<T>) -> Polynomial<T> {
        pseudo_div(self.clone(), other.clone()).0
    }
}

impl<'a, 'b, T> Div<&'b Polynomial<T>> for &'a Polynomial<T>
where
    T: EuclideanDomain + Clone + Eq
{
    type Output = Polynomial<T>;

    fn div(self, other: &Polynomial<T>) -> Polynomial<T> {
        pseudo_div(self.clone(), other.clone()).0
    }
}

impl<T> DivAssign<Polynomial<T>> for Polynomial<T>
where
    T: EuclideanDomain + Clone + Eq
{
    fn div_assign(&mut self, other: Polynomial<T>) {
        *self = self.clone() / other;
    }
}

impl<T> EuclideanDomain for Polynomial<T>
where
    T: EuclideanDomain + Clone + Eq
{
    fn modulus(self, other: Self) -> Self {
        pseudo_div(self, other).1
    }

    fn gcd(self, other: Self) -> Self {
        extended_gcd(self, other).2
    }
}

#[cfg(test)]
mod tests {
    use super::Polynomial;

    #[test]
    fn new() {
        fn check(dst: Vec<i32>, src: Vec<i32>) {
            assert_eq!(dst, Polynomial::new(src).data);
        }
        check(vec![1, 2, 3], vec![1, 2, 3]);
        check(vec![1, 2, 3], vec![1, 2, 3, 0, 0]);
        check(vec![], vec![0, 0, 0]);
    }

    #[test]
    fn neg_add_sub() {
        fn check(a: &[i32], b: &[i32], c: &[i32]) {
            fn check_eq(a: &Polynomial<i32>, b: &Polynomial<i32>) {
                assert_eq!(*a, *b);
                assert_eq!(-a, -b);
            }
            fn check_add(sum: &Polynomial<i32>, a: &Polynomial<i32>, b: &Polynomial<i32>) {
                check_eq(sum, &(a + b));
                check_eq(sum, &(b + a));
            }
            fn check_sub(sum: &Polynomial<i32>, a: &Polynomial<i32>, b: &Polynomial<i32>) {
                check_eq(a, &(sum - b));
                check_eq(b, &(sum - a));
            }

            let a = &Polynomial::new(a.to_vec());
            let b = &Polynomial::new(b.to_vec());
            let c = &Polynomial::new(c.to_vec());
            check_add(c, a, b);
            check_add(&(-c), &(-a), &(-b));
            check_sub(c, a, b);
            check_sub(&(-c), &(-a), &(-b));
        }
        check(&[], &[], &[]);
        check(&[], &[1], &[1]);
        check(&[1], &[1], &[2]);
        check(&[1, 0, 1], &[1], &[2, 0, 1]);
        check(&[1, 0, -1], &[-1, 0, 1], &[]);
    }

    #[test]
    fn mul() {
        fn check(a: &[i32], b: &[i32], c: &[i32]) {
            let a = Polynomial::new(a.to_vec());
            let b = Polynomial::new(b.to_vec());
            let c = Polynomial::new(c.to_vec());
            assert_eq!(c, &a * &b);
            assert_eq!(c, &b * &a);
        }
        check(&[], &[], &[]);
        check(&[0, 0], &[], &[]);
        check(&[0, 0], &[1], &[]);
        check(&[1, 0], &[1], &[1]);
        check(&[1, 0, 1], &[1], &[1, 0, 1]);
        check(&[1, 1], &[1, 1], &[1, 2, 1]);
        check(&[1, 1], &[1, 0, 1], &[1, 1, 1, 1]);
        check(&[0, 0, 1], &[0, 0, 1], &[0, 0, 0, 0, 1]);
    }

    #[test]
    fn eval() {
        fn check<F: Fn(i32) -> i32>(pol: &[i32], f: F) {
            for n in -10..10 {
                assert_eq!(f(n), Polynomial::new(pol.to_vec()).eval(n));
            }
        }
        check(&[], |_x| 0);
        check(&[1], |_x| 1);
        check(&[1, 1], |x| x + 1);
        check(&[0, 1], |x| x);
        check(&[10, -10, 10], |x| 10 * x * x - 10 * x + 10);
    }

    #[test]
    fn pretty() {
        fn check(slice: &[i32], s: &str) {
            assert_eq!(s.to_string(), Polynomial::new(slice.to_vec()).pretty("x"));
        }
        check(&[0], "0");
        check(&[1], "1");
        check(&[1, 1], "1+x");
        check(&[1, 1, 1], "1+x+x^2");
        check(&[2, 2, 2], "2+2*x+2*x^2");
        check(&[0, 0, 0, 1], "x^3");
        check(&[0, 0, 0, -1], "-x^3");
        check(&[-1, 0, 0, -1], "-1-x^3");
        check(&[-1, 1, 0, -1], "-1+x-x^3");
        check(&[-1, 1, -1, -1], "-1+x-x^2-x^3");
    }
}
