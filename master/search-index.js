var N = null;var searchIndex = {};
searchIndex["num_traits"]={"doc":"Numeric traits for generic mathematics","items":[[3,"ParseFloatError","num_traits","",N,N],[12,"kind","","",0,N],[4,"FloatErrorKind","","",N,N],[13,"Empty","","",1,N],[13,"Invalid","","",1,N],[5,"clamp","","A value bounded by a minimum and a maximum",N,[[["t"],["t"],["t"]],["t"]]],[0,"identities","","",N,N],[5,"zero","num_traits::identities","Returns the additive identity, `0`.",N,[[],["t"]]],[5,"one","","Returns the multiplicative identity, `1`.",N,[[],["t"]]],[8,"Zero","","Defines an additive identity element for `Self`.",N,N],[10,"zero","","Returns the additive identity element of `Self`, `0`.",2,[[],["self"]]],[10,"is_zero","","Returns `true` if `self` is equal to the additive identity.",2,[[["self"]],["bool"]]],[8,"One","","Defines a multiplicative identity element for `Self`.",N,N],[10,"one","","Returns the multiplicative identity element of `Self`, `1`.",3,[[],["self"]]],[11,"is_one","","Returns `true` if `self` is equal to the multiplicative identity.",3,[[["self"]],["bool"]]],[0,"sign","num_traits","",N,N],[5,"abs","num_traits::sign","Computes the absolute value.",N,[[["t"]],["t"]]],[5,"abs_sub","","The positive difference of two numbers.",N,[[["t"],["t"]],["t"]]],[5,"signum","","Returns the sign of the number.",N,[[["t"]],["t"]]],[8,"Signed","","Useful functions for signed numbers (i.e. numbers that can be negative).",N,N],[10,"abs","","Computes the absolute value.",4,[[["self"]],["self"]]],[10,"abs_sub","","The positive difference of two numbers.",4,[[["self"],["self"]],["self"]]],[10,"signum","","Returns the sign of the number.",4,[[["self"]],["self"]]],[10,"is_positive","","Returns true if the number is positive and false if the number is zero or negative.",4,[[["self"]],["bool"]]],[10,"is_negative","","Returns true if the number is negative and false if the number is zero or positive.",4,[[["self"]],["bool"]]],[8,"Unsigned","","A trait for values which cannot be negative",N,N],[0,"ops","num_traits","",N,N],[0,"saturating","num_traits::ops","",N,N],[8,"Saturating","num_traits::ops::saturating","Saturating math operations",N,N],[10,"saturating_add","","Saturating addition operator. Returns a+b, saturating at the numeric bounds instead of overflowing.",5,[[["self"],["self"]],["self"]]],[10,"saturating_sub","","Saturating subtraction operator. Returns a-b, saturating at the numeric bounds instead of overflowing.",5,[[["self"],["self"]],["self"]]],[0,"checked","num_traits::ops","",N,N],[8,"CheckedAdd","num_traits::ops::checked","Performs addition that returns `None` instead of wrapping around on overflow.",N,N],[10,"checked_add","","Adds two numbers, checking for overflow. If overflow happens, `None` is returned.",6,[[["self"],["self"]],["option"]]],[8,"CheckedSub","","Performs subtraction that returns `None` instead of wrapping around on underflow.",N,N],[10,"checked_sub","","Subtracts two numbers, checking for underflow. If underflow happens, `None` is returned.",7,[[["self"],["self"]],["option"]]],[8,"CheckedMul","","Performs multiplication that returns `None` instead of wrapping around on underflow or overflow.",N,N],[10,"checked_mul","","Multiplies two numbers, checking for underflow or overflow. If underflow or overflow happens, `None` is returned.",8,[[["self"],["self"]],["option"]]],[8,"CheckedDiv","","Performs division that returns `None` instead of panicking on division by zero and instead of wrapping around on underflow and overflow.",N,N],[10,"checked_div","","Divides two numbers, checking for underflow, overflow and division by zero. If any of that happens, `None` is returned.",9,[[["self"],["self"]],["option"]]],[8,"CheckedRem","","Performs an integral remainder that returns `None` instead of panicking on division by zero and instead of wrapping around on underflow and overflow.",N,N],[10,"checked_rem","","Finds the remainder of dividing two numbers, checking for underflow, overflow and division by zero. If any of that happens, `None` is returned.",10,[[["self"],["self"]],["option"]]],[8,"CheckedNeg","","Performs negation that returns `None` if the result can't be represented.",N,N],[10,"checked_neg","","Negates a number, returning `None` for results that can't be represented, like signed `MIN` values that can't be positive, or non-zero unsigned values that can't be negative.",11,[[["self"]],["option"]]],[8,"CheckedShl","","Performs a left shift that returns `None` on overflow.",N,N],[10,"checked_shl","","Shifts a number to the left, checking for overflow. If overflow happens, `None` is returned.",12,[[["self"],["u32"]],["option"]]],[8,"CheckedShr","","Performs a right shift that returns `None` on overflow.",N,N],[10,"checked_shr","","Shifts a number to the left, checking for overflow. If overflow happens, `None` is returned.",13,[[["self"],["u32"]],["option"]]],[0,"wrapping","num_traits::ops","",N,N],[8,"WrappingAdd","num_traits::ops::wrapping","Performs addition that wraps around on overflow.",N,N],[10,"wrapping_add","","Wrapping (modular) addition. Computes `self + other`, wrapping around at the boundary of the type.",14,[[["self"],["self"]],["self"]]],[8,"WrappingSub","","Performs subtraction that wraps around on overflow.",N,N],[10,"wrapping_sub","","Wrapping (modular) subtraction. Computes `self - other`, wrapping around at the boundary of the type.",15,[[["self"],["self"]],["self"]]],[8,"WrappingMul","","Performs multiplication that wraps around on overflow.",N,N],[10,"wrapping_mul","","Wrapping (modular) multiplication. Computes `self * other`, wrapping around at the boundary of the type.",16,[[["self"],["self"]],["self"]]],[0,"inv","num_traits::ops","",N,N],[8,"Inv","num_traits::ops::inv","Unary operator for retrieving the multiplicative inverse, or reciprocal, of a value.",N,N],[16,"Output","","The result after applying the operator.",17,N],[10,"inv","","Returns the multiplicative inverse of `self`.",17,N],[0,"mul_add","num_traits::ops","",N,N],[8,"MulAdd","num_traits::ops::mul_add","Fused multiply-add. Computes `(self * a) + b` with only one rounding error, yielding a more accurate result than an unfused multiply-add.",N,N],[16,"Output","","The resulting type after applying the fused multiply-add.",18,N],[10,"mul_add","","Performs the fused multiply-add operation.",18,N],[8,"MulAddAssign","","The fused multiply-add assignment operation.",N,N],[10,"mul_add_assign","","Performs the fused multiply-add operation.",19,[[["self"],["a"],["b"]]]],[0,"bounds","num_traits","",N,N],[8,"Bounded","num_traits::bounds","Numbers which have upper and lower bounds",N,N],[10,"min_value","","returns the smallest finite number this type can represent",20,[[],["self"]]],[10,"max_value","","returns the largest finite number this type can represent",20,[[],["self"]]],[0,"float","num_traits","",N,N],[8,"FloatCore","num_traits::float","Generic trait for floating point numbers that works with `no_std`.",N,N],[10,"infinity","","Returns positive infinity.",21,[[],["self"]]],[10,"neg_infinity","","Returns negative infinity.",21,[[],["self"]]],[10,"nan","","Returns NaN.",21,[[],["self"]]],[10,"neg_zero","","Returns `-0.0`.",21,[[],["self"]]],[10,"min_value","","Returns the smallest finite value that this type can represent.",21,[[],["self"]]],[10,"min_positive_value","","Returns the smallest positive, normalized value that this type can represent.",21,[[],["self"]]],[10,"epsilon","","Returns epsilon, a small positive value.",21,[[],["self"]]],[10,"max_value","","Returns the largest finite value that this type can represent.",21,[[],["self"]]],[11,"is_nan","","Returns `true` if the number is NaN.",21,[[["self"]],["bool"]]],[11,"is_infinite","","Returns `true` if the number is infinite.",21,[[["self"]],["bool"]]],[11,"is_finite","","Returns `true` if the number is neither infinite or NaN.",21,[[["self"]],["bool"]]],[11,"is_normal","","Returns `true` if the number is neither zero, infinite, subnormal or NaN.",21,[[["self"]],["bool"]]],[10,"classify","","Returns the floating point category of the number. If only one property is going to be tested, it is generally faster to use the specific predicate instead.",21,[[["self"]],["fpcategory"]]],[11,"floor","","Returns the largest integer less than or equal to a number.",21,[[["self"]],["self"]]],[11,"ceil","","Returns the smallest integer greater than or equal to a number.",21,[[["self"]],["self"]]],[11,"round","","Returns the nearest integer to a number. Round half-way cases away from `0.0`.",21,[[["self"]],["self"]]],[11,"trunc","","Return the integer part of a number.",21,[[["self"]],["self"]]],[11,"fract","","Returns the fractional part of a number.",21,[[["self"]],["self"]]],[11,"abs","","Computes the absolute value of `self`. Returns `FloatCore::nan()` if the number is `FloatCore::nan()`.",21,[[["self"]],["self"]]],[11,"signum","","Returns a number that represents the sign of `self`.",21,[[["self"]],["self"]]],[11,"is_sign_positive","","Returns `true` if `self` is positive, including `+0.0` and `FloatCore::infinity()`, and since Rust 1.20 also `FloatCore::nan()`.",21,[[["self"]],["bool"]]],[11,"is_sign_negative","","Returns `true` if `self` is negative, including `-0.0` and `FloatCore::neg_infinity()`, and since Rust 1.20 also `-FloatCore::nan()`.",21,[[["self"]],["bool"]]],[11,"min","","Returns the minimum of the two numbers.",21,[[["self"],["self"]],["self"]]],[11,"max","","Returns the maximum of the two numbers.",21,[[["self"],["self"]],["self"]]],[11,"recip","","Returns the reciprocal (multiplicative inverse) of the number.",21,[[["self"]],["self"]]],[11,"powi","","Raise a number to an integer power.",21,[[["self"],["i32"]],["self"]]],[10,"to_degrees","","Converts to degrees, assuming the number is in radians.",21,[[["self"]],["self"]]],[10,"to_radians","","Converts to radians, assuming the number is in degrees.",21,[[["self"]],["self"]]],[10,"integer_decode","","Returns the mantissa, base 2 exponent, and sign as integers, respectively. The original number can be recovered by `sign * mantissa * 2 ^ exponent`.",21,N],[8,"Float","","Generic trait for floating point numbers",N,N],[10,"nan","","Returns the `NaN` value.",22,[[],["self"]]],[10,"infinity","","Returns the infinite value.",22,[[],["self"]]],[10,"neg_infinity","","Returns the negative infinite value.",22,[[],["self"]]],[10,"neg_zero","","Returns `-0.0`.",22,[[],["self"]]],[10,"min_value","","Returns the smallest finite value that this type can represent.",22,[[],["self"]]],[10,"min_positive_value","","Returns the smallest positive, normalized value that this type can represent.",22,[[],["self"]]],[11,"epsilon","","Returns epsilon, a small positive value.",22,[[],["self"]]],[10,"max_value","","Returns the largest finite value that this type can represent.",22,[[],["self"]]],[10,"is_nan","","Returns `true` if this value is `NaN` and false otherwise.",22,[[["self"]],["bool"]]],[10,"is_infinite","","Returns `true` if this value is positive infinity or negative infinity and false otherwise.",22,[[["self"]],["bool"]]],[10,"is_finite","","Returns `true` if this number is neither infinite nor `NaN`.",22,[[["self"]],["bool"]]],[10,"is_normal","","Returns `true` if the number is neither zero, infinite, [subnormal][subnormal], or `NaN`.",22,[[["self"]],["bool"]]],[10,"classify","","Returns the floating point category of the number. If only one property is going to be tested, it is generally faster to use the specific predicate instead.",22,[[["self"]],["fpcategory"]]],[10,"floor","","Returns the largest integer less than or equal to a number.",22,[[["self"]],["self"]]],[10,"ceil","","Returns the smallest integer greater than or equal to a number.",22,[[["self"]],["self"]]],[10,"round","","Returns the nearest integer to a number. Round half-way cases away from `0.0`.",22,[[["self"]],["self"]]],[10,"trunc","","Return the integer part of a number.",22,[[["self"]],["self"]]],[10,"fract","","Returns the fractional part of a number.",22,[[["self"]],["self"]]],[10,"abs","","Computes the absolute value of `self`. Returns `Float::nan()` if the number is `Float::nan()`.",22,[[["self"]],["self"]]],[10,"signum","","Returns a number that represents the sign of `self`.",22,[[["self"]],["self"]]],[10,"is_sign_positive","","Returns `true` if `self` is positive, including `+0.0`, `Float::infinity()`, and since Rust 1.20 also `Float::nan()`.",22,[[["self"]],["bool"]]],[10,"is_sign_negative","","Returns `true` if `self` is negative, including `-0.0`, `Float::neg_infinity()`, and since Rust 1.20 also `-Float::nan()`.",22,[[["self"]],["bool"]]],[10,"mul_add","","Fused multiply-add. Computes `(self * a) + b` with only one rounding error, yielding a more accurate result than an unfused multiply-add.",22,[[["self"],["self"],["self"]],["self"]]],[10,"recip","","Take the reciprocal (inverse) of a number, `1/x`.",22,[[["self"]],["self"]]],[10,"powi","","Raise a number to an integer power.",22,[[["self"],["i32"]],["self"]]],[10,"powf","","Raise a number to a floating point power.",22,[[["self"],["self"]],["self"]]],[10,"sqrt","","Take the square root of a number.",22,[[["self"]],["self"]]],[10,"exp","","Returns `e^(self)`, (the exponential function).",22,[[["self"]],["self"]]],[10,"exp2","","Returns `2^(self)`.",22,[[["self"]],["self"]]],[10,"ln","","Returns the natural logarithm of the number.",22,[[["self"]],["self"]]],[10,"log","","Returns the logarithm of the number with respect to an arbitrary base.",22,[[["self"],["self"]],["self"]]],[10,"log2","","Returns the base 2 logarithm of the number.",22,[[["self"]],["self"]]],[10,"log10","","Returns the base 10 logarithm of the number.",22,[[["self"]],["self"]]],[11,"to_degrees","","Converts radians to degrees.",22,[[["self"]],["self"]]],[11,"to_radians","","Converts degrees to radians.",22,[[["self"]],["self"]]],[10,"max","","Returns the maximum of the two numbers.",22,[[["self"],["self"]],["self"]]],[10,"min","","Returns the minimum of the two numbers.",22,[[["self"],["self"]],["self"]]],[10,"abs_sub","","The positive difference of two numbers.",22,[[["self"],["self"]],["self"]]],[10,"cbrt","","Take the cubic root of a number.",22,[[["self"]],["self"]]],[10,"hypot","","Calculate the length of the hypotenuse of a right-angle triangle given legs of length `x` and `y`.",22,[[["self"],["self"]],["self"]]],[10,"sin","","Computes the sine of a number (in radians).",22,[[["self"]],["self"]]],[10,"cos","","Computes the cosine of a number (in radians).",22,[[["self"]],["self"]]],[10,"tan","","Computes the tangent of a number (in radians).",22,[[["self"]],["self"]]],[10,"asin","","Computes the arcsine of a number. Return value is in radians in the range [-pi/2, pi/2] or NaN if the number is outside the range [-1, 1].",22,[[["self"]],["self"]]],[10,"acos","","Computes the arccosine of a number. Return value is in radians in the range [0, pi] or NaN if the number is outside the range [-1, 1].",22,[[["self"]],["self"]]],[10,"atan","","Computes the arctangent of a number. Return value is in radians in the range [-pi/2, pi/2];",22,[[["self"]],["self"]]],[10,"atan2","","Computes the four quadrant arctangent of `self` (`y`) and `other` (`x`).",22,[[["self"],["self"]],["self"]]],[10,"sin_cos","","Simultaneously computes the sine and cosine of the number, `x`. Returns `(sin(x), cos(x))`.",22,N],[10,"exp_m1","","Returns `e^(self) - 1` in a way that is accurate even if the number is close to zero.",22,[[["self"]],["self"]]],[10,"ln_1p","","Returns `ln(1+n)` (natural logarithm) more accurately than if the operations were performed separately.",22,[[["self"]],["self"]]],[10,"sinh","","Hyperbolic sine function.",22,[[["self"]],["self"]]],[10,"cosh","","Hyperbolic cosine function.",22,[[["self"]],["self"]]],[10,"tanh","","Hyperbolic tangent function.",22,[[["self"]],["self"]]],[10,"asinh","","Inverse hyperbolic sine function.",22,[[["self"]],["self"]]],[10,"acosh","","Inverse hyperbolic cosine function.",22,[[["self"]],["self"]]],[10,"atanh","","Inverse hyperbolic tangent function.",22,[[["self"]],["self"]]],[10,"integer_decode","","Returns the mantissa, base 2 exponent, and sign as integers, respectively. The original number can be recovered by `sign * mantissa * 2 ^ exponent`.",22,N],[8,"FloatConst","","",N,N],[10,"E","","Return Euler’s number.",23,[[],["self"]]],[10,"FRAC_1_PI","","Return `1.0 / π`.",23,[[],["self"]]],[10,"FRAC_1_SQRT_2","","Return `1.0 / sqrt(2.0)`.",23,[[],["self"]]],[10,"FRAC_2_PI","","Return `2.0 / π`.",23,[[],["self"]]],[10,"FRAC_2_SQRT_PI","","Return `2.0 / sqrt(π)`.",23,[[],["self"]]],[10,"FRAC_PI_2","","Return `π / 2.0`.",23,[[],["self"]]],[10,"FRAC_PI_3","","Return `π / 3.0`.",23,[[],["self"]]],[10,"FRAC_PI_4","","Return `π / 4.0`.",23,[[],["self"]]],[10,"FRAC_PI_6","","Return `π / 6.0`.",23,[[],["self"]]],[10,"FRAC_PI_8","","Return `π / 8.0`.",23,[[],["self"]]],[10,"LN_10","","Return `ln(10.0)`.",23,[[],["self"]]],[10,"LN_2","","Return `ln(2.0)`.",23,[[],["self"]]],[10,"LOG10_E","","Return `log10(e)`.",23,[[],["self"]]],[10,"LOG2_E","","Return `log2(e)`.",23,[[],["self"]]],[10,"PI","","Return Archimedes’ constant.",23,[[],["self"]]],[10,"SQRT_2","","Return `sqrt(2.0)`.",23,[[],["self"]]],[0,"real","num_traits","",N,N],[8,"Real","num_traits::real","A trait for real number types that do not necessarily have floating-point-specific characteristics such as NaN and infinity.",N,N],[10,"min_value","","Returns the smallest finite value that this type can represent.",24,[[],["self"]]],[10,"min_positive_value","","Returns the smallest positive, normalized value that this type can represent.",24,[[],["self"]]],[10,"epsilon","","Returns epsilon, a small positive value.",24,[[],["self"]]],[10,"max_value","","Returns the largest finite value that this type can represent.",24,[[],["self"]]],[10,"floor","","Returns the largest integer less than or equal to a number.",24,[[["self"]],["self"]]],[10,"ceil","","Returns the smallest integer greater than or equal to a number.",24,[[["self"]],["self"]]],[10,"round","","Returns the nearest integer to a number. Round half-way cases away from `0.0`.",24,[[["self"]],["self"]]],[10,"trunc","","Return the integer part of a number.",24,[[["self"]],["self"]]],[10,"fract","","Returns the fractional part of a number.",24,[[["self"]],["self"]]],[10,"abs","","Computes the absolute value of `self`. Returns `Float::nan()` if the number is `Float::nan()`.",24,[[["self"]],["self"]]],[10,"signum","","Returns a number that represents the sign of `self`.",24,[[["self"]],["self"]]],[10,"is_sign_positive","","Returns `true` if `self` is positive, including `+0.0`, `Float::infinity()`, and with newer versions of Rust `f64::NAN`.",24,[[["self"]],["bool"]]],[10,"is_sign_negative","","Returns `true` if `self` is negative, including `-0.0`, `Float::neg_infinity()`, and with newer versions of Rust `-f64::NAN`.",24,[[["self"]],["bool"]]],[10,"mul_add","","Fused multiply-add. Computes `(self * a) + b` with only one rounding error, yielding a more accurate result than an unfused multiply-add.",24,[[["self"],["self"],["self"]],["self"]]],[10,"recip","","Take the reciprocal (inverse) of a number, `1/x`.",24,[[["self"]],["self"]]],[10,"powi","","Raise a number to an integer power.",24,[[["self"],["i32"]],["self"]]],[10,"powf","","Raise a number to a real number power.",24,[[["self"],["self"]],["self"]]],[10,"sqrt","","Take the square root of a number.",24,[[["self"]],["self"]]],[10,"exp","","Returns `e^(self)`, (the exponential function).",24,[[["self"]],["self"]]],[10,"exp2","","Returns `2^(self)`.",24,[[["self"]],["self"]]],[10,"ln","","Returns the natural logarithm of the number.",24,[[["self"]],["self"]]],[10,"log","","Returns the logarithm of the number with respect to an arbitrary base.",24,[[["self"],["self"]],["self"]]],[10,"log2","","Returns the base 2 logarithm of the number.",24,[[["self"]],["self"]]],[10,"log10","","Returns the base 10 logarithm of the number.",24,[[["self"]],["self"]]],[10,"to_degrees","","Converts radians to degrees.",24,[[["self"]],["self"]]],[10,"to_radians","","Converts degrees to radians.",24,[[["self"]],["self"]]],[10,"max","","Returns the maximum of the two numbers.",24,[[["self"],["self"]],["self"]]],[10,"min","","Returns the minimum of the two numbers.",24,[[["self"],["self"]],["self"]]],[10,"abs_sub","","The positive difference of two numbers.",24,[[["self"],["self"]],["self"]]],[10,"cbrt","","Take the cubic root of a number.",24,[[["self"]],["self"]]],[10,"hypot","","Calculate the length of the hypotenuse of a right-angle triangle given legs of length `x` and `y`.",24,[[["self"],["self"]],["self"]]],[10,"sin","","Computes the sine of a number (in radians).",24,[[["self"]],["self"]]],[10,"cos","","Computes the cosine of a number (in radians).",24,[[["self"]],["self"]]],[10,"tan","","Computes the tangent of a number (in radians).",24,[[["self"]],["self"]]],[10,"asin","","Computes the arcsine of a number. Return value is in radians in the range [-pi/2, pi/2] or NaN if the number is outside the range [-1, 1].",24,[[["self"]],["self"]]],[10,"acos","","Computes the arccosine of a number. Return value is in radians in the range [0, pi] or NaN if the number is outside the range [-1, 1].",24,[[["self"]],["self"]]],[10,"atan","","Computes the arctangent of a number. Return value is in radians in the range [-pi/2, pi/2];",24,[[["self"]],["self"]]],[10,"atan2","","Computes the four quadrant arctangent of `self` (`y`) and `other` (`x`).",24,[[["self"],["self"]],["self"]]],[10,"sin_cos","","Simultaneously computes the sine and cosine of the number, `x`. Returns `(sin(x), cos(x))`.",24,N],[10,"exp_m1","","Returns `e^(self) - 1` in a way that is accurate even if the number is close to zero.",24,[[["self"]],["self"]]],[10,"ln_1p","","Returns `ln(1+n)` (natural logarithm) more accurately than if the operations were performed separately.",24,[[["self"]],["self"]]],[10,"sinh","","Hyperbolic sine function.",24,[[["self"]],["self"]]],[10,"cosh","","Hyperbolic cosine function.",24,[[["self"]],["self"]]],[10,"tanh","","Hyperbolic tangent function.",24,[[["self"]],["self"]]],[10,"asinh","","Inverse hyperbolic sine function.",24,[[["self"]],["self"]]],[10,"acosh","","Inverse hyperbolic cosine function.",24,[[["self"]],["self"]]],[10,"atanh","","Inverse hyperbolic tangent function.",24,[[["self"]],["self"]]],[0,"cast","num_traits","",N,N],[5,"cast","num_traits::cast","Cast from one machine scalar to another.",N,[[["t"]],["option"]]],[8,"ToPrimitive","","A generic trait for converting a value to a number.",N,N],[11,"to_isize","","Converts the value of `self` to an `isize`.",25,[[["self"]],["option",["isize"]]]],[11,"to_i8","","Converts the value of `self` to an `i8`.",25,[[["self"]],["option",["i8"]]]],[11,"to_i16","","Converts the value of `self` to an `i16`.",25,[[["self"]],["option",["i16"]]]],[11,"to_i32","","Converts the value of `self` to an `i32`.",25,[[["self"]],["option",["i32"]]]],[10,"to_i64","","Converts the value of `self` to an `i64`.",25,[[["self"]],["option",["i64"]]]],[11,"to_i128","","Converts the value of `self` to an `i128`.",25,[[["self"]],["option",["i128"]]]],[11,"to_usize","","Converts the value of `self` to a `usize`.",25,[[["self"]],["option",["usize"]]]],[11,"to_u8","","Converts the value of `self` to an `u8`.",25,[[["self"]],["option",["u8"]]]],[11,"to_u16","","Converts the value of `self` to an `u16`.",25,[[["self"]],["option",["u16"]]]],[11,"to_u32","","Converts the value of `self` to an `u32`.",25,[[["self"]],["option",["u32"]]]],[10,"to_u64","","Converts the value of `self` to an `u64`.",25,[[["self"]],["option",["u64"]]]],[11,"to_u128","","Converts the value of `self` to an `u128`.",25,[[["self"]],["option",["u128"]]]],[11,"to_f32","","Converts the value of `self` to an `f32`.",25,[[["self"]],["option",["f32"]]]],[11,"to_f64","","Converts the value of `self` to an `f64`.",25,[[["self"]],["option",["f64"]]]],[8,"FromPrimitive","","A generic trait for converting a number to a value.",N,N],[11,"from_isize","","Convert an `isize` to return an optional value of this type. If the value cannot be represented by this value, then `None` is returned.",26,[[["isize"]],["option"]]],[11,"from_i8","","Convert an `i8` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["i8"]],["option"]]],[11,"from_i16","","Convert an `i16` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["i16"]],["option"]]],[11,"from_i32","","Convert an `i32` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["i32"]],["option"]]],[10,"from_i64","","Convert an `i64` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["i64"]],["option"]]],[11,"from_i128","","Convert an `i128` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["i128"]],["option"]]],[11,"from_usize","","Convert a `usize` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["usize"]],["option"]]],[11,"from_u8","","Convert an `u8` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["u8"]],["option"]]],[11,"from_u16","","Convert an `u16` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["u16"]],["option"]]],[11,"from_u32","","Convert an `u32` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["u32"]],["option"]]],[10,"from_u64","","Convert an `u64` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["u64"]],["option"]]],[11,"from_u128","","Convert an `u128` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["u128"]],["option"]]],[11,"from_f32","","Convert a `f32` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["f32"]],["option"]]],[11,"from_f64","","Convert a `f64` to return an optional value of this type. If the type cannot be represented by this value, then `None` is returned.",26,[[["f64"]],["option"]]],[8,"NumCast","","An interface for casting between machine scalars.",N,N],[10,"from","","Creates a number from another value that can be converted into a primitive via the `ToPrimitive` trait.",27,[[["t"]],["option"]]],[8,"AsPrimitive","","A generic interface for casting between machine scalars with the `as` operator, which admits narrowing and precision loss. Implementers of this trait AsPrimitive should behave like a primitive numeric type (e.g. a newtype around another primitive), and the intended conversion must never fail.",N,N],[10,"as_","","Convert a value to another, using the `as` operator.",28,[[["self"]],["t"]]],[0,"int","num_traits","",N,N],[8,"PrimInt","num_traits::int","",N,N],[10,"count_ones","","Returns the number of ones in the binary representation of `self`.",29,[[["self"]],["u32"]]],[10,"count_zeros","","Returns the number of zeros in the binary representation of `self`.",29,[[["self"]],["u32"]]],[10,"leading_zeros","","Returns the number of leading zeros in the binary representation of `self`.",29,[[["self"]],["u32"]]],[10,"trailing_zeros","","Returns the number of trailing zeros in the binary representation of `self`.",29,[[["self"]],["u32"]]],[10,"rotate_left","","Shifts the bits to the left by a specified amount amount, `n`, wrapping the truncated bits to the end of the resulting integer.",29,[[["self"],["u32"]],["self"]]],[10,"rotate_right","","Shifts the bits to the right by a specified amount amount, `n`, wrapping the truncated bits to the beginning of the resulting integer.",29,[[["self"],["u32"]],["self"]]],[10,"signed_shl","","Shifts the bits to the left by a specified amount amount, `n`, filling zeros in the least significant bits.",29,[[["self"],["u32"]],["self"]]],[10,"signed_shr","","Shifts the bits to the right by a specified amount amount, `n`, copying the \"sign bit\" in the most significant bits even for unsigned types.",29,[[["self"],["u32"]],["self"]]],[10,"unsigned_shl","","Shifts the bits to the left by a specified amount amount, `n`, filling zeros in the least significant bits.",29,[[["self"],["u32"]],["self"]]],[10,"unsigned_shr","","Shifts the bits to the right by a specified amount amount, `n`, filling zeros in the most significant bits.",29,[[["self"],["u32"]],["self"]]],[10,"swap_bytes","","Reverses the byte order of the integer.",29,[[["self"]],["self"]]],[10,"from_be","","Convert an integer from big endian to the target's endianness.",29,[[["self"]],["self"]]],[10,"from_le","","Convert an integer from little endian to the target's endianness.",29,[[["self"]],["self"]]],[10,"to_be","","Convert `self` to big endian from the target's endianness.",29,[[["self"]],["self"]]],[10,"to_le","","Convert `self` to little endian from the target's endianness.",29,[[["self"]],["self"]]],[10,"pow","","Raises self to the power of `exp`, using exponentiation by squaring.",29,[[["self"],["u32"]],["self"]]],[0,"pow","num_traits","",N,N],[5,"pow","num_traits::pow","Raises a value to the power of exp, using exponentiation by squaring.",N,[[["t"],["usize"]],["t"]]],[5,"checked_pow","","Raises a value to the power of exp, returning `None` if an overflow occurred.",N,[[["t"],["usize"]],["option"]]],[8,"Pow","","Binary operator for raising a value to a power.",N,N],[16,"Output","","The result after applying the operator.",30,N],[10,"pow","","Returns `self` to the power `rhs`.",30,N],[8,"Num","num_traits","The base trait for numeric types, covering `0` and `1` values, comparisons, basic numeric operations, and string conversion.",N,N],[16,"FromStrRadixErr","","",31,N],[10,"from_str_radix","","Convert from a string and radix <= 36.",31,[[["str"],["u32"]],["result"]]],[8,"NumOps","","The trait for types implementing basic numeric operations",N,N],[8,"NumRef","","The trait for `Num` types which also implement numeric operations taking the second operand by reference.",N,N],[8,"RefNum","","The trait for references which implement numeric operations, taking the second operand either by value or by reference.",N,N],[8,"NumAssignOps","","The trait for types implementing numeric assignment operators (like `+=`).",N,N],[8,"NumAssign","","The trait for `Num` types which also implement assignment operators.",N,N],[8,"NumAssignRef","","The trait for `NumAssign` types which also implement assignment operations taking the second operand by reference.",N,N],[11,"fmt","","",1,[[["self"],["formatter"]],["result"]]],[11,"fmt","","",0,[[["self"],["formatter"]],["result"]]],[11,"fmt","","",0,[[["self"],["formatter"]],["result"]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[["self"]],["result"]]],[11,"into","","",0,[[["self"]],["u"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"get_type_id","","",0,[[["self"]],["typeid"]]],[11,"to_string","","",0,[[["self"]],["string"]]],[11,"from","","",1,[[["t"]],["t"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[["self"]],["result"]]],[11,"into","","",1,[[["self"]],["u"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"get_type_id","","",1,[[["self"]],["typeid"]]]],"paths":[[3,"ParseFloatError"],[4,"FloatErrorKind"],[8,"Zero"],[8,"One"],[8,"Signed"],[8,"Saturating"],[8,"CheckedAdd"],[8,"CheckedSub"],[8,"CheckedMul"],[8,"CheckedDiv"],[8,"CheckedRem"],[8,"CheckedNeg"],[8,"CheckedShl"],[8,"CheckedShr"],[8,"WrappingAdd"],[8,"WrappingSub"],[8,"WrappingMul"],[8,"Inv"],[8,"MulAdd"],[8,"MulAddAssign"],[8,"Bounded"],[8,"FloatCore"],[8,"Float"],[8,"FloatConst"],[8,"Real"],[8,"ToPrimitive"],[8,"FromPrimitive"],[8,"NumCast"],[8,"AsPrimitive"],[8,"PrimInt"],[8,"Pow"],[8,"Num"]]};
searchIndex["polynomial"]={"doc":"Manipulations and data types that represent polynomial.","items":[[3,"Polynomial","polynomial","Polynomial expression",N,N],[11,"eq","","",0,[[["self"],["polynomial"]],["bool"]]],[11,"ne","","",0,[[["self"],["polynomial"]],["bool"]]],[11,"clone","","",0,[[["self"]],["polynomial"]]],[11,"fmt","","",0,[[["self"],["formatter"]],["result"]]],[11,"new","","Creates new `Polynomial`.",0,[[["vec"]],["polynomial"]]],[11,"eval","","Evaluates the polynomial value.",0,[[["self"],["t"]],["t"]]],[11,"data","","Gets the slice of internal data.",0,N],[11,"pretty","","Pretty prints the polynomial.",0,[[["self"],["str"]],["string"]]],[11,"neg","","",0,[[["self"]],["polynomial"]]],[11,"add","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"add","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"sub","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"sub","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"mul","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"mul","","",0,[[["self"],["polynomial"]],["polynomial"]]],[11,"zero","","",0,[[],["polynomial"]]],[11,"is_zero","","",0,[[["self"]],["bool"]]],[11,"one","","",0,[[],["polynomial"]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"into","","",0,[[["self"]],["u"]]],[11,"to_owned","","",0,[[["self"]],["t"]]],[11,"clone_into","","",0,N],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"try_into","","",0,[[["self"]],["result"]]],[11,"get_type_id","","",0,[[["self"]],["typeid"]]]],"paths":[[3,"Polynomial"]]};
initSearch(searchIndex);
