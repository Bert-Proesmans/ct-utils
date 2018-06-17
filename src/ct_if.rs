//! This module defines a types to encode an IF test within the type system.
//!
//! The idea behind this concept is to match the condition, which is a type,
//! with the structure the test is implemented for.
//! This allows for a basic test similar to the following
//! ```rust
//! let result = std::any::TypeId::of::<i32>() == std::any::TypeId::of::<i32>();
//! if result {
//!     // Condition matched
//! } else {
//!     // Condition failed to match
//! }
//! ```
//!
//! # Example
//! ```rust,no_run
//! # extern crate ct_utils;
//! use ct_utils::prelude::*;
//!
//! // Trait to negate the signed-ness of a specific integer.
//! trait DeSignature<Target> {
//!     type Result: ?Sized;
//! }
//!
//! impl<Target> DeSignature<Target> for i32 {
//!     // Depending on Target, CTIf::Path will become signed or unsigned.
//!     // Result will receive the type contained by CTIf::Path.
//!     type Result = <IfCheck<i32> as CTIf<Target, u32, i32>>::Path;
//! }
//! ```
//!
//! # Notes
//! -   If the receiving type parameter is constrained, the generic [`CTIf`] causes
//!     compilation errors due to missing constraints.
//!     You have to create your own specialized implementation of [`CTIf`], which is
//!     made easy by utilizing the macro [`ctif_specialize`].
//!

use std::marker::PhantomData;

/// Represents a boolean value encoded within the typesystem.
///
/// See also [`CTFalse`] and [`CTTrue`].
pub trait CTBool {
    /// Returns a boolean value corresponding to the implemented type.
    fn to_bool() -> bool;
}

/// Generic version of an IF test encoded within the type system.
///
/// Condition   is the type which must match.
/// OptionTrue  will be passed into [`CTIf::Path`] if the condition match is TRUE.
/// OptionFalse will be passed into [`CTIf::Path`] if the condition match is FALSE.
///
/// Specialized versions of this trait are necessary when the receiving type parameter
/// is constrained. See [`ctif_specialize`] to create such a specialized version.
pub trait CTIf<Condition, OptionTrue, OptionFalse>
where
    OptionTrue: 'static + ?Sized,
    OptionFalse: 'static + ?Sized,
{
    /// Type representing how the condition on the implemented type matches.
    type Result: CTBool;
    /// Type which holds either of the two generic option arguments, depending on how the
    /// condition matches.
    type Path: 'static + ?Sized;
}

/// Type representing a FALSE value.
pub enum CTFalse {}
/// Type representing a TRUE value.
pub enum CTTrue {}

/// Actual type used to perform an IF check through the type system.
///
/// Performing an IF test through the type system requires both this structure as well
/// as the [`CTIf`] trait (or a specialized one). The typed that needs to be matched
/// is passed into this struct as generic argument for X.
/// The resulting type must then be cast as [`CTIf`] trait, which includes the desired type.
/// [`CTIf::Path`] will then hold the match relevant type.
/// eg
/// ```rust,ignore
/// <IfCheck<Subject> as CTIf<Desired, TypeTrue, TypeFalse>>::Path;
/// ```
pub struct IfCheck<X> {
    _marker: PhantomData<X>,
}

impl CTBool for CTFalse {
    fn to_bool() -> bool {
        false
    }
}

impl CTBool for CTTrue {
    fn to_bool() -> bool {
        true
    }
}

impl<X, CondFail, OptionTrue, OptionFalse> CTIf<CondFail, OptionTrue, OptionFalse> for IfCheck<X>
where
    OptionTrue: 'static + ?Sized,
    OptionFalse: 'static + ?Sized,
{
    default type Result = CTFalse;
    default type Path = OptionFalse;
}

impl<X, OptionTrue, OptionFalse> CTIf<X, OptionTrue, OptionFalse> for IfCheck<X>
where
    OptionTrue: 'static + ?Sized,
    OptionFalse: 'static + ?Sized,
{
    type Result = CTTrue;
    type Path = OptionTrue;
}

/// Macro for specializing [`CTIf`].
///
/// If receiving associated types are constrained, the generic [`CTIf`] is not usable any more
/// because there is no syntax carrying over these constraints accross the IF test.
/// Solving this requires building a new trait similar to [`CTIf`] with constraints which are
/// specific to your use case. These constraints will be applied to [`CTIf::Path`].
///
/// This macro helps in building that specialization. It creates a specialized trait and implements
/// it for [`IfCheck`], the latter can be re-used accross specializations.
/// Implementers only need to provide a new name for the trait and the required constraints.
/// Provided outer attributes are applied to the newly created trait as well.
///
/// Using this specialized trait is analogue to using [`CTIf`] and [`IfCheck`].
///
/// # Example
/// ```rust,ignore
/// ctif_specialize {
///     /// Optional doc-attribute explaining things about the special IF test.
///     trait_name = "MySpecialIf",
///     conditions = [Add<u32>, Mul<u32>]
/// }
///  ```
///
/// That macro call will expand to the following code.
/// ```rust, ignore
/// /// Optional doc-attribute explaining things about the special IF test.
/// pub trait MySpecialIf<Condition, OptionTrue, OptionFalse> {
///     type Result: CTBool;
///     type Path: Add<u32> + Mul<u32>;
/// }
/// ```
#[macro_export]
macro_rules! ctif_specialize {
    (
        $( #[$meta_links:meta] )*
        trait_name = $trait:ident,
        conditions = [$($cond:path),+]
    ) => {
        $( #[$meta_links] )*
    	pub trait $trait<Condition, OptionTrue, OptionFalse> {
            /// Auto generated
    		type Result: $crate::ct_if::CTBool;
    		/// Auto generated
            type Path: $( $cond +)+;
    	}

    	impl<X, CondFail, OptionTrue, OptionFalse> $trait<CondFail, OptionTrue, OptionFalse> for $crate::ct_if::IfCheck<X>
    	where
    		OptionTrue: $( $cond +)+,
    		OptionFalse: $( $cond +)+,
    	{
		    default type Result = $crate::ct_if::CTFalse;
		    default type Path = OptionFalse;
		}

		impl<X, OptionTrue, OptionFalse> $trait<X, OptionTrue, OptionFalse> for $crate::ct_if::IfCheck<X>
		where
    		OptionTrue: $( $cond +)+,
    		OptionFalse: $( $cond +)+,
		{
		    type Result = $crate::ct_if::CTTrue;
		    type Path = OptionTrue;
		}
    };
}

#[cfg(test)]
mod test {
    use super::*;
    use std::any::TypeId;

    fn match_on<Subject: CTBool>() -> TypeId {
        TypeId::of::<<IfCheck<Subject> as CTIf<CTTrue, CTTrue, CTFalse>>::Path>()
    }

    #[test]
    fn test_true() {
        assert_eq!(match_on::<CTTrue>(), TypeId::of::<CTTrue>());
    }

    #[test]
    fn test_false() {
        assert_eq!(match_on::<CTFalse>(), TypeId::of::<CTFalse>());
    }
}
