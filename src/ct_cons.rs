//! This module defines a cons list for types, [`CTCons`].
//! The cons list can be queried and the result is calculated at compile time.
//! See [`CTSized`] and [`CTOffset`] for more information about querying the cons list.
//!
//! # Example
//! ```rust
//! extern crate ct_utils;
//! use ct_utils::prelude::*;
//! use ct_utils::ct_cons::Cons;
//!
//! fn main() {
//!     type ExampleOne = Cons<Cons<Cons<CTConsTerm, u8>, u32>, u64>;
//!     //
//!     type ExampleTwo = <<CTConsTerm as CTAppend<u8>>::Output as CTAppend<u32>>::Output;
//! }
//! ```

use ct_if::IfCheck;
use std::marker::PhantomData;
use std::ops::Add;
use typenum::{U0, U1, U1024, Unsigned};

/// This value is returned when querying [`CTOffset`] and the requested type is not
/// found within the subject [`CTCons`].
pub type CTConsOffsetInvalid = U1024;

/// Represents a cons list where each new addition builds further onto the previous list.
/// The previous list is at [`CTCons::Tail`] and [`CTConsTerm`] is used as bootstrapper
/// to create the initial tail.
/// The latest item is at [`CTCons::Head`].
///
/// Use [`CTAppend`] to add new types to the cons list.
///
/// # Preconditions
/// -   The cons list MUST NOT contain multiple items of the exact same type. This will result
///     in wrong offsets.
///     Type X and Type Y are considered exactly the same if their TypeId match. eg
///     `std::any::TypeId::of::<X> == std::any::TypeId::of::<Y>`
///     See [`std::any::TypeId`].
///
pub trait CTCons {
    /// The head of the list. This is exactly one item.
    type Head: 'static;
    /// This is the parent of the implemented type. The tail contains all items except the Head
    /// of the implemented type.
    type Tail: CTCons + 'static;
}

#[doc(hidden)]
// Trait used to count the amount of items within [`CTCons`], but due to constraints must be publicly
// exported.
// Use the trait [`CTSized`] to query the size of [`CTCons`].
pub trait CTCounter {
    /// A type defined by [`typenum`] which represents an unsigned integer.
    /// On this type is also addition with 1u implemented.
    ///
    /// # Note
    /// The only operation possible on this type is addition and creation of a corresponding value.
    type Counter: Unsigned + Add<U1>;
}

/// Trait used to append items to compile time structure.
///
/// Cast the parent structure as [`CTAppend`] whith the addition as generic argument.
/// If this trait is implemented for the parent structure, [`CTAppend::Output`] will
/// hold the resulting type.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// type ExampleTwo = <<CTConsTerm as CTAppend<u8>>::Output as CTAppend<u32>>::Output;
/// # }
/// ```
pub trait CTAppend<X> {
    /// The new compile time structure which consists of the implemented structure
    /// with X as new item.
    type Output: CTCons;
}

/// Trait used to measure the amount of items within compile time structures.
///
/// Cast the structure as [`CTSized`]. If this trait is implemented, you can query the
/// size from [`CTSized::Size`].
/// Alternatively a value can be constructed from the type representing the size, just
/// call [`CTSized::size`].
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// # fn main() {
/// let size = <Cons<Cons<Cons<CTConsTerm, u8>, u32>, u64> as CTSized>::size();
/// assert_eq!(size, 3);
/// # }
/// ```
pub trait CTSized {
    /// The size representation of the implemented compile time structure.
    type Size: Unsigned;

    /// Returns the amount of items added to the implemented compile time structure.
    fn size() -> usize;
}

/// Trait used to calculate the 0-indexed offset of a specific type item within
/// compile time structures.
///
/// Cast the structure as [`CTOffset`]. If this trait is implemented, you can query the
/// offset of the requested item from [`CTOffset::Offset`].
/// Alternatively a value can be constructed representing the offset, just call
/// [`CTOffset::offset`].
///
/// ** Preferably use the [`CTOffsetExt`] trait! **
///
/// # Note
/// If the requested type cannot be found within the implemented structure,
/// [`CTConsOffsetInvalid`] is returned.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// # use ct_utils::ct_cons::CTOffset;
/// # fn main() {
/// let offset = <Cons<Cons<Cons<CTConsTerm, u8>, u32>, u64> as CTOffset<u64>>::offset();
/// assert_eq!(offset, 2);    // Note: Offset is 0-indexed!
/// # }
/// ```
pub trait CTOffset<Target> {
    /// The offset representation of the type Target within the implemented compile time
    /// structure.
    ///
    /// # Note
    /// If the type was NOT found within the implemented ct structure, [`CTConsOffsetInvalid`]
    /// is provided.
    type Offset: Unsigned + Add<U1>;

    /// Returns a value representing the offset within the compile time structure.
    fn offset() -> usize;
}

/// Trait used to calculate the offset of a specific type without upcasting to the
/// [`CTOffset`] trait.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// type BigList = Cons<Cons<Cons<CTConsTerm, u8>, u32>, u64>;
/// # fn main() {
/// let offset = BigList::offset_of::<u64>();
/// assert_eq!(offset, 2);    // Note: Offset is 0-indexed!
/// # }
/// ```
pub trait CTOffsetExt {
    /// Returns the offset of the provided type within the implemented compile time
    /// structure.
    fn offset_of<X>() -> usize
    where
        Self: CTOffset<X>;
}

/// Termination type for [`Cons`].
///
/// Use this type to construct a new cons list ([`CTCons`]). See [`CTAppend`] for more
/// information.
pub enum CTConsTerm {}

/// Actual type used to carry cons list information.
///
/// This type is useful to create a new cons list in a compact syntax, like the example
/// within the module documentation. Other than for creating new cons lists this structure
/// isn't useful.
pub struct Cons<Tail, Head>
where
    Tail: CTCons,
{
    _marker: PhantomData<(Tail, Head)>,
}

ctif_specialize!{
    /// Specialized implementation of [`IfCheck`] to accomodate for the additional constraints
    /// necessary on [`CTIf::Path`].
    trait_name = CTIfOffset,
    conditions = [Unsigned, Add<U1>]
}

impl CTCons for CTConsTerm {
    type Head = ();
    type Tail = CTConsTerm;
}

impl<X> CTAppend<X> for CTConsTerm
where
    X: 'static,
{
    type Output = Cons<CTConsTerm, X>;
}

impl CTCounter for CTConsTerm {
    type Counter = U0;
}

impl<Target> CTOffset<Target> for CTConsTerm {
    type Offset = CTConsOffsetInvalid;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<Tail, Head> CTCons for Cons<Tail, Head>
where
    Tail: CTCons + 'static,
    Head: 'static,
{
    type Head = Head;
    type Tail = Tail;
}

impl<X, Tail, Head> CTAppend<X> for Cons<Tail, Head>
where
    X: 'static,
    Tail: CTCons + 'static,
    Head: 'static,
{
    type Output = Cons<Cons<Tail, Head>, X>;
}

impl<Tail, Head> CTCounter for Cons<Tail, Head>
where
    Tail: CTCounter + CTCons,
    <<Tail as CTCounter>::Counter as Add<U1>>::Output: Unsigned + Add<U1>,
{
    type Counter = <Tail::Counter as Add<U1>>::Output;
}

impl<Tail, Head> CTSized for Cons<Tail, Head>
where
    Tail: CTCons,
    Self: CTCounter,
{
    type Size = <Self as CTCounter>::Counter;

    fn size() -> usize {
        Self::Size::to_usize()
    }
}

impl<Target, Tail, Head> CTOffset<Target> for Cons<Tail, Head>
where
    Tail: CTCons + CTOffset<Target> + CTCounter,
{
    type Offset = <IfCheck<Head> as CTIfOffset<Target, Tail::Counter, Tail::Offset>>::Path;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<C> CTOffsetExt for C
where
    C: CTCons,
{
    fn offset_of<X>() -> usize
    where
        C: CTOffset<X>,
    {
        C::offset()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    type Single = Cons<CTConsTerm, i32>;
    type Middle = Cons<Cons<Cons<CTConsTerm, i32>, u32>, f32>;
    type Big = Cons<Cons<Cons<Cons<Cons<CTConsTerm, i32>, u32>, f32>, i64>, usize>;

    #[test]
    fn sized_single() {
        let size = Single::size();
        assert_eq!(size, 1);
    }

    #[test]
    fn sized_big() {
        let size = Big::size();
        assert_eq!(size, 5);
    }

    fn offset_for<CTCons, Target>() -> usize
    where
        CTCons: CTOffset<Target>,
    {
        CTCons::offset()
    }

    #[test]
    fn offset_first() {
        let offset = offset_for::<Single, i32>();
        assert_eq!(offset, 0);
    }

    #[test]
    fn offset_middle() {
        let offset = offset_for::<Middle, u32>();
        assert_eq!(offset, 1);
    }

    #[test]
    fn offset_end() {
        let offset = offset_for::<Big, usize>();
        assert_eq!(offset, 4);
    }

    #[test]
    fn offset_unknown() {
        let offset = offset_for::<Single, f32>();
        assert_eq!(offset, CTConsOffsetInvalid::to_usize());
    }
}
