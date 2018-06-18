//! This module defines two list types: [`TList`] and [`VList`].
//! Both lists are a kind of cons list, but the T in [`TList`] stands for type
//! and the V in [`VList`] stands for value.
//!
//! [`TList`] is intended as cons list for reasoning about types.
//! [`VList`] is intended as heterogenous list, it's functionality is similar to the
//! HCons type within the Frunk crate.
//!
//! These list types can be queried and query results are only calculated during compilation.
//! See [`CTSized`], [`CTOffset`] and [`VPick`] for more information about querying.
//!
//! # Example
//! ```rust
//! extern crate ct_utils;
//! use ct_utils::prelude::*;
//! use ct_utils::ct_cons::Cons;
//!
//! fn main() {
//!     type ExampleOne = Cons<Cons<Cons<TTerm, u8>, &'static str>, u64>;
//!     //
//!     type ExampleTwo = <<TTerm as TAppend<u8>>::Output as TAppend<u32>>::Output;
//!     //
//!     let vlist = VNil.push(0u8).push("Hello").push(0u64);
//! }
//! ```

use std::marker::PhantomData;
use std::ops::Add;
use typenum::{U0, U1, Unsigned};

/// Represents a cons list for reasoning about types, their order and offsets.
///
/// Type lists are 0-sized. Look at [`VList`] if storage of data is also necessary.
///
/// # Preconditions
/// -   The item types are not specifically constrained, it's best to only push unique items
///     into the list. That way all queries will always return the expected result.
///     Type X is considered different from Type Y if their TypeId do not match. eg
///     `std::any::TypeId::of::<X> == std::any::TypeId::of::<Y>`
///     See [`std::any::TypeId`].
///
pub trait TList {
    /// The item that was most recently appended to the list.
    type Head;
    /// The parent list of the current one.
    /// The parent list is exactly the same list as Self, but the Head item is removed.
    type Tail: TList;
}

/// Represents a cons list for heterogenous storage of data.
///
/// A [`VList`] is almost functionally identical to [`TList`] except for the storage part.
/// The items within this list are actual values.
///
pub trait VList {
    /// The type of the item that was most recently appended to the list.
    type Head;
    /// The parent list of the current one.
    /// The parent list is exactly the same list as Self, but the Head item is removed.
    type Tail: VList;
}

#[doc(hidden)]
// Trait used to count the amount of items within [`TList`], but due to constraints must be publicly
// exported.
// Use the trait [`CTSized`] to query the size of [`TList`].
pub trait CTCounter {
    /// A type defined by [`typenum`] which represents an unsigned integer.
    /// On this type is also addition with 1u implemented.
    ///
    /// # Note
    /// The only operation possible on this type is addition and creation of a corresponding value.
    type Monotone: Unsigned + Add<U1>;
}

/// Trait for retrieving the amount of items within compile time structures.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// # fn main() {
/// let size = <Cons<Cons<Cons<TTerm, u8>, u32>, u64> as CTSized>::size();
/// assert_eq!(size, 3);
/// # }
/// ```
pub trait CTSized {
    /// The amount of items within the implemented compile time structure.
    /// The amount is encoded as a type, provided by [`typenum`].
    type Size: Unsigned;

    /// Returns the amount of items as a value.
    fn size() -> usize;
}

/// Trait used to calculate the offset of a specific type item within compile time structures.
/// The offset is 0-indexed which means that the 1st item will be at offset 0.
///
/// # Note
/// -   The compiler will throw an error if the requested type is not found within the
///     compile time structure.
/// -   This does NOT produce expected results if the list contains multiple items
///     of identical types.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// # fn main() {
/// let offset = <Cons<Cons<Cons<TTerm, u8>, u32>, u64> as CTOffset<u64, _>>::offset();
/// assert_eq!(offset, 2);    // Note: Offset is 0-indexed!
/// # }
/// ```
///
/// The following example does not compile.
/// ```rust,compile_fail
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// let offset = <Cons<Cons<Cons<TTerm, u8>, u32>, u64> as CTOffset<i64, _>>::offset();
/// # }
pub trait CTOffset<Target, Distance> {
    /// The offset of the Target item within the implemented compile time structure.
    /// The offset is encoded as a type, provided by [`typenum`].
    type Offset: Unsigned;

    /// Returns the offset of Target as a value.
    fn offset() -> usize;
}

/*
/// Trait used to calculate the offset of a specific type without upcasting to the
/// [`CTOffset`] trait.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # use ct_utils::ct_cons::Cons;
/// type BigList = Cons<Cons<Cons<TListTerm, u8>, u32>, u64>;
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
*/

/// Trait used to append items to a [`TList`].
///
/// This trait is only applicable to [`TList`]. For the [`VList`] variant look at
/// [`VAppend`].
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// type ExampleTwo = <<TTerm as TAppend<u8>>::Output as TAppend<u32>>::Output;
/// # }
/// ```
pub trait TAppend<X>
where
    Self: TList,
{
    /// The new compile time structure with the new item appended.
    type Output: TList;
}

/// Trait used to append items to a [`VList`].
///
/// This trait is only applicable to [`VList`]. For the [`TList`] variant look at
/// [`TAppend`].
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// let mut big_int = 50u64;
/// let vlist = VNil.push(0u32).push("hello").push(&mut big_int);
/// # }
/// ```
pub trait VAppend<X>
where
    Self: VList,
{
    /// The new type of list after pushing the new value.
    type Output: VList;

    /// Returns a new list by pushing the provided item into the implemented list.
    fn push(self, item: X) -> Self::Output;
}

/// Trait used to retrieve the value of a specified item from a [`VList`].
///
/// # Note
/// -   This does NOT produce expected results if the list contains multiple items
///     of identical types.
/// -   Be wary of references you push into the list, each call to [`VPick::get`]
///     and [`VPick::get_mut`] will return a reference to the item.
///     Retrieving a mutable reference to an immutable reference will not allow to
///     overwrite the referenced item, but does allow to replace the immutable
///     reference with some other reference.
///
/// # Example
/// ```rust
/// # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// let vlist = VNil.push(0u32).push("hello");
/// let the_string: &&str = vlist.get();
/// println!("String is: {}", the_string);
/// # }
/// ```
///
/// The following example does not compile.
/// ```rust,compile_fail
///  # extern crate ct_utils;
/// # use ct_utils::prelude::*;
/// # fn main() {
/// let vlist = VNill.push(0u32).push("hello");
/// let the_string: &i64 = vlist.get();
/// println!("String is: {}", the_string);
/// # }
/// ```
pub trait VPick<Target, Distance>
where
    Self: VList,
{
    /// Retrieves a reference to the value, which is stored as Target type, within the current list.
    fn get(&self) -> &Target;

    /// Retrieves a mutable reference to the value, which is stored as Target type, within the current list.
    fn get_mut(&mut self) -> &mut Target;
}

/// Termination type for [`TList`].
///
/// This type cannot be instantiated so it's only useful at type-level.
pub enum TTerm {}

/// Termination type for [`VList`].
///
/// This is a 0-sized type when instantiated.
pub struct VNil;

#[doc(hidden)]
// Type used to help the compiler distinguish between implementation blocks.
// Here effectively means that the head of the subject list IS the item we're looking for.
pub enum Here {}

#[doc(hidden)]
// Type used to help the compiler distinguis between implementation blocks.
// There effectively means that the item we're looking for is at a relative offset.
// The relative offset is recursively encoded within this type. eg
// `There<There<There<Here>>>`
// indicates that 3 recursions must happen to find our target.
pub struct There<T>(PhantomData<T>);

/// Actual type used to represent type list information.
///
/// This type is useful to create a new [`TList`] with compact syntax, see the example
/// within the module documentation.
/// Other than for creating new lists this structure isn't useful.
pub struct Cons<Tail, Head>
where
    Tail: TList,
{
    _marker: PhantomData<(Tail, Head)>,
}

/// Actual type used to represent and carry value list information.
///
/// This type also contains values for the types it has encoded within the signature.
pub struct VCons<Tail, Head>
where
    Tail: VList,
{
    head: Head,
    tail: Tail,
}

impl CTCounter for TTerm {
    type Monotone = U0;
}

impl CTCounter for VNil {
    type Monotone = U0;
}

impl<Tail, Head> CTCounter for Cons<Tail, Head>
where
    Tail: TList + CTCounter,
    <<Tail as CTCounter>::Monotone as Add<U1>>::Output: Unsigned + Add<U1>,
{
    type Monotone = <Tail::Monotone as Add<U1>>::Output;
}

impl<Tail, Head> CTCounter for VCons<Tail, Head>
where
    Tail: VList + CTCounter,
    <<Tail as CTCounter>::Monotone as Add<U1>>::Output: Unsigned + Add<U1>,
{
    type Monotone = <Tail::Monotone as Add<U1>>::Output;
}

impl TList for TTerm {
    type Head = ();
    type Tail = TTerm;
}

impl VList for VNil {
    type Head = ();
    type Tail = VNil;
}

impl<Tail, Head> TList for Cons<Tail, Head>
where
    Tail: TList,
{
    type Head = Head;
    type Tail = Tail;
}

impl<Tail, Head> VList for VCons<Tail, Head>
where
    Tail: VList,
{
    type Head = Head;
    type Tail = Tail;
}

impl<Tail, Head> CTSized for Cons<Tail, Head>
where
    Tail: TList + CTCounter,
    <<Tail as CTCounter>::Monotone as Add<U1>>::Output: Unsigned,
{
    type Size = <Tail::Monotone as Add<U1>>::Output;

    fn size() -> usize {
        Self::Size::to_usize()
    }
}

impl<Tail, Head> CTSized for VCons<Tail, Head>
where
    Tail: VList + CTCounter,
    <<Tail as CTCounter>::Monotone as Add<U1>>::Output: Unsigned,
{
    type Size = <Tail::Monotone as Add<U1>>::Output;

    fn size() -> usize {
        Self::Size::to_usize()
    }
}

impl<Tail, Target> CTOffset<Target, Here> for Cons<Tail, Target>
where
    Tail: TList + CTCounter,
{
    type Offset = Tail::Monotone;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<Tail, Head, Target, TailDistance> CTOffset<Target, There<TailDistance>> for Cons<Tail, Head>
where
    Tail: TList + CTCounter + CTOffset<Target, TailDistance>,
{
    type Offset = Tail::Offset;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<Tail, Target> CTOffset<Target, Here> for VCons<Tail, Target>
where
    Tail: VList + CTCounter,
{
    type Offset = Tail::Monotone;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<Tail, Head, Target, TailDistance> CTOffset<Target, There<TailDistance>> for VCons<Tail, Head>
where
    Tail: VList + CTCounter + CTOffset<Target, TailDistance>,
{
    type Offset = Tail::Offset;

    fn offset() -> usize {
        Self::Offset::to_usize()
    }
}

impl<X> TAppend<X> for TTerm
where
    Cons<TTerm, X>: TList,
{
    type Output = Cons<TTerm, X>;
}

impl<Tail, Head, X> TAppend<X> for Cons<Tail, Head>
where
    Tail: TList,
    Cons<Cons<Tail, Head>, X>: TList,
{
    type Output = Cons<Cons<Tail, Head>, X>;
}

impl<X> VAppend<X> for VNil
where
    VCons<VNil, X>: VList,
{
    type Output = VCons<VNil, X>;

    fn push(self, item: X) -> Self::Output {
        VCons {
            head: item,
            tail: self,
        }
    }
}

impl<Tail, Head, X> VAppend<X> for VCons<Tail, Head>
where
    Tail: VList,
    VCons<VCons<Tail, Head>, X>: VList,
{
    type Output = VCons<VCons<Tail, Head>, X>;

    fn push(self, item: X) -> Self::Output {
        VCons {
            head: item,
            tail: self,
        }
    }
}

impl<Tail, Target> VPick<Target, Here> for VCons<Tail, Target>
where
    Self: VList,
    Tail: VList,
{
    fn get(&self) -> &Target {
        &self.head
    }

    fn get_mut(&mut self) -> &mut Target {
        &mut self.head
    }
}

impl<Tail, Head, Target, TailDistance> VPick<Target, There<TailDistance>> for VCons<Tail, Head>
where
    Self: VList,
    Tail: VList + VPick<Target, TailDistance>,
{
    fn get(&self) -> &Target {
        self.tail.get()
    }

    fn get_mut(&mut self) -> &mut Target {
        self.tail.get_mut()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    type TSingle = Cons<TTerm, i32>;
    type TMiddle = Cons<Cons<Cons<TTerm, i32>, u32>, f32>;
    type TBig = Cons<Cons<Cons<Cons<Cons<TTerm, i32>, u32>, f32>, i64>, usize>;

    lazy_static! {
        static ref VSINGLE: VCons<VNil, i32> = VNil.push(0i32);
        static ref VMIDDLE: VCons<VCons<VCons<VNil, i32>, u32>, f32> =
            { VNil.push(0i32).push(0u32).push(0f32) };
        static ref VBIG: VCons<VCons<VCons<VCons<VCons<VNil, i32>, u32>, f32>, i64>, usize> = {
            VNil.push(0i32)
                .push(0u32)
                .push(0f32)
                .push(0i64)
                .push(0usize)
        };
    }

    fn type_offset_for<List, X, Distance>() -> usize
    where
        List: TList + CTOffset<X, Distance>,
    {
        List::offset()
    }

    fn value_offset_for<List, X, Distance>(_list: &List) -> usize
    where
        List: VList + CTOffset<X, Distance>,
    {
        List::offset()
    }

    fn value_size_for<List>(_list: &List) -> usize
    where
        List: VList + CTSized,
    {
        List::size()
    }

    #[test]
    fn type_sized_single() {
        let size = TSingle::size();
        assert_eq!(size, 1);
    }

    #[test]
    fn value_sized_single() {
        let size = value_size_for(&*VSINGLE);
        assert_eq!(size, 1);
    }

    #[test]
    fn type_sized_big() {
        let size = TBig::size();
        assert_eq!(size, 5);
    }

    #[test]
    fn value_sized_big() {
        let size = value_size_for(&*VBIG);
        assert_eq!(size, 5);
    }

    #[test]
    fn value_offset_first() {
        let offset = type_offset_for::<TSingle, i32, _>();
        assert_eq!(offset, 0);
    }

    #[test]
    fn type_offset_first() {
        let offset = value_offset_for::<_, i32, _>(&*VSINGLE);
        assert_eq!(offset, 0);
    }

    #[test]
    fn type_offset_middle() {
        let offset = type_offset_for::<TMiddle, u32, _>();
        assert_eq!(offset, 1);
    }

    #[test]
    fn value_offset_middle() {
        let offset = value_offset_for::<_, u32, _>(&*VMIDDLE);
        assert_eq!(offset, 1);
    }

    #[test]
    fn type_offset_end() {
        let offset = type_offset_for::<TBig, usize, _>();
        assert_eq!(offset, 4);
    }

    #[test]
    fn value_offset_end() {
        let offset = value_offset_for::<_, usize, _>(&*VBIG);
        assert_eq!(offset, 4);
    }

    #[test]
    fn value_replace() {
        let mut list = VNil.push(0u32).push(0i8).push("Hello");
        *list.get_mut() = 10i8;
        *list.get_mut() = "Hello World";

        let number: i8 = *list.get();
        assert_eq!(number, 10i8);

        let string: &str = *list.get();
        assert_eq!(string, "Hello World");
    }
}
