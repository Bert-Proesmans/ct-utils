/* README TEST */
#[allow(unused_imports)]

#[macro_use] extern crate ct_utils;

use ct_utils::prelude::*;
use ct_utils::ct_cons::Cons;

type BigList = Cons<Cons<Cons<Cons<Cons<TTerm, i32>, u32>, f32>, i64>, usize>;

fn main() {
	let list_size = BigList::size();							// 1-indexed
	let list_offset = <BigList as CTOffset<i64, _>>::offset(); 	// 0-indexed

	assert!(list_size > list_offset);
	assert_eq!(list_size, 5);
	assert_eq!(list_offset, 3);
}
