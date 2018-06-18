# CT-Utils

This crate contains types and behaviours which resolve at compile time.

## Getting started

Include this crate as dependancy by inserting the following into your `Cargo.toml` file.

```toml
[dependencies]
ct-utils = "1.10.0"
```

Inside your `lib.rs` or `main.rs` add the usage of this crate.
Often used types are re-exported inside the prelude of this crate which lower the
verbosity of your implementation. Otherwise all types are accessible through their fully
qualified path.

```rust
#[macro_use] extern crate ct_utils;

// Optional
use ct_utils::prelude::*;
```

And you're all set!

## Usage

An example of the included cons list is shown, which is the `CTCons` trait.

Construct a cons list of type items and calculate the offset of one specific type.

```rust
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
```
