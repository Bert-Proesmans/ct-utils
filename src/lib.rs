// #![deny(missing_docs)]
#![doc(html_root_url = "https://docs.rs/ct-utils/0.0.1")]

//! Crate containing compile time utilities.
//!
//!

extern crate typenum;

#[cfg(test)]
#[macro_use]
extern crate lazy_static;

// #[macro_use]
// pub mod ct_if;
/* Macro containing modules gutter */
pub mod ct_cons;
// pub mod ct_array;

pub mod prelude {
    //! Re-export of often used types and behaviour.
    //!
    pub use ct_cons::{CTOffset, CTSized, TAppend, TList, TTerm, VAppend, VList, VNil, VPick};
    // pub use ct_if::{CTBool, CTFalse, CTIf, CTTrue, IfCheck};
}
