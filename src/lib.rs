#![feature(specialization)]
#![deny(missing_docs)]

//! Crate containing compile time utilities.
//!
//!

extern crate typenum;

#[macro_use]
pub mod ct_if;
/* Macro containing modules gutter */
pub mod ct_cons;

pub mod prelude {
    //! Re-export of often used types and behaviour.
    //!
    pub use ct_cons::{CTAppend, CTCons, CTConsTerm, CTOffsetExt, CTSized};
    pub use ct_if::{CTBool, CTFalse, CTIf, CTTrue, IfCheck};
}
