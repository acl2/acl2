; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "editions")
(include-book "syntax/top")
(include-book "mir/top")
(include-book "import/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc rust
  :parents (acl2::kestrel-books)
  :short "An ACL2 library for the Rust programming language."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library aims at a deep embedding of Rust in ACL2:
     Rust programs are represented as ACL2 data at every stage of
     a pipeline that mirrors the Rust compiler's front half
     &mdash; lexing (with token trees), parsing,
     macro expansion, name resolution, desugaring,
     type and trait checking, and lowering to MIR
     (the compiler's mid-level intermediate representation) &mdash;
     together with an interpreter of MIR
     that plays the role that Miri plays for rustc.
     Since Rust has no normative specification,
     we follow a basket of references:
     the "
    (xdoc::ahref "https://rust-lang.github.io/fls/"
                 "Ferrocene Language Specification")
    ", the "
    (xdoc::ahref "https://doc.rust-lang.org/1.87.0/reference/"
                 "Rust Reference")
    ", the "
    (xdoc::ahref "https://github.com/rust-lang/rust/tree/1.87.0"
                 "Rust compiler")
    " (pinned at version 1.87.0), "
    (xdoc::ahref "https://github.com/minirust/minirust"
                 "MiniRust")
    " for the MIR semantics, and "
    (xdoc::ahref "https://github.com/rust-lang/miri"
                 "Miri")
    " as a testing oracle.")
   (xdoc::p
    "The library is organized in two tracks,
     following the "
    (xdoc::seetopic "c::c" "C library")
    ":
     a tool-oriented syntax track in the @('\"RUST$\"') package
     (see @(see rust$::syntax-for-tools)),
     which aims at representing, parsing, and printing
     the full surface language;
     and a language-formalization track in the @('\"RUST\"') package,
     which gives static and dynamic semantics to
     growing subsets of the language.
     The supported editions are Rust 2021 and 2024
     (see @(see editions)), with 2024 the default.")
   (xdoc::p
    "This is work in progress, at an early stage.
     At this time of writing, lexing is done.")))
