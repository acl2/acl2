; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

; These allow the deftypes clique below to prove
; its internal theorems under the controlled configuration,
; as in ../syntax/token-trees.lisp.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir
  :parents (rust)
  :short "A formalization of MIR, rustc's mid-level intermediate
          representation."
  :long
  (xdoc::topstring
   (xdoc::p
    "MIR is the control-flow-graph representation on which
     rustc performs borrow checking, drop elaboration,
     and optimization, and from which it generates code;
     it is also the representation that
     our interpreter executes and
     our importer extracts from rustc.
     The fixtypes mirror <i>rustc's</i> MIR syntax
     (its types, places, rvalues, statements, and terminators,
     as the importer receives them),
     while the interpreter's state and value model
     will follow "
    (xdoc::ahref "https://github.com/minirust/minirust" "MiniRust")
    ";
     this dialect decision is D9 in the plan document.")
   (xdoc::p
    "This is a draft covering the monomorphic core
     (the R0 subset of the plan's subset ladder,
     which is also the shape of post-monomorphization code):
     there are no type parameters, no regions/lifetimes
     (MIR for execution has them erased),
     and, per the plan's panic=abort decision (D3),
     no unwind edges in terminators.")
   (xdoc::p
    "References:
     the "
    (xdoc::ahref "https://rustc-dev-guide.rust-lang.org/mir/index.html"
                 "rustc dev guide's MIR chapters")
    ", the @('rustc_middle::mir') and @('rustc_middle::ty') "
    (xdoc::ahref
     "https://github.com/rust-lang/rust/tree/1.87.0/compiler/rustc_middle"
     "sources")
    " (pinned per the plan's D6), and "
    (xdoc::ahref "https://github.com/minirust/minirust" "MiniRust")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum int-type
  :short "Fixtype of signed integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('IntTy')."))
  (:isize ())
  (:i8 ())
  (:i16 ())
  (:i32 ())
  (:i64 ())
  (:i128 ())
  :pred int-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum uint-type
  :short "Fixtype of unsigned integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('UintTy')."))
  (:usize ())
  (:u8 ())
  (:u16 ())
  (:u32 ())
  (:u64 ())
  (:u128 ())
  :pred uint-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum float-type
  :short "Fixtype of floating-point types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('FloatTy'),
     restricted to the two stable-and-fully-supported types
     (@('f16') and @('f128') are not yet stable)."))
  (:f32 ())
  (:f64 ())
  :pred float-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mutability
  :short "Fixtype of mutability markers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('Mutability')
     (@(':not') is shared/immutable, @(':mut') is unique/mutable),
     used in reference and raw pointer types
     and in borrow rvalues."))
  (:not ())
  (:mut ())
  :pred mutabilityp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes tys
  :short "Fixtypes of (monomorphic) MIR types."

  (fty::deftagsum ty
    :short "Fixtype of monomorphic types."
    :long
    (xdoc::topstring
     (xdoc::p
      "Mirrors the cases of rustc's @('TyKind')
       that can occur in the monomorphic core:
       primitives, tuples, arrays, references, raw pointers,
       algebraic data types (structs and enums),
       and function items.")
     (xdoc::p
      "An ADT type refers, by name, to
       a definition in the program's ADT table
       (see the abstract syntax book);
       since the core is monomorphic, there are no generic arguments.
       A function item type (rustc's @('TyKind::FnDef')) is
       the zero-sized type of a named function;
       it is how call terminators refer to their callees.
       References and raw pointers carry no region:
       regions are erased in the MIR that we execute.")
     (xdoc::p
      "The unit type is the empty tuple, as in Rust.
       Slices, @('str'), closures, trait objects, and function pointers
       will be added as the subset ladder climbs."))
    (:bool ())
    (:char ())
    (:int ((type int-type)))
    (:uint ((type uint-type)))
    (:float ((type float-type)))
    (:tuple ((types ty-list)))
    (:array ((elem ty)
             (len acl2::nat)))
    (:ref ((mut mutability)
           (ty ty)))
    (:raw-ptr ((mut mutability)
               (ty ty)))
    (:adt ((name acl2::string)))
    (:fn-def ((name acl2::string)))
    :pred ty-p
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist ty-list
    :short "Fixtype of lists of types."
    :elt-type ty
    :true-listp t
    :elementp-of-nil nil
    :pred ty-listp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ty
  :short "A type witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type ty-p
  :body (ty-bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod variant
  :short "Fixtype of ADT variant definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variant has a name and a list of field types.
     A struct is an ADT with a single variant;
     fields of tuple structs and tuple variants are
     positional (their names are the indices as decimal strings
     in rustc, but only positions matter here)."))
  ((name acl2::string)
   (fields ty-list))
  :pred variantp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist variant-list
  :short "Fixtype of lists of ADT variant definitions."
  :elt-type variant
  :true-listp t
  :elementp-of-nil nil
  :pred variant-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod adt-def
  :short "Fixtype of ADT definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "An algebraic data type definition:
     a struct (one variant) or an enum (any number of variants).
     Unions will be added with the unsafe subset.
     The name is repeated here from the ADT table key
     for convenience and error messages."))
  ((name acl2::string)
   (variants variant-list))
  :pred adt-defp)
