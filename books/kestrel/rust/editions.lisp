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
(include-book "std/util/defirrelevant" :dir :system)
(include-book "std/util/defval" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ editions
  :parents (rust)
  :short "Rust editions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rust evolves without breaking old code by way of editions.
     An edition is a named dialect of the language,
     chosen per crate (in @('Cargo.toml') or via @('--edition')),
     that gates a small set of surface-level differences:
     which identifiers are keywords,
     certain lexical reservations,
     some parsing and pattern-matching rules,
     and a few desugaring and scoping rules.
     Crates of different editions link together freely,
     because editions do not change the compiled representation.")
   (xdoc::p
    "We support the 2021 and 2024 editions, with 2024 as the default.
     The differences between these two editions that affect this library
     include:
     the reservation of @('gen') as a keyword in 2024;
     the lexical reservation of guarded strings
     (@('#\"...\"#') and @('##')) in 2024;
     the behavior of the @('expr') macro fragment specifier;
     restrictions on match ergonomics in patterns;
     @('unsafe extern') blocks and unsafe attributes;
     lifetime capture rules for return-position @('impl Trait');
     and changes to the scopes of some temporaries
     (which affect where values are dropped).
     The editions before 2021 are not supported.")
   (xdoc::p
    "The edition is threaded through the parts of this library
     whose behavior is edition-dependent,
     such as keyword classification in the lexer."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum edition
  :short "Fixtype of editions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model the Rust 2021 and 2024 editions."))
  (:e2021 ())
  (:e2024 ())
  :pred editionp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-edition
  :short "An edition witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a fixed but opaque witness of the @(tsee edition) fixtype,
     for use where a value of the type is needed
     but its identity must not matter:
     to fill the non-error result slots of a function
     that is returning an error,
     and to complete branches that are provably unreachable
     but still need a well-typed value.
     The @(tsee defirrelevant) means that the exact value is irrelevant.")
   (xdoc::p
    "Using this nullary function, which is kept disabled,
     instead of just writing some constructor call inline,
     documents at each use site that the value is arbitrary,
     and keeps proofs honest:
     a proof cannot depend on which edition this is
     unless the definition is deliberately enabled,
     so accidental dependence shows up as a proof failure.")
   (xdoc::p
    "The same convention, following the C library,
     is used for other fixtypes of this library;
     their witnesses (also of irrelevant value) reference this documentation."))
  :type editionp
  :body (edition-e2024))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *default-edition*
  :short "The default edition (Rust 2024)."
  (edition-e2024))
