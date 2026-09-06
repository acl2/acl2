; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "types")
(include-book "abstract-syntax")
(include-book "limits")
(include-book "values")
(include-book "states")
(include-book "interp")

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
     rustc-shaped syntax keeps the importer a near-transliteration,
     while MiniRust supplies a rigorous semantic style.")
   (xdoc::p
    "MIR is not a single language:
     rustc reshapes it through three dialects as compilation proceeds
     (built, analysis, and runtime MIR, in its phase vocabulary),
     which differ in which constructs may appear
     and in what some constructs mean.
     We model <i>runtime MIR before any optimization passes</i>:
     the body returned by rustc's
     @('mir_drops_elaborated_and_const_checked') query,
     in which drops have been elaborated and made unconditional,
     the constructs that exist only for borrow checking are gone,
     and overflow checks are materialized as
     explicit checked operations and assertions.
     On drop-free code this dialect coincides with
     the analysis MIR of the earlier @('mir_promoted') query
     minus its borrowck-only statements,
     so the formalization also serves
     extraction pipelines that read that query;
     see @(see mir-abstract-syntax) for the precise phase pin.
     The dialect distinctions are confined to that code vocabulary
     of statements, terminators, and rvalues;
     rustc has a single type system shared by all MIR dialects,
     so the type fixtypes (@(tsee ty) and its components)
     apply to any dialect unchanged,
     up to the monomorphic, region-erased form described next.")
   (xdoc::p
    "This is a draft covering the monomorphic core &mdash;
     the shape of post-monomorphization code:
     there are no type parameters, no regions/lifetimes
     (MIR for execution has them erased),
     and, because we model the @('panic=abort') compilation mode,
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
    " (pinned at rustc 1.87.0), and "
    (xdoc::ahref "https://github.com/minirust/minirust" "MiniRust")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc mir-tests
  :parents (mir)
  :short "Tests of the MIR abstract syntax and interpreter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The MIR formalization is exercised by test books under
     @('mir/tests/').  These are run by the ACL2 regression
     (@('make regression') in @('books/')); they are deliberately
     not included by @('mir/top'), so building the library does not
     require running them or fetching their inputs.")
   (xdoc::ul
    (xdoc::li
     "@('aes-fixslice-program'): a large committed constant holding a
      real AES-128 crate imported to MIR (see @(see mir-import)),
      used as a fixture so the interpreter tests need neither the
      importer nor its input at build time.")
    (xdoc::li
     "@('aes-fixslice'): runs that program's @('encrypt') and
      @('decrypt') on the interpreter, checking the FIPS-197
      known-answer vectors and, differentially, against the ACL2
      AES-128 specification."))))
