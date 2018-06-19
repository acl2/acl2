;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "utilities/top" :ttags :all)

;; ======================================================================

;; Proofs of correctness of various x86 programs: We exclude these
;; from the x86isa documentation.  There are a lot of name clashes
;; here.  The empty encapsulates below avoid this name clash problem
;; while ensuring that the books get built as a part of the
;; regression.

;; ----------------------------------------------------------------------
;; Application Programs:

;; The factorial program has been proved correct using two methods:
;; inductive assertions and wormhole abstraction.
(local
 (encapsulate
   ()
   (local (include-book "factorial/fact-inductive-assertions" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "factorial/fact-wormhole-abstraction" :ttags :all))))

;; A pretty simple proof of correctness of an application program that
;; determines whether a given input is a power of 2 or not.
(local
 (encapsulate
   ()
   (local (include-book "powOfTwo/powOfTwo" :ttags :all))))

;; The proof of correctness of a population count program was done
;; using the GL bit-blasting framework.
(local
 (encapsulate
   ()
   (local (include-book "popcount/popcount" :ttags :all))))

;; Same popcount program as popcount/popcount, but here we use our
;; lemma libraries to perform symbolic simulation.
(local
 (encapsulate
   ()
   (local (include-book "popcount/popcount-general" :ttags :all))))

(local
 (encapsulate
   ()
   (local (include-book "wordCount/wc" :ttags :all))))

;; Proof of correctness of a simple array copy sub-routine:
(local
 (encapsulate
   ()
   (local (include-book "dataCopy/dataCopy" :ttags :all))))

;; ----------------------------------------------------------------------
;; System Program:

;; The zeroCopy program has been proved correct in both the marking
;; and non-marking view of the x86 model.

(local
 (encapsulate
   ()
   (local (include-book "zeroCopy/non-marking-view/zeroCopy" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "zeroCopy/marking-view/zeroCopy" :ttags :all))))

;; ======================================================================

;; x86isa+Codewalker:

(local
 (encapsulate
   ()
   (local (include-book "codewalker-examples/factorial" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "codewalker-examples/popcount-32" :ttags :all))))

;; ======================================================================

;; The following books present small examples that Shilpi presents in
;; her PhD dissertation to illustrate how symbolic simulation is
;; controlled in all views of operation of the x86 model.

(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-app-view" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-system-level-marking-view" :ttags :all))))
(local
 (encapsulate
   ()
   (local (include-book "dissertation-examples/clc-stc-system-level-non-marking-view" :ttags :all))))

;; ======================================================================
