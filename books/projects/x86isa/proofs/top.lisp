;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

;; Proof utilities
(include-book "utilities/programmer-level-memory-utils" :ttags :all)
(include-book "utilities/physical-memory-utils" :ttags :all)
(include-book "utilities/system-level-memory-utils" :ttags :all)
(include-book "utilities/paging-utils" :ttags :all)
(include-book "utilities/environment-utils" :ttags :all)

;; Program proofs:

(defsection code-proofs
  :parents (X86ISA)
  :short "Verification of various x86 programs"
  :long "<p>Detailed documentation topic coming soon!</p>

<p>The factorial program has been proved correct using two
methods:</p>

<ol>
<li>Inductive Assertions: See book @('factorial/fact-inductive-assertions.lisp').</li>
<li>Wormhole Abstraction: See book @('factorial/fact-wormhole-abstraction.lisp').</li>
</ol>
"

;; [Shilpi]: There are name clashes in these two factorial books.  The
;; empty encapsulates below avoid this name clash problem while
;; ensuring that the books get built as a part of the
;; regression. Another way to ensure that these books get built is to
;; rely on cert.pl's dependency scanner and put these include-books in
;; a multi-line comment or something.

(local
 (encapsulate
  ()
  (local (include-book "factorial/fact-inductive-assertions" :ttags :all))))

(local
 (encapsulate
  ()
  (local (include-book "factorial/fact-wormhole-abstraction" :ttags :all))))

  )

;; ======================================================================
