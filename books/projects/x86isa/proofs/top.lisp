;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

;; Proof utilities
(include-book "utilities/programmer-level-mode/programmer-level-memory-utils" :ttags :all)
(include-book "utilities/programmer-level-mode/environment-utils" :ttags :all)
(include-book "utilities/system-level-mode/physical-memory-utils" :ttags :all)
(include-book "utilities/system-level-mode/paging-lib/paging-top" :ttags :all)
(include-book "utilities/system-level-mode/system-level-memory-utils" :ttags :all)

;; Program proofs:

(defsection code-proofs
  :parents (X86ISA)
  :short "Verification of various x86 programs"
  :long "<p>Detailed documentation topic coming soon!</p>

<p>The <b>factorial program</b> has been proved correct using two methods:</p>

<ol>
<li>Inductive Assertions: See book @('factorial/fact-inductive-assertions.lisp').</li>
<li>Wormhole Abstraction: See book @('factorial/fact-wormhole-abstraction.lisp').</li>
</ol>

<p>The proof of correctness of the <b>word-count program</b> can be found in
@('word-count/wc.lisp').</p>

<p>The proof of correctness of a simple <b>array copy sub-routine</b> can be
found in @('dataCopy/dataCopy.lisp').</p>

<p>The proof of correctness of a <b>population count program</b> can
be found in @('popcount/popcount.lisp'). This proof was done using the
@(see GL::GL) symbolic simulation framework.</p>

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

  (local
   (encapsulate
    ()
    (local (include-book "popcount/popcount" :ttags :all))))

  (local
   (encapsulate
    ()
    (local (include-book "word-count/wc" :ttags :all))))

  (local
   (encapsulate
    ()
    (local (include-book "dataCopy/dataCopy" :ttags :all))))

  )

;; ======================================================================
