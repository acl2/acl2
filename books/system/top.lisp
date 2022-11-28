; Copyright (C) 2014, Regents of the University of Texas
; Written (originally) by Matt Kaufmann (original date April, 2010)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; WARNING (as of 10/23/2022): This book is included in community book
; std/system/top.lisp, which in turn is included in community book
; std/top.lisp, which in turn is included in several community books.  So
; consider the consequences for community book certification if you extend or
; shrink the set of books included below.  A list of books in this directory
; that are not included after including those below (by evaluating (strip-cdrs
; (strip-cars (global-val 'include-book-alist (w state)))), hence either
; directly or as subsidiary books), each with a brief summary, may be found in
; a long comment below the include-book forms that follow.

; See also devel-check.lisp, which includes only the books that are intended to
; support the devel-check target of ../../GNUmakefile.  (Those books are
; largely the ones below as of 10/23/2022, which is when devel-check.lisp
; stopped including top.lisp.)

(in-package "ACL2")

(include-book "hl-addr-combine")
(include-book "extend-pathname")
(include-book "verified-termination-and-guards")
(include-book "sublis-var")
(include-book "subcor-var")
(include-book "subst-expr")
(include-book "subst-var")
(include-book "convert-normalized-term-to-pairs")
(include-book "meta-extract")
(include-book "legal-variablep")
(include-book "merge-sort-term-order")
(include-book "termp")
(include-book "kestrel")
(include-book "remove-guard-holders")
(include-book "merge-sort-symbol-lt")
(include-book "pseudo-good-worldp")
(include-book "bind-macro-args")
(include-book "case-match")
(include-book "fmx-cw")
(include-book "all-fnnames")
(include-book "observation1-cw")
(include-book "defstobj")

; Below are the books not included by includeing all of the above (at least, as
; of 10/23/2022).  See the warning near the top of this file before including
; any of these.

; A random package:
; acl2-system-exports.lisp

; Example referenced in source comments:
; bigger-limits.lisp

; This book "shows that the cantor pairing function, hl-nat-combine, is
; bijective."
; cantor-pairing-bijective.lisp

; This books runs (add-guards-as-assertions-all), which checks top-level calls
; of built-in functions that are in :logic mode, guard-verified.
; check-system-guards.lisp

; "A Utility for Comparing the .out Files Produced during Book Certification":
; compare-out-files.lisp

; A tool to find dead code:
; dead-source-code.lisp

; Silly file to trick cert.pl into including the right books.
; deps-pcert.lisp

; This book supports ../../GNUmakefile target devel-check and includes many
; of the books included by the present book.
; devel-check.lisp

; Tools to return lists of event names matching a given prefix:
; event-names.lisp

; Proof that f-put-global preserves state-p1:
; f-put-global.lisp

; Tests of fancy string reader:
; fancy-string-reader-test.lisp

; Proof that "demonstrates that hl-nat-combine is onto the naturals":
; hl-nat-combine-onto.lisp

; Proof that obviously-equiv-terms are suitably equal or Boolean equivalent
; obviously-equiv-terms.lisp

; Checks pertaining to inlining and stack overflows:
; optimize-check-aux.lisp
; optimize-check.lisp

; "Returns a summary of where a @(see logical-name) originates from":
; origin.lisp

; Some lemmas about pseudo-termp
; pseudo-termp-lemmas.lisp

; Tool for generating a list of random numbers in [0, limit)
; random.lisp

; Locally included in remove-guard-holders.lisp
; remove-guard-holders-lemmas.lisp

; Termination and guard proofs now included in sources, saved
; in this book for historical reasons:
; too-many-ifs.lisp

; Dependency scanner help for toothbrush:
; toothbrush-deps.lisp

; Proof of the Correctness of CADR Centric Untranslation:
; untranslate-car-cdr.lisp

; Some lemmas about updating state:
; update-state.lisp

; Checks world invariants:
; worldp-check.lisp
