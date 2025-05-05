; An Axe Rewriter for x86 lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../make-rewriter-simple")
(include-book "evaluator-x86")
(include-book "syntaxp-evaluator-x86")
(include-book "bind-free-evaluator-x86")

;; Bad rule from x86 model:
(in-theory (disable natp-when-gte-0))

(local (in-theory (disable ;; these break the proofs below:
                           acl2::nth-when-zp ; loops with ACL2::CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS
                           reverse-removal ; introduces REV (not our normal form)
                           ;; for speed:
                           acl2::len-when-atom
                           acl2::|(< 0 (len x))|
                           assoc-keyword ; why are these arising?
                           (:t assoc-keyword)
                           keyword-value-listp
                           member-of-cons)))

;; these slow down the proofs below:
(local (in-theory (disable x86isa::unsigned-byte-p-when-sib-p
                           bigmem::nth-pgp
                           acl2::true-listp-of-car-when-true-list-listp
                           x86isa::member-p-pos-value ; hung in part on len (seems bad)
                           x86isa::n08p-element-of-byte-listp
                           x86isa::unsigned-byte-p-when-modr/m-p
                           x86isa::unsigned-byte-p-when-vex3-byte2-p
                           x86isa::unsigned-byte-p-when-vex3-byte1-p
                           x86isa::unsigned-byte-p-when-vex2-byte1-p
                           x86isa::unsigned-byte-p-when-evex-byte3-p
                           x86isa::unsigned-byte-p-when-evex-byte2-p
                           x86isa::unsigned-byte-p-when-evex-byte1-p
                           x86isa::unsigned-byte-p-when-8bits-p
                           acl2::acl2-numberp-of-car-when-acl2-number-listp
                           ;; (:executable-counterpart tau-system) ; todo
                           )))

;; Create the "x86" rewriter.  Here, "x86" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-dag-x86, simplify-term-x86, simplify-term-to-term-x86, simplify-terms-to-terms-x86,
;; and def-simplified-x86.
(make-rewriter-simple x86
                      axe-evaluator-x86
                      x86
                      x86
                      t ; do use SMT
                      )
