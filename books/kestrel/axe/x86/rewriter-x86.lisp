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

(local (in-theory (disable ;; these break the proofs below:
                           acl2::nth-when-zp ; loops with ACL2::CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS
                           reverse-removal ; introduces REV (not our normal form)
                           ;; for speed:
                           acl2::len-when-atom
                           acl2::|(< 0 (len x))|
                           assoc-keyword ; why are these arising?
                           (:t assoc-keyword)
                           KEYWORD-VALUE-LISTP
                           )))

;; these slow down the proofs below:
(local (in-theory (disable x86isa::unsigned-byte-p-when-sib-p
                           bigmem::nth-pgp
                           acl2::true-listp-of-car-when-true-list-listp
                           x86isa::member-p-pos-value ; hung in part on len (seems bad)
                           x86isa::n08p-element-of-byte-listp
                           X86ISA::UNSIGNED-BYTE-P-WHEN-MODR/M-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE2-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-VEX3-BYTE1-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-VEX2-BYTE1-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE3-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE2-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-BYTE1-P
                           X86ISA::UNSIGNED-BYTE-P-WHEN-8BITS-P
                           ACL2::ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP
                           ;; (:EXECUTABLE-COUNTERPART TAU-SYSTEM) ; todo
                           )))

;; Create the "x86" rewriter.  Here, "x86" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-term-x86, simp-term-x86, simp-terms-x86, simplify-dag-x86,
;; and def-simplified-dag-x86.
(make-rewriter-simple x86
                      axe-evaluator-x86
                      x86
                      x86)
