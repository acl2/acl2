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

;; these break the proofs below:
(local (in-theory (disable acl2::nth-when-zp ; loops with ACL2::CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS
                           reverse-removal ; introduces REV (not our normal form)
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
