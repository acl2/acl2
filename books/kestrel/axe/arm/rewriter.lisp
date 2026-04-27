; An Axe Rewriter for ARM lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../make-rewriter-simple")
(include-book "evaluator")
(include-book "syntaxp-evaluator")
(include-book "../axe-syntaxp-evaluator-basic") ;; (include-book "syntaxp-evaluator-arm")
(include-book "../axe-bind-free-evaluator-basic") ;; (include-book "bind-free-evaluator-arm")

;; (local (in-theory (disable ;; these break the proofs below:
;;                            acl2::nth-when-zp ; loops with ACL2::CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS
;;                            reverse-removal ; introduces REV (not our normal form)
;;                            ;; for speed:
;;                            acl2::len-when-atom
;;                            acl2::|(< 0 (len x))|
;;                            assoc-keyword ; why are these arising?
;;                            (:t assoc-keyword)
;;                            keyword-value-listp
;;                            member-of-cons)))

;; To speed up the proofs below:
(local (in-theory (disable ;; acl2::natp-of-car-when-nat-listp-type
                           ;; bigmem::nth-pgp
                           ;; acl2::true-listp-of-car-when-true-list-listp
                           ;; acl2::acl2-numberp-of-car-when-acl2-number-listp ; via fty
                           ;; ;; (:executable-counterpart tau-system) ; todo
                           )))

;; Create the "arm" rewriter.  Here, "arm" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-dag-arm, simplify-term-arm, simplify-term-to-term-arm, simplify-terms-to-terms-arm,
;; and def-simplified-arm.
(make-rewriter-simple arm
                      axe-evaluator-arm
                      arm
                      basic ; arm
                      :smt t ; do use SMT
                      )
