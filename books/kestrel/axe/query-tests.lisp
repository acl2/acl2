; Tests of the query tool defined in query.lisp.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more tests.

;; I am not sure sure if STP will always give back the same counterexample on a
;; given (invalid) problem.  If it doesn't, we may need to relax some of the
;; checking done in these tests.

(include-book "query")
(include-book "kestrel/axe/rules-in-rule-lists" :dir :system) ;for equal-same, etc

;; Test assert-equal-with-stobjs:
(assert-equal-with-stobjs (query (equal (bvplus 8 1 x) 3))
                          :sat
                          :stobjs (state))


;; TODO: For tests with a unique solution, that that value is returned:

;; Is there an X such that x+1 is 3?  Yes: 2.  This test is mentioned in the
;; documentation.
(assert-query-result (query (equal (bvplus 8 1 x) 3))
                     :sat)

;; Is there an X such that X*X is 25? Yes: 5.
(assert-query-result (query (equal (bvmult 8 x x) 25))
                     :sat)

;; Is there anything which gives 17 when doubled?  No.
(assert-query-result (query (equal (bvmult 8 2 x) 17))
                     :unsat)

;; The counterexample "(BINARY-+ '1 X) is 4" is not in fact spurious, but the
;; tool can't tell that (it doesn't know about +, only bvplus), so we get
;; :unknown.
(assert-query-result (query (equal (bvplus 8 1 (+ 1 x)) 5))
                     :unknown)

;; In this query, the solver doesn't generate a value for Y (because it is
;; irrelevant to the validity of the SMT problem -- it can be cancelled from
;; both sides), so our tool fills in 0 for Y in the returned counterexample.
(assert-query-result (query (equal (bvplus 32 x y) (bvplus 32 y z)))
                     :sat)

;; Is there an X that is equal to itself?  Yes, in fact, that's true for every
;;X, so we return :valid (which is somewhat unusual).
(assert-query-result (query (equal x x) :rules '(equal-same))
                     :valid)

;; This returns :unknown, because the tool doesn't know the type of X and Y:
(assert-query-result (query (equal x y))
                     :unknown)

;; This returns :unknown, because the tool doesn't know the type of X and Y:
(assert-query-result (query (not (equal x y)))
                     :unknown)

;; This test is mentioned in the documentation.
(assert-query-result (query (equal (bvplus 8 1 x) (bvplus 8 2 x)))
                     :unsat)





;; TODO: Should this work?: (query x)

;; TODO: Get this working:
;; (assert-query-result (query (and (unsigned-byte-p 8 x)
;;                                  (unsigned-byte-p 8 y)
;;                                  (equal x y))
;;                             :rules (append '(not-of-if
;;                                              if-becomes-myif
;;                                              not-of-myif
;;                                              myif-becomes-boolif)
;;                                            (booleanp-rules))
;;                             )
;;                      (:sat ...))

;; ;; TODO: Get this working:
;; (assert-query-result (query (and (unsigned-byte-p 8 x)
;;                                  (unsigned-byte-p 8 y)
;;                                  (not (equal x y))))
;;                      ...)

;; TODO: Try a pigeonhole test


;; TODO: Make these into tests:
;; (query t)
;; (query nil)
;; (query (implies nil x))
;; (query (implies x nil))
