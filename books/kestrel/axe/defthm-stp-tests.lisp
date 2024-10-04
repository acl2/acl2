; Tests of defthm-stp
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

; cert_param: (uses-stp)

(include-book "defthm-stp")
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; A simple test that uses STP to prove that bvplus is commutative (on 32-bit values).
(deftest
  (defthm-stp test1 (equal (bvplus 32 x y) (bvplus 32 y x))))

;; A simple test that is not true:
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test of :rule-classes nil
(deftest
  (defthm-stp test2 (equal (bvplus 32 x y) (bvplus 32 x y)) :rule-classes nil))

;; test :counterexample
(must-fail (defthm-stp test3 (equal (bvplus 32 x y) (bvplus 32 x z)) :counterexample t))

; "Dropping a disjunct that is a (possibly negated) variable: X."
; "Note: No disjuncts. Not calling STP."
(must-fail (defthm-stp test3 x :counterexample t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some tests with BVSX:
(deftest
  (defthm-stp bvsx-32-16-def
    (implies (unsigned-byte-p 64 x)
             (equal (bvsx 32 16 x)
                    (bvif 32 (equal 1 (getbit 15 x))
                          (bvcat 16 65535 16 (bvsx 32 16 x))
                          (bvsx 32 16 x))))
    :rule-classes nil))

(must-fail
  (defthm-stp bvsx-32-16-def-bad
    (implies (unsigned-byte-p 64 x)
             (equal (bvsx 32 16 x)
                    (bvif 32 (equal 1 (getbit 15 x))
                          (bvcat 16 65534 ; note this: should be 65535
                                 16 (bvsx 32 16 x))
                          (bvsx 32 16 x))))
    :rule-classes nil))

(must-fail (defthm-stp bvsx-bad
             (implies (unsigned-byte-p 64 x)
                      (equal (bvsx 32 16 x) (bvsx 32 16 y)))
             :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some array tests:

(defthm-stp array0
  (equal (bv-array-write 8 100 7 val1 (bv-array-write 8 100 4 val2 data))
         (bv-array-write 8 100 4 val2 (bv-array-write 8 100 7 val1 data))))

(defthm-stp array1a
  (equal (bv-array-read 8 16 index (bv-array-write 8 16 index val data))
         (bvchop 8 val))
  :print t)

(defthm-stp array1b
  (implies (unsigned-byte-p 8 val)
           (equal (bv-array-read 8 16 index (bv-array-write 8 16 index val data))
                  val))
  :print t)

(must-fail
  ;; don't know the type of val
  (defthm-stp array1c
    (equal (bv-array-read 8 16 index (bv-array-write 8 16 index val data))
           val)
    :print t))

;; arrays lengths not equal
;; todo: improve the error message
;; todo: add an option to print the inferred types
(must-fail
  (defthm-stp array2
    (equal (bv-array-write 8 100 7 val1 (bv-array-write 8 100 4 val2 data))
           (bv-array-write 9 100 4 val2 (bv-array-write 9 100 7 val1 data)))
    :print t
    ))

;; ;; The arrays can't be equal because they have different lengths.  However, this seems to fail
;; ;; because the types are wrong.
;; (must-fail
;;   (defthm-stp array3
;;     (not (equal (bv-array-write 8 16 index1 val1 array1)
;;                 (bv-array-write 8 17 index2 val2 array2)))
;;     :print t))

;; ;; TODO: Sould this pass?  The array equality gets cut out, but in fact we know it is false.
;; ;; This depends on knowing that the arrays can't be equal because they have different lengths.
;; (must-fail
;;   (defthm-stp array4
;;     (equal (bvif 8 (equal (bv-array-write 8 16 index1 val1 array1)
;;                           (bv-array-write 8 17 index2 val2 array2))
;;                  2
;;                  3)
;;            3)
;;     :print t))

;; Should cut out (bar x) and (foo (bar x)).
(defstub foo (x) t)
(defstub bar (x) t)

;; (foo x) gets replaced by a fresh BV variable of width 8
(defthm-stp cutting-test1
    (equal (bvplus 8 (foo x) y)
           (bvplus 8 y (foo x)))
    :print t)

;; fails but does call STP (todo: how to check that? see prove-with-stp-tester):
(must-fail
  (defthm-stp cutting-test2
    (equal (bvplus 8 (foo (bar x)) y)
           (bvplus 8 (bar x) y))
    :print t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (foo s) is used in a type-inconsistent way:
(must-fail
  (defthm-stp type-test1
    (booland (foo x)
             (bvplus 8 (foo x) y))
    :print t))

;; type error: booland called on a BV
(must-fail
  (defthm-stp type-test2
    (booland (bvplus 8 x y)
             z)
    :print t))

;; This work because the whole BVPLUS node gets cut out due to the bad argument.  A warning is printed.
(defthm-stp type-test3
  (equal (bvplus 8 x 'foo)
         (bvplus 8 x 'foo))
  :rule-classes nil
  :print t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some tests of booleans:

(must-fail (defthm-stp booland-1 (booland x y)))
(defthm-stp booland-2 (equal (booland x y) (booland y x)))
(defthm-stp booland-3 (not (booland x (not x))))

(must-fail (defthm-stp boolor-1 (boolor x y)))
(defthm-stp boolor-2 (equal (boolor x y) (boolor y x)))
(defthm-stp boolor-3 (boolor x (not x)))
