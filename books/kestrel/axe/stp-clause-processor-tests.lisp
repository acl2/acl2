; Tests of the STP clause processor
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

; cert_param: (uses-stp)

; Matt K. mod: Avoid ACL2(p) with waterfall-parallelism, "Clause-processors
; that return one or more stobjs are not officially supported when waterfall
; parallelism is enabled."
(set-waterfall-parallelism nil)

(include-book "stp-clause-processor")
(include-book "std/testing/must-fail" :dir :system)
;(include-book "std/testing/must-fail-with-hard-error" :dir :system)

;full syntax for the :clause-processor hint:
(defthm stp-clause-processor-test-0
  (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
  :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
           :clause-processor (stp-clause-processor clause nil state))))

;short syntax for the :clause-processor hint:
(defthm stp-clause-processor-test-0b
  (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
  :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
           :clause-processor stp-clause-processor)))

;; (defthm mytest
;;   (not (not (equal (bvplus 33 x y) (bvplus 32 z x))))
;;   :hints (("Goal" :in-theory nil :clause-processor (stp-clause-processor clause nil state))))


;; todo: get this to work:
;; (defthm mytest
;;   (implies (equal 0 x) (equal (bvplus 32 x 0) 0))
;;   :hints (("Goal" :clause-processor (stp-clause-processor clause '((:must-prove . t)) state))))

;; Proof should fail but no hard error:
(must-fail
  (defthm stp-clause-processor-fail-1
    (not (not (equal (bvplus 32 x y) (bvplus 32 x z))))
    :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
             :clause-processor (stp-clause-processor clause nil state)))))

;; Should fail with a hard error since :must-prove is given:
(must-fail ; this did not work, perhaps the hard error is caught: must-fail-with-hard-error
  (defthm stp-clause-processor-fail-1
    (not (not (equal (bvplus 32 x y) (bvplus 32 x z))))
    :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
             :clause-processor (stp-clause-processor clause '((:must-prove . t)) state)))))

;; Test the :print option:
(defthm stp-clause-processor-test-3
  (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
           :clause-processor (stp-clause-processor clause '((:print . t)) state))))

;; Test the :max-conflicts option:
(defthm stp-clause-processor-test-4
  (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
  :rule-classes nil
  :hints (("Goal" :in-theory nil ; ensure the clause-processor does the work
           :clause-processor (stp-clause-processor clause '((:max-conflicts . 100)) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm-with-stp-clause-processor mytest (not (not (equal (bvplus 32 x y) (bvplus 33 y x)))))

(defthm-with-stp-clause-processor defthm-with-stp-clause-processor-test-1
  (equal (bvplus 32 x y)
         (bvplus 32 y x)))

;; Test :print
(defthm-with-stp-clause-processor defthm-with-stp-clause-processor-test-1b
  (equal (bvplus 32 x y)
         (bvplus 32 y x))
  :print t)

; Same as above but with double negation added
(defthm-with-stp-clause-processor defthm-with-stp-clause-processor-test-2
  (not (not (equal (bvplus 32 x y)
                   (bvplus 32 y x)))))

;; Test :rule-classes
(defthm-with-stp-clause-processor defthm-with-stp-clause-processor-test-3
  (equal (bvplus 32 x y)
         (bvplus 32 x y))
  :rule-classes nil)

;; TODO: Test other options
