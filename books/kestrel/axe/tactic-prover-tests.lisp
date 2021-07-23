; Tests of the tactic prover
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

; cert_param: (uses-stp)

(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "tactic-prover")
(include-book "kestrel/axe/rules-in-rule-lists" :dir :system) ;for equal-same, etc

;A simple test
(deftest
  (prove-equivalence2 '(car (cons x 7)) 'x :rules '(car-cons equal-same)))

;; Test a failure:
(deftest
  (must-fail (prove-equivalence2 '(car (cons 7 x)) 'x :rules '(car-cons equal-same))))


;; Test redundancy checking:
(deftest
  (prove-equivalence2 '(car (cons x 7)) 'x :rules '(car-cons equal-same))
  ;; redundant:
  (prove-equivalence2 '(car (cons x 7)) 'x :rules '(car-cons equal-same))
  ;; something non-redundant still fails:
  (must-fail (prove-equivalence2 '(car (cons 7 x)) 'x :rules '(car-cons equal-same))))

;;TODO: Uncomment these after adding rules:

;; (must-fail
;;  (prove-equivalence2 (dagify-term '(bvplus '32 '1 x))
;;                      (dagify-term '(bvplus '32 '2 x))))

;; (deftest
;;   (prove-equivalence2 (dagify-term '(bvplus '32 '7 x))
;;                       (dagify-term '(bvplus '32 x '7))))


;; (must-fail ;the dags have different vars
;;  (prove-equivalence2 (dagify-term '(bvplus '32 x y))
;;                     (dagify-term '(bvplus '32 x z))))

;; ;TODO: Improve the error message here:
;; (must-fail ;the dags have different vars
;;  (prove-equivalence2 (dagify-term '(bvplus '32 x y))
;;                     (dagify-term '(bvmult '32 x y))))

;; ;try with terms instead of dags:
;; (deftest
;;   (prove-equivalence2 '(bvplus '32 '7 x)
;;                       '(bvplus '32 x '7)))

;; ; try with one term and one dag:
;; (deftest
;;   (prove-equivalence2 '(bvplus '32 '7 x)
;;                       (dagify-term '(bvplus '32 x '7))))

(deftest
  (prove-equivalence2 '(bvplus 32 '1 '1) ''2 :rules '(equal-same)))

(deftest
  (must-fail (prove-equivalence2 '(bvplus 32 x y) '(bvmult 32 x y) :rules '(equal-same))))


(deftest
  (must-fail (prove-with-tactics '(< (getbit 1 x) 2) :tactics '((:cases (equal 0 (getbit 1 x)) (equal 1 (getbit 0 x))) :acl2))))

(deftest
  (prove-with-tactics '(< (getbit 1 x) 2) :tactics '((:cases (equal 0 (getbit 1 x)) (equal 1 (getbit 1 x))) :rewrite)))

;; Test of :rule-classes nil (todo: test more rule-classes)
(deftest
  (prove-with-tactics '(equal 0 0) :tactics '(:rewrite) :rule-classes nil))

;;
;; Tests of the :stp tactic:
;;

(deftest
  (prove-with-tactics '(equal (bvplus '32 x y) (bvplus '32 y x)) :tactics '(:stp)))

;; STP finds the counter-example of 0 and 1
(deftest
  (must-fail (prove-with-tactics '(equal (bvplus '32 x y) (bvplus '32 x x)) :tactics '(:stp))))

;; TODO: Add many more tests


;TODO: should fail (elem 1 is not necessarily greater than 8), but the array read in the assumption is getting cut out
;; (deftest
;;   ;;todo: include less?
;;   (include-book "kestrel/axe/axe-rules-mixed" :dir :system)
;;   (include-book "kestrel/axe/axe-rules" :dir :system) ;include less?  but some of these rules are now used during decompilation
;;   (include-book "kestrel/jvm/jvm-rules" :dir :system)
;;   (include-book "kestrel/axe/jvm/jvm-rules-axe" :dir :system)
;;   (include-book "kestrel/axe/math-rules" :dir :system)
;;   (defthmd if-becomes-boolif-axe
;;     (implies (and (axe-syntaxp (and (known-booleanp b dag-array)))
;;;                  (axe-syntaxp (and (known-booleanp c dag-array)))
;;                   (booleanp b)
;;                   (booleanp c))
;;              (equal (if a b c)
;;                     (boolif a b c)))
;;     :hints (("Goal" :in-theory (enable myif boolif))))
;;   (prove-with-tactics '(implies (and (equal '2 (len arr))
;;                                      (all-unsigned-byte-p '32 arr)
;;                                      (true-listp arr)
;;                                      (equal (bv-array-read '32 (len arr) '0 arr) '8)) ;the length here doesn't get rewritten to 2 because this is an assumption
;;                                 (sbvlt '32 (bv-array-read '32 (len arr) '0 arr)
;;                                        (bv-array-read '32 (len arr) '1 arr)))
;;                       :tactics '(:rewrite :stp)
;;                       :print :verbose
;;                       :rules (append '(implies)
;;                                      (booleanp-rules)
;;                                      (amazing-rules))))

;wow!  This proves even with timeout 0 (presumably by rewriting)
(deftest
  (prove-with-tactics '(equal (bvplus '32 x y) (bvplus '32 y x)) :tactics '(:stp) :timeout 0))

(deftest
  (prove-with-tactics '(equal (bvplus '32 x y) (bvplus '32 y x)) :tactics '(:stp) :timeout 100000))

(deftest
  (prove-with-tactics '(equal (bvplus '32 x y) (bvplus '32 y x)) :tactics '(:stp) :timeout nil))

;wow!  This proves even with timeout 0 (presumably by rewriting)
(deftest
  (prove-with-tactics '(equal (bvmult '4 x (bvmult '4 y z)) (bvmult '4 z (bvmult '4 y x))) :tactics '(:stp) :timeout 0))

;; TODO: Add tests where the :timeout arg matters

;; TODO: Test STP-based pruning.

;; test of :simplify-assumptions
(deftest
  (prove-with-tactics '(if (equal x 3) t nil)
                      ;; this has to get simplified to be useful:
                      :assumptions '((car (cons (equal x 3) y)))
                      :simplify-assumptions t
                      :tactics '(:rewrite)
                      :rules '(car-cons)
                      :rule-classes nil ;todo: why?
                      ))

;; Same as above but without :simplify-assumptions, so this fails:
(deftest
  (must-fail (prove-with-tactics '(if (equal x 3) t nil)
                                 ;; this has to get simplified to be useful:
                                 :assumptions '((car (cons (equal x 3) y)))
;                      :simplify-assumptions t
                                 :tactics '(:rewrite)
                                 :rules '(car-cons)
                                 :rule-classes nil ;todo: why?
                                 )))

(deftest
  (prove-with-tactics t :rule-classes nil :tactics '(:stp)))

;; 3 is non-nil (so it is "true"), so this should prove
(deftest
  (prove-with-tactics 3 :rule-classes nil :tactics '(:stp)))

(deftest
  (must-fail (prove-with-tactics nil :rule-classes nil :tactics '(:stp))))
