; Tests of the DAG machinery
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

;; Note that currently this tests fairly sophisticated utils that depend on
;; skip-proofs, whereas it may be better in general to use simpler dag utlis.

(include-book "kestrel/axe/dagify" :dir :system) ;for dagify-term!, brings in skip-proofs
(include-book "kestrel/axe/dag-to-term-with-lets" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(deftest
  (assert-equal (dagify-term! '(binary-+ (binary-* '2 x) (binary-* '2 y)))
                '((4 BINARY-+ 1 3)
                  (3 BINARY-* '2 2)
                  (2 . Y)
                  (1 BINARY-* '2 0)
                  (0 . X)))

  ;; Example of how to embed a DAG into a defun (using the axe evaluator).  Here
  ;; we use an embedded dag to compute 2x+2y.
  (defun foo (a b)
    (dag-val-with-axe-evaluator
     '((4 binary-+ 1 3)
       (3 binary-* '2 2)
       (2 . y)
       (1 binary-* '2 0)
       (0 . x))
     (acons 'x a (acons 'y b nil))
     nil ;no interpreted functions
     0))

  (assert-equal (foo 100 7) 214) ;it works!
  )


(deftest
  ;; a variant with an unknown function "bar"
  (defun foo2 (a b)
    (dag-val-with-axe-evaluator
     '((4 bar 1 3)
       (3 binary-* '2 2)
       (2 . y)
       (1 binary-* '2 0)
       (0 . x))
     (acons 'x a (acons 'y b nil))
     nil
     0))

  ;; must fail beause we can't evaluate bar
  (must-fail-with-hard-error (foo2 100 7)) ;todo: this is an abuse of must-fail-with-hard-error because the form does not return an error triple

;must fail because bar is not yet defined
  (must-fail-with-hard-error (make-interpreted-function-alist '(bar) (w state))) ;todo: this is an abuse of must-fail-with-hard-error because the form does not return an error triple
  )

(deftest
  ;;now we define bar
  (defun bar (x y) (+ x y))

  ;; Here we show an interpreted-function-alist that contains a definition for bar:
  (assert-equal (make-interpreted-function-alist '(bar) (w state))
                '((bar (x y) (binary-+ x y))))

  ;; This variant of foo calls bar, but that is okay because we pass in bar's
  ;; definition in the interpreted-function-alist.
  (defun foo3 (a b)
    (dag-val-with-axe-evaluator
     '((4 bar 1 3)
       (3 binary-* '2 2)
       (2 . y)
       (1 binary-* '2 0)
       (0 . x))
     (acons 'x a (acons 'y b nil))
     '((BAR (X Y) (BINARY-+ X Y)))
     0))

  (assert-equal (foo3 100 7) 214) ;it works!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (assert-equal (dagify-term! '(foo3 '3 x)) ;todo: what should happen with the interpreted-function-alist here?
                '((1 FOO3 '3 0)
                  (0 . X)))

  (assert-equal (make-interpreted-function-alist '(foo3) (w state))
                '((FOO3 (A B)
                        (DAG-VAL-WITH-AXE-EVALUATOR '((4 BAR 1 3)
                                                      (3 BINARY-* '2 2)
                                                      (2 . Y)
                                                      (1 BINARY-* '2 0)
                                                      (0 . X))
                                                    (ACONS 'X A (ACONS 'Y B 'NIL))
                                                    '((BAR (X Y) (BINARY-+ X Y)))
                                                    '0))))

  ;; here we have an interpreted-function-alist that contains a function with a
  ;; dag with a different interpreted-function-alist.
  (defun foo-of-3 (a)
    (dag-val-with-axe-evaluator
     '((1 FOO3 '3 0)
       (0 . X))
     (acons 'x a nil)
     '((FOO3 (A B)
             (DAG-VAL-WITH-AXE-EVALUATOR '((4 BAR 1 3)
                                           (3 BINARY-* '2 2)
                                           (2 . Y)
                                           (1 BINARY-* '2 0)
                                           (0 . X))
                                         (ACONS 'X A (ACONS 'Y B 'NIL))
                                         '((BAR (X Y) (BINARY-+ X Y)))
                                         '0 ;this gets replaced with one more than the array-depth we give in the outer call
                                         )))
     0 ; this value gets used and gets incremented for inner calls to DAG-VAL-WITH-AXE-EVALUATOR, causing the array-depth for inner calls to be ignored.
     ))

  (assert-equal (FOO-OF-3 100) 206) ;it works!
  )

(skip-proofs (make-flag apply-axe-evaluator)) ;todo termination

(in-theory (disable lookup-eq-safe use-all-<-for-car pseudo-dag-arrayp-list all-<-of-alen1-when-pseudo-dag-arrayp-list nat-listp quotep
                    ;CONSP-FROM-LEN-CHEAP
                    DEFAULT-CDR
                    DEFAULT-CAR
                    BVCHOP-WITH-N-NEGATIVE
                    BVCHOP-WITH-N-NEGATIVE
                    NOT-<-OF-CAR-WHEN-ALL-<
                    ;;USE-ALL-CONSP-FOR-CAR
                    ;;ALL-CONSP-WHEN-NOT-CONSP
                    ))

;(in-theory (enable CONSP-OF-CDR))

;; ;; todo: prove that the array-depth does not affect the answer:
;; (defthm-flag-APPLY-AXE-EVALUATOR
;;   (defthmd theorem-for-apply-axe-evaluator
;;     (equal (apply-axe-evaluator fn args interpreted-function-alist array-depth)
;;            (apply-axe-evaluator fn args interpreted-function-alist array-depth2))
;;     :flag apply-axe-evaluator)
;;   (defthmd theorem-for-eval-axe-evaluator
;;     (equal (eval-axe-evaluator alist form interpreted-function-alist array-depth)
;;            (eval-axe-evaluator alist form interpreted-function-alist array-depth2))
;;     :flag eval-axe-evaluator)
;;   (defthmd theorem-for-eval-list-axe-evaluator
;;     (equal (eval-list-axe-evaluator alist form-lst interpreted-function-alist array-depth)
;;            (eval-list-axe-evaluator alist form-lst interpreted-function-alist array-depth2))
;;     :flag eval-list-axe-evaluator)
;;   (defthmd theorem-for-dag-val-with-axe-evaluator
;;     (equal (dag-val-with-axe-evaluator dag alist interpreted-function-alist array-depth)
;;            (dag-val-with-axe-evaluator dag alist interpreted-function-alist array-depth2))
;;     :flag dag-val-with-axe-evaluator)
;;   (defthmd theorem-for-eval-dag-with-axe-evaluator
;;     (equal (eval-dag-with-axe-evaluator nodenum-worklist dag-array-name dag-array var-value-alist eval-array-name eval-array interpreted-function-alist array-depth)
;;            (eval-dag-with-axe-evaluator nodenum-worklist dag-array-name dag-array var-value-alist eval-array-name eval-array interpreted-function-alist array-depth2))
;;     :flag eval-dag-with-axe-evaluator)
;;   :hints (("Goal" :expand ((:free (fn) (APPLY-AXE-EVALUATOR FN ARGS INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH))
;;                            (:free (fn) (APPLY-AXE-EVALUATOR FN ARGS INTERPRETED-FUNCTION-ALIST array-depth2))
;;                            (DAG-VAL-WITH-AXE-EVALUATOR DAG ALIST INTERPRETED-FUNCTION-ALIST array-depth2))))

;;   )

(assert-equal
 (dag-to-term-with-lets
  '((4 bar 3)
    (3 binary-* 2 2)
    (2 binary-+ 0 1)
    (1 . y)
    (0 . x)))
 ;; node 2 appears twice and so gets let-bound
 '(BAR (LET* ((VAR-FOR-LET2 (BINARY-+ X Y)))
             (BINARY-* VAR-FOR-LET2 VAR-FOR-LET2))))

;(make-term-into-dag-array 'x 'dag-array-name 'dag-parent-array-name nil)
;(make-term-into-dag-array '(foo '3 x) 'dag-array-name 'dag-parent-array-name nil)
