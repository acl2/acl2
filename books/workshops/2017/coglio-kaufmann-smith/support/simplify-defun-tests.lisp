; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file is based closely on simplify-body-tests.lisp.  Note in particular
; the new section at the end, which explains something about how simplify-defun
; works.

(in-package "ACL2")

(include-book "simplify-defun")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplify-defun tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some errors with patterns.
(deftest
  (defun foo (x) (+ 1 1 x))

  ;; Illegal nesting in pattern
  (must-fail (simplify-defun foo :simplify-body (:@ (+ 1 (:@ (+ 1 x))))))

  ;; Illegal nesting in pattern
  (must-fail (simplify-defun foo :simplify-body (:@ (+ 1 @))))

  ;; No @-vars or calls of :@.
  (must-fail (simplify-defun foo :simplify-body _))
  )

;;simple test of a non-recursive function
(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (simplify-defun foo)
  (must-be-redundant
    (DEFUN FOO{1} (X) (declare (xargs :normalize nil)) (+ 2 X))
    (DEFTHM FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;TODO: The output here gives almost no information if this fails
;;test show-simplify-defun
(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (must-succeed (show-simplify-defun foo))
  (must-succeed (simplify-defun foo :show-only t)))

;;simple example of a recursive function
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify-defun bar)
  (must-be-redundant
    (DEFUND BAR{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :USE (:TERMINATION-THEOREM BAR)))))
      (IF (ZP X) 0 (+ 2 (BAR{1} (+ -1 X)))))
    (DEFTHM BAR-BECOMES-BAR{1}
      (EQUAL (BAR X) (BAR{1} X)))))

;;same as above, but test :theorem-name and :new-name arguments, test
;;that results are suitably disabled, and test print-def nil (well, not
;;much of a test unless we look at the result!).
(deftest
  (defund bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify-defun bar
                  :new-name bar-simp
                  :theorem-name bar-simplified
                  :theorem-disabled t
                  :print-def nil)
  (assert-event (disabledp 'bar-simp)) ;disabled because bar is disabled
  (assert-event (disabledp 'bar-simplified))
  (must-be-redundant
    (DEFUND BAR-SIMP (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :USE (:TERMINATION-THEOREM BAR)))))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;;same as above, but create enabled definitions
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify-defun bar
                  :new-name bar-simp
                  :theorem-name bar-simplified
                  ;; :function-disabled nil ; default of :auto, so unnecessary
                  ;:theorem-disabled nil ; default of nil, so unnecessary
                  )
  (assert-event (not (disabledp 'bar-simp))) ;not disabled because bar is not disabled
  (assert-event (not (disabledp 'bar-simplified)))
  (must-be-redundant
    (DEFUN BAR-SIMP (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :USE (:TERMINATION-THEOREM BAR)))))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;;same as above, but test :function-disabled
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify-defun bar
                  :new-name bar-simp
                  :theorem-name bar-simplified
                  :function-disabled t
                  :theorem-disabled nil)
  (assert-event (disabledp 'bar-simp))
  (assert-event (not (disabledp 'bar-simplified)))
  (must-be-redundant
    (DEFUN BAR-SIMP (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :USE (:TERMINATION-THEOREM BAR)))))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;; Test with :assumptions and a non-recursive function
(deftest
  (defun foo (x)
    (ifix x))
  (simplify-defun foo :assumptions ((integerp x)))
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL :normalize nil))
      X)
    (DEFTHM FOO-BECOMES-FOO{1}
      (IMPLIES (INTEGERP X)
               (EQUAL (FOO X) (FOO{1} X))))))

;; As above, but evaluating assumptions
(deftest
  (defun foo (x)
    (ifix x))
  (simplify-defun foo :assumptions (:eval (list '(integerp x))))
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL :normalize nil))
      X)
    (DEFTHM FOO-BECOMES-FOO{1}
      (IMPLIES (INTEGERP X)
               (EQUAL (FOO X) (FOO{1} X))))))

;move
(defthm integer-listp-of-cdr
  (implies (integer-listp x)
           (integer-listp (cdr x))))

(defthm integerp-of-car
  (implies (and (not (atom x))
                (integer-listp x))
           (INTEGERP (CAR X))))

;; Test with :assumptions and a recursive function
(deftest
  (defun foo (x)
    (if (atom x)
        nil
      (cons (ifix (first x))
            (foo (rest x)))))
  (simplify-defun foo :assumptions ((integer-listp x))
; rules used to simplify the body:
                 :theory '(ifix integerp-of-car)
; rules used to prove that the assumptions still hold on the recursive call:
                 :assumption-theory '(INTEGER-LISTP-of-cdr)
                 )
  (must-be-redundant

;;; OBSOLETE Comment from Matt K. (now that simplify-defun uses
;;; directed-untranslate):

;;; The original version below, commented out, may be prettier; perhaps I
;;; should change simplify-defun to call reconstruct-macros-in-term, as
;;; does the original simplify-body.  However, here is an argument for why it
;;; might be better to avoid that utility.  Suppose we instead define foo as
;;; follows (logically equivalent, for what it's worth, to the foo just above):
;;; (defun foo (x) (if (consp x) (cons (ifix (first x)) (foo (rest x))) nil)).
;;; Then when we run the original simplify-body exactly as below, the resulting
;;; body is as follows.

;;;   (AND (CONSP X) (CONS (CAR X) (FOO{1} (CDR X))))

;;; The task of deciding whether or not the result should have AND probably
;;; needs to consider not only the translated simplified body, but also the
;;; original untranslated body.  That seems potentially messy.  Moreover, if
;;; the final result isn't more or less "perfect" (whatever that means), then
;;; it may confuse more than it helps because of the unpredictability.  If we
;;; avoid trying to reconstruct, then at least the final result is predictably
;;; something that is returned by untranslate.

    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :USE (:TERMINATION-THEOREM FOO)))))
      (if (ATOM X) ;the ifix here gets dropped!
          NIL
        (CONS (CAR X) (FOO{1} (REST X)))))

   (DEFTHM FOO-BECOMES-FOO{1}
      (IMPLIES (INTEGER-LISTP x)
               (EQUAL (FOO X) (FOO{1} X))))))

;; Test of mutual recursion (simplifies all functions in the nest)
(deftest
  (mutual-recursion
   (defun foo (x) (if (atom x) (+ 1 1) (cons (ffn-symb x) (foo-lst (rest x)))))
   (defun foo-lst (x)
     (if (atom x)
         nil
       (cons (+ 1 2 (foo (first x)))
             (foo-lst (rest x))))))
  (simplify-defun foo)
  (must-be-redundant
    (MUTUAL-RECURSION
     (DEFUN FOO{1} (X)
       (DECLARE (XARGS :NORMALIZE NIL
                       :GUARD T
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           2
           (CONS (FFN-SYMB X) (FOO-LST{1} (REST X)))))
     (DEFUN FOO-LST{1} (X)
       (DECLARE (XARGS :NORMALIZE NIL
                       :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL
                       :HINTS (("Goal" :USE (:TERMINATION-THEOREM FOO-LST))
                               '(:IN-THEORY (DISABLE* FOO-LST (:E FOO-LST)
                                                      (:T FOO-LST))))))
       (IF (ATOM X)
           NIL
           (CONS (+ 3 (FOO{1} (CAR X)))
                 (FOO-LST{1} (REST X))))))
    (DEFTHM FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))
    (DEFTHM FOO-LST-BECOMES-FOO-LST{1}
      (EQUAL (FOO-LST X) (FOO-LST{1} X)))))

;; As above, but specify the simplification of only one function
(deftest
  (mutual-recursion
   (defun foo (x) (if (atom x) (+ 1 1) (cons (ffn-symb x) (foo-lst (rest x)))))
   (defun foo-lst (x)
     (if (atom x)
         nil
       (cons (+ 1 2 (foo (first x)))
             (foo-lst (rest x))))))
  (simplify-defun foo :simplify-body (:map (foo t) (foo-lst nil)))
  (must-be-redundant
    (MUTUAL-RECURSION
     (DEFUN FOO{1} (X)
       (DECLARE (XARGS :NORMALIZE NIL
                       :GUARD T
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           2
           (CONS (FFN-SYMB X)
                 (FOO-LST{1} (REST X)))))
     (DEFUN FOO-LST{1} (X)
       (DECLARE (XARGS :NORMALIZE NIL
                       :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           NIL
           (CONS (+ 1 2 (FOO{1} (FIRST X)))
                 (FOO-LST{1} (REST X))))))
    (DEFTHM FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))
    (DEFTHM FOO-LST-BECOMES-FOO-LST{1}
      (EQUAL (FOO-LST X) (FOO-LST{1} X)))))

; Mutual-recursion with same :assumptions for each function
(deftest
  (mutual-recursion
   (defun f1 (x)
     (if (consp x)
         (cons (+ 1 -1 (car x)) (f2 (cdr x)))
       nil))
   (defun f2 (x)
     (if (consp x)
         (cons (+ -1 1 (car x)) (f1 (cdr x)))
       nil)))
  (defthm acl2-numberp-of-car
    (implies (and (not (atom x))
                  (integer-listp x))
             (acl2-numberp (car x))))
  (simplify-defun f1 :assumptions ((integer-listp x)))
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (CONS (CAR X)
                (F2{1} (CDR X)))
          NIL))
    (DEFUN F2{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (CONS (CAR X)
                (F1{1} (CDR X)))
          NIL)))
   (DEFTHM F1-BECOMES-F1{1}
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F1 X) (F1{1} X))))
   (DEFTHM F2-BECOMES-F2{1}
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F2 X) (F2{1} X))))))

; Mutual-recursion with different :assumptions for each function
(deftest
  (mutual-recursion
   (defun f1 (x)
     (if (and (consp x)
              (integer-listp x))
         (cons (+ 1 -1 (car x))
               (f2 (cdr x)))
       nil))
   (defun f2 (x)
     (if (consp x)
         (cons (+ -1 1 (car x)) (f1 (cdr x)))
       nil)))
  (defthm acl2-numberp-of-car
    (implies (and (not (atom x))
                  (integer-listp x))
             (acl2-numberp (car x))))
  (simplify-defun f1
                  :assumptions
; As a test, we switch the order of keys in the :map alist from clique order.
                  (:map (f2 ((integer-listp x))) (f1 nil)))
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F1{1} (X)
                       (DECLARE (XARGS :NORMALIZE NIL
                                       :GUARD T
                                       :VERIFY-GUARDS NIL))
                       (IF (AND (CONSP X) (INTEGER-LISTP X))
                           (CONS (CAR X) (F2{1} (CDR X)))
                           NIL))
                     (DEFUN F2{1} (X)
                       (DECLARE (XARGS :NORMALIZE NIL
                                       :GUARD T
                                       :VERIFY-GUARDS NIL))
                       (IF (CONSP X)
                           (CONS (CAR X) (F1{1} (CDR X)))
                           NIL)))
   (DEFTHM F1-BECOMES-F1{1}
     (EQUAL (F1 X) (F1{1} X)))
   (DEFTHM F2-BECOMES-F2{1}
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F2 X) (F2{1} X))))))

; Test of :map, which also tests that congruence-theory is enabled even when
; only some of the function bodies have patterns.

(deftest
  (mutual-recursion
   (defun f1 (x)
     (if (consp x)
         (f2 (cdr x))
       (car (cons x (car (cons x x))))))
   (defun f2 (x)
     (if (consp x)
         (f3 (cdr x))
       (car (cons x (car (cons x x))))))
   (defun f3 (x)
     (if (consp x)
         (f4 (cdr x))
       (car (cons x (car (cons x x))))))
   (defun f4 (x)
     (if (consp x)
         (f5 (cdr x))
       (car (cons x (car (cons x x))))))
   (defun f5 (x)
     (if (consp x)
         (f1 (cdr x))
       (car (cons x (car (cons x x)))))))
  (simplify-defun f1 :simplify-body (:map ((f2 f3) nil)
                                          (f5 (cons x @))
                                          (:otherwise t)))
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X) (F2{1} (CDR X)) X))
    (DEFUN F2{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F3{1} (CDR X))
          (CAR (CONS X (CAR (CONS X X))))))
    (DEFUN F3{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F4{1} (CDR X))
          (CAR (CONS X (CAR (CONS X X))))))
    (DEFUN F4{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X) (F5{1} (CDR X)) X))
    (DEFUN F5{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F1{1} (CDR X))
          (CAR (CONS X X)))))
   (DEFTHM F1-BECOMES-F1{1} (EQUAL (F1 X) (F1{1} X))
     :HINTS (("Goal" :USE F1-BECOMES-F1{1}-LEMMA
              :IN-THEORY NIL)))
   (DEFTHM F2-BECOMES-F2{1} (EQUAL (F2 X) (F2{1} X))
     :HINTS (("Goal" :USE F2-BECOMES-F2{1}-LEMMA
              :IN-THEORY NIL)))
   (DEFTHM F3-BECOMES-F3{1} (EQUAL (F3 X) (F3{1} X))
     :HINTS (("Goal" :USE F3-BECOMES-F3{1}-LEMMA
              :IN-THEORY NIL)))
   (DEFTHM F4-BECOMES-F4{1} (EQUAL (F4 X) (F4{1} X))
     :HINTS (("Goal" :USE F4-BECOMES-F4{1}-LEMMA
              :IN-THEORY NIL)))
   (DEFTHM F5-BECOMES-F5{1} (EQUAL (F5 X) (F5{1} X))
     :HINTS (("Goal" :USE F5-BECOMES-F5{1}-LEMMA
              :IN-THEORY NIL)))))

; Specify that no simplification is done
(deftest

  (defun foo (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (foo (cdr x))
      (car (cons x x))))

  (simplify-defun foo
                  :simplify-body nil
                  :simplify-guard nil
                  :simplify-measure nil)

  (must-be-redundant
    (DEFUND FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD (AND (TRUE-LISTP X) (NOT (ATOM X)))
                      :MEASURE (FIX (LEN X))
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X))
          (FOO{1} (CDR X))
          (CAR (CONS X X))))))

;; test of :enable
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify-defun foo :enable (double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; test of :enable with just a symbol
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify-defun foo :enable double)
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; test of :enable with multiple rules
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify-defun foo :enable (double natp))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

; simple test of :theory
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify-defun foo :theory '(double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

; another test of :theory
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify-defun foo :theory (enable double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; test of :enable and :disable
(deftest
  (defun foo (x) (+ x x))
  (defthmd double-good
    (equal (+ x x) (* 2 x)))
  (defthm double-bad
    (equal (+ x x) (+ 0 (* 2 x))))
  (simplify-defun foo :enable (double-good) :disable (double-bad))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; reverse of previous test
(deftest
  (defun foo (x) (+ x x))
  (defund zerofn (x) (declare (ignore x)) 0)
  (defthm double-good
    (equal (+ x x) (* 2 x)))
  (defthmd double-bad
    (equal (+ x x) (+ (zerofn x) (* 2 x))))
  (simplify-defun foo :enable (double-bad) :disable (double-good))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (+  (zerofn x) (* 2 X)))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; as for test before last, but using rulesets
(deftest
  (defun foo (x) (+ x x))
  (defthmd double-good
    (equal (+ x x) (* 2 x)))
  (defthm double-bad
    (equal (+ x x) (+ 0 (* 2 x))))
  (def-ruleset my-enables '(double-good))
  (def-ruleset my-disables '(double-bad))
  (simplify-defun foo :enable my-enables :disable my-disables)
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO{1}
      (EQUAL (FOO X) (FOO{1} X)))))

;; test of :enable nil:
(deftest
  (defun foo (x) (car (cons x x)))
  (simplify-defun foo :enable nil)
  (must-be-redundant
   (DEFUN FOO{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL
                     :GUARD-HINTS (("Goal") '(:IN-THEORY (ENABLE*)))))
     X)))

;; Test where the assumption is hidden inside a function call that we expand
;; before simplifying:
(deftest
  (defund integerp-wrapper (x) (integerp x)) ;this gets expanded below
  (defun foo (x)
    (ifix x))
  (simplify-defun foo :assumptions ((integerp-wrapper x))
                 :enable (integerp-wrapper))
  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL :normalize nil))
      X)
    (DEFTHM FOO-BECOMES-FOO{1}
      (IMPLIES (INTEGERP-wrapper X) ;the unsimplified assumption
               (EQUAL (FOO X)
                      (FOO{1} X))))))


;; Test a bad argument to :theory (causes an error in tool2, which we catch):
(deftest
  (must-fail (simplify-defun natp :theory '(((f)))))
)

;; Test simplification with respect to use of guard as the assumptions.
(deftest

  (defun foo (x)
    (declare (xargs :guard (true-listp x)))
    (if (consp x)
        (foo (cdr x))
      x))

  (simplify-defun foo :assumptions :guard)

  (must-be-redundant
    (DEFUN FOO{1} (X)
      (DECLARE
       (XARGS :NORMALIZE NIL
              :GUARD (TRUE-LISTP X)
              :MEASURE (ACL2-COUNT X)
              :VERIFY-GUARDS T
              :GUARD-HINTS (("Goal" :USE (:GUARD-THEOREM FOO)))
              :HINTS (("Goal" :USE (:TERMINATION-THEOREM FOO)))))
      (IF (CONSP X)
          (FOO{1} (CDR X))
        NIL))
    (DEFTHM FOO-BECOMES-FOO{1}
      (IMPLIES (TRUE-LISTP X)
               (EQUAL (FOO X) (FOO{1} X))))))

;; Test :verify-guards.

;; First, test default for :verify-guards (two tests).
(deftest

  (defun foo (x)
    (car (cons x x)))

  (simplify-defun foo)

  (assert-event (eq (symbol-class 'foo{1} (w state)) :ideal)))

(deftest

  (defun foo (x)
    (declare (xargs :verify-guards t))
    (car (cons x x)))

  (simplify-defun foo)

  (assert-event (eq (symbol-class 'foo{1} (w state)) :common-lisp-compliant)))

;; Next, test :verify-guards t.
(deftest

  (defun foo (x)
    (declare (xargs :verify-guards nil))
    (car (cons x x)))

  (simplify-defun foo :verify-guards t)

  (assert-event (eq (symbol-class 'foo{1} (w state)) :common-lisp-compliant)))

;; Finally, test :verify-guards nil.
(deftest

  (defun foo (x)
    (declare (xargs :verify-guards t))
    (car (cons x x)))

  (simplify-defun foo :verify-guards nil)

  (assert-event (eq (symbol-class 'foo{1} (w state)) :ideal)))

;; Test error from :?.  Error should say:
;;; ACL2 Error in SIMPLIFY-DEFUN:  It is illegal to simplify the DEFUN
;;; for FOO because its measure, (:? X), is a call of :?.
(deftest

  (encapsulate
    ()
    (local (defun foo (x)
             (if (consp x)
                 (foo (cdr x))
               (car (cons x x)))))

    (defun foo (x)
      (declare (xargs :measure (:? x)))
      (if (consp x)
          (foo (cdr x))
        (car (cons x x)))))

  (must-fail (simplify-defun foo)))

;; Basic test of simplifying guard and measure
(deftest

  (defun foo (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (foo (cdr x))
      x))

  (simplify-defun foo
                  :simplify-body nil
                  :simplify-guard t
                  :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD (AND (TRUE-LISTP X) (CONSP X))
                      :MEASURE (LEN X)
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X)) (FOO{1} (CDR X)) X)))

  (defun bar (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (bar (cdr x))
      x))

  (must-fail ; attempt fails to simplify the body
   (simplify-defun bar
                   :simplify-guard t
                   :simplify-measure t))

  (simplify-defun bar
                  :must-simplify nil
                  :simplify-guard t
                  :simplify-measure t))

;; As above, but use long form of :must-simplify.

(deftest

  (defun foo (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (foo (cdr x))
      x))

  (simplify-defun foo
                  :simplify-body nil
                  :simplify-guard t
                  :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD (AND (TRUE-LISTP X) (CONSP X))
                      :MEASURE (LEN X)
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X)) (FOO{1} (CDR X)) X)))

  (defun bar (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (bar (cdr x))
      x))

  (must-fail ; attempt fails to simplify the body
   (simplify-defun bar
                   :must-simplify (:body t)
                   :simplify-guard t
                   :simplify-measure t))

  (simplify-defun bar
                  :must-simplify (:body nil)
                  :simplify-guard t
                  :simplify-measure t))

;; Assumptions are not used when simplifying guard and measure
(deftest

  (defun foo (x)
    (declare (xargs :guard (natp x)
                    :measure (nfix x)))
    (if (zp x)
        x
      (foo (1- x))))

  (simplify-defun foo
                  :assumptions :guard
                  :simplify-guard t
                  :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD (AND (INTEGERP X) (NOT (< X 0)))
                      :MEASURE (IF (INTEGERP X) (IF (< X 0) 0 X) 0)
                      :VERIFY-GUARDS T))
      (IF (ZP X) 0 (FOO{1} (1- X))))))

;; Let's test the use of a pattern for :simplify-body.

(deftest

  (encapsulate
    ((p1 (x) t)
     (p0 (x) t)
     (p1a (x) t)
     (p2 (x) t)
     (f (x) t)
     (g (x) t))
    (set-ignore-ok t)
    (set-irrelevant-formals-ok t)
    (local (defun p0 (x) nil))
    (local (defun p1 (x) nil))
    (local (defun p1a (x) (p1 x)))
    (local (defun p2 (x) nil))
    (defun p2a (x) (p2 x))
    (local (defun f (x) x))
    (local (defun g (x) x))
    (defthm p0-implies-p1a-equals-p1
      (implies (p0 x)
               (equal (p1a x)
                      (p1 x))))
    (defthm p1-and-p2-imply-f-id
      (implies (and (p0 x) (p1 x) (not (p2 x)))
               (equal (f x) x))))

  (defun foo (x)
    (declare (xargs :normalize nil))
    (g (if (p1 x) (g (if (p2a x) (cons x x) (f x))) (cons x x))))

  (simplify-defun foo
                  :assumptions ((p0 x)))

  (simplify-defun foo
                  :assumptions ((p0 x))
                  :simplify-body (if (p2a x) (cons x x) @)
; numbered-names mod (new name)
                  :new-name foo{2})

  (must-be-redundant

    (DEFUN FOO{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (G (IF (P1 X)
             (G (IF (P2 X) (CONS X X) X))
             (CONS X X))))

    (DEFUN FOO{2} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (G (IF (P1 X)
             (G (IF (P2A X) (CONS X X) X))
             (CONS X X))))))

; Simple test with pattern that failed before fixing fn-is-fn-copy to use
; install-not-normalized-name in its hint:

(deftest
  (defun foo (x) (cons x x))
  (defun bar (x) (cons x x))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo y) (bar y) z)))
  (simplify-defun f
                  :simplify-body (if (foo x) @ z))
  (must-be-redundant
    (DEFUN F{1} (X Y Z)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (CONS (IF (FOO X) (CONS X X) Z)
            (IF (FOO Y) (BAR Y) Z)))))

; Test the need for exact matches of pattern variables other than underscores,
; and also test that two underscore variable occurrences must match to the same
; subterm.  First, the simple example from the :doc; then, a modification that
; illustrates pattern matching in more detail.

(deftest
  (defun foo (x) x)
  (defun bar (x) (if x (cons x x) 17))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo x) (foo y) z)))
  (simplify-defun f
                  :simplify-body (if (foo x) @ z)))

(deftest
  (defun foo (x) x)
  (defun bar (x) (if x (cons x x) 17))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo x) (foo y) z)))
; Note that (foo x) is not an instance of (foo a) by instantiating only @-vars
; and _-vars.
  (must-fail (simplify-defun f
                             :simplify-body (if (foo a) @ z)))
  (simplify-defun f
                  :simplify-body (if (foo _a) @ _b))
  (must-be-redundant
    (DEFUN F{1} (X Y Z)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (CONS (IF (FOO X) (CONS X X) Z)
            (IF (FOO X) (FOO Y) Z)))))

; As just above, but notice that underscore can be replicated.
(deftest
  (defun foo (x) x)
  (defun bar (x) (if x (cons x x) 17))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo x) (foo y) z)))
  (simplify-defun f
                  :simplify-body (if (foo _) @ _))
  (must-be-redundant
    (DEFUN F{1} (X Y Z)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (CONS (IF (FOO X) (CONS X X) Z)
            (IF (FOO X) (FOO Y) Z)))))

; Test sensitivity to generated equivalence relation at subterm.

(deftest
  (defund foo (a)
    (declare (xargs :guard t))
    (list a))
  (defthm member-equal-foo
    (member-equal a (foo a))
    :hints (("Goal" :in-theory (enable foo))))
  (defun f (a)
    (declare (xargs :guard t))
    (if (member-equal a (foo a)) t nil))
  (simplify-defun f
                  :simplify-body (if @ t nil))
  (must-be-redundant
    (DEFUN F{1} (A)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T))
      T)))

; Second test of sensitivity to generated equivalence relation at subterm,
; which failed in the initial implementation of their handling in function
; fn-simp-body.

(deftest
  (defund foo (a)
    (declare (xargs :guard t))
    (list a))
  (defthm member-equal-foo
    (member-equal a (foo a))
    :hints (("Goal" :in-theory (enable foo))))
  (defun my-equiv (x y)
    (declare (xargs :guard t))
    (equal x y))
  (defequiv my-equiv)
  (defun my-if (x y z)
    (declare (xargs :guard t))
    (if x y z))
  (defthm iff-implies-equal-my-if-1
    (implies (iff x x-equiv)
             (equal (my-if x y z) (my-if x-equiv y z)))
    :rule-classes (:congruence))
  (defthm my-equiv-implies-equal-my-if-1
    (implies (my-equiv x x-equiv)
             (equal (my-if x y z) (my-if x-equiv y z)))
    :rule-classes (:congruence))
  (defun f (a)
    (declare (xargs :guard t))
    (my-if (member-equal a (foo a)) t nil))
  (simplify-defun f
                  :simplify-body (my-if @ t nil))
  (must-be-redundant
    (DEFUN F{1} (A)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T))
      (MY-IF T T NIL))))

; Test of simplifying guard with respect to Boolean equivalence

(defun fix-true-listp (lst)
  (if (consp lst)
      (cons (car lst)
            (fix-true-listp (cdr lst)))
    nil))

(defthm member-fix-true-listp
  (iff (member a (fix-true-listp lst))
       (member a lst)))

(deftest
  (defun foo (x y)
    (declare (xargs :guard (member-equal x (ec-call (fix-true-listp y)))))
    (cons x y))
  (simplify-defun foo :simplify-body nil :simplify-guard t :verify-guards nil)
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD (MEMBER-EQUAL X Y)
                      :VERIFY-GUARDS NIL))
      (CONS X Y))))

; Test of :guard-hints.
(deftest
  (defun my-consp (x)
    (declare (xargs :guard t))
    (consp x))
  (defun my-cdr (x)
    (declare (xargs :guard (my-consp x)))
    (cdr x))
  (defun f1 (x)
    (declare (xargs :guard t))
    (if (consp x)
        (if (my-consp (f1 (cdr x)))
            (f1 (my-cdr x))
          x)
      (car (cons x x))))
  (defthm f1-measure-lemma
    (equal (acl2-count (my-cdr x))
           (acl2-count (cdr x))))
  (in-theory (disable my-cdr my-consp (tau-system)))
  (must-fail (simplify-defun f1))
  (simplify-defun f1
                  :guard-hints
                  (("Goal" :in-theory (enable my-cdr my-consp))))
  (must-be-redundant
   (DEFUN F1{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T
                     :GUARD-HINTS (("Goal" :IN-THEORY (ENABLE MY-CDR MY-CONSP)))
                     :HINTS (("Goal" :USE (:TERMINATION-THEOREM F1))
                             '(:IN-THEORY (DISABLE* F1 (:E F1) (:T F1))))))
     (IF (CONSP X)
         (IF (MY-CONSP (F1{1} (CDR X)))
             (F1{1} (MY-CDR X))
             X)
         X))))

; It would be good to add a test here that default-hints are ignored.  But
; after CONSIDERABLE effort I (Matt) haven't been able to make such a test for
; the latest version of simplify-defun, because of the priority of (new)
; explicit hints.  Maybe another time.

; Test of :measure-hints.
(deftest
  (defun k (x y)
    (declare (ignore y))
    x)
  (defund foo (x y)
    (declare (xargs :ruler-extenders :all))
    (if (consp x)
        (foo (k (cdr x) (foo (cdr x) y)) y)
      (car (cons y y))))
  (in-theory (disable k))
  (simplify-defun foo ; fails (takes awhile) without the following:
                  :measure-hints (("Goal" :in-theory (enable k))))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL
                      :HINTS (("Goal" :IN-THEORY (ENABLE K)))))
      (IF (CONSP X)
          (FOO{1} (K (CDR X) (FOO{1} (CDR X) Y)) Y)
          Y))))

; Tests for more than one match: non-recursive case, top-level term.

(deftest
  (defun foo (x y)
    (declare (xargs :ruler-extenders :all))
    (list
     (* 3 (+ 1 (+ 1 x)))
     (* 3 (+ 1 (+ 1 x)))
     (* 4 5 (+ 1 (+ 1 y)))))
; Underscore variables other than _ must be distinct for matches to different
; terms:
  (must-fail (simplify-defun foo
                             :simplify-body (list (* 3 @1)
                                                  _1
                                                  (* _1 5 @2))))
; @-variables other than @ must be distinct for matches to different terms:
  (must-fail (simplify-defun foo
                             :simplify-body (list (* 3 @1)
                                                  _
                                                  (* 4 5 @1))))
; This one is fine.
  (simplify-defun foo
                  :simplify-body (list (* 3 @1)
                                       _1
                                       (* _2 5 @2)))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :RULER-EXTENDERS :ALL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (LIST (* 3 (+ 2 X))
            (* 3 (+ 1 (+ 1 X)))
            (* 4 5 (+ 2 Y))))))

; As above, but allow @ to match more than one term.
(deftest
  (defun foo (x y)
    (declare (xargs :ruler-extenders :all))
    (list
     (* 3 (+ 1 (+ 1 x)))
     (* 3 (+ 1 (+ 1 x)))
     (* 4 5 (+ 1 (+ 1 y)))))
  (simplify-defun foo
                  :simplify-body (list (* 3 @)
                                       _1
                                       (* _2 5 @)))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :RULER-EXTENDERS :ALL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (LIST (* 3 (+ 2 X))
            (* 3 (+ 1 (+ 1 X)))
            (* 4 5 (+ 2 Y))))))

; Tests for more than one match: non-recursive case, non-top-level term.

(deftest
  (defun foo (x y)
    (list (list (list
                 (* 3 (+ 1 (+ 1 x)))
                 (* 3 (+ 1 (+ 1 x)))
                 (* 4 5 (+ 1 (+ 1 y)))))))
; Underscore variables other than _ must be distinct for matches to different terms:
  (must-fail (simplify-defun foo
                             :simplify-body (list (* 3 @1)
                                                  _a
                                                  (* _a 5 @2))))
; @-vars other than @ must be distinct for matches to different terms, and we
; want a suitable error message about that even if matching fails:
  (must-fail (simplify-defun foo
                             :simplify-body (list (* 3 @a)
                                                  @a
                                                  _)))
; This one is fine.
  (simplify-defun foo
                  :simplify-body (list (* 3 @1)
                                       _1
                                       (* _2 5 @2)))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (LIST (LIST (LIST (* 3 (+ 2 X))
                        (* 3 (+ 1 (+ 1 X)))
                        (* 4 5 (+ 2 Y))))))))

; As just above, but notice that @ can be replicated.
(deftest
  (defun foo (x y)
    (list (list (list
                 (* 3 (+ 1 (+ 1 x)))
                 (* 3 (+ 1 (+ 1 x)))
                 (* 4 5 (+ 1 (+ 1 y)))))))

; This one is fine.
  (simplify-defun foo
                  :simplify-body (list (* 3 @)
                                       _1
                                       (* _2 5 @)))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (LIST (LIST (LIST (* 3 (+ 2 X))
                        (* 3 (+ 1 (+ 1 X)))
                        (* 4 5 (+ 2 Y))))))))

; Tests for more than one match: recursive case.

(deftest
  (defun foo (x y)
    (declare (xargs :ruler-extenders :all))
    (list (list
           (if (consp y)
               (foo (list (* 3 (+ 1 (+ 1 x)))
                          (* 4 (+ 1 (+ 1 (car y)))))
                    (cdr y))
             (cons x (* 5 6 (+ 1 1 y)))))))
  (simplify-defun foo
                  :simplify-body (if _1
                                     (foo (list @1 _2)
                                          _3)
                                   (cons _4 (* _5 _6 @2))))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT Y)
                      :VERIFY-GUARDS NIL))
      (LIST (LIST
             (IF (CONSP Y)
                 (FOO{1} (LIST (+ 6 (* 3 X))
                              (* 4 (+ 1 (+ 1 (CAR Y)))))
                        (CDR Y))
                 (CONS X (* 5 6 (+ 2 Y)))))))))

; Exactly as above, but with right-associated (flat) unsimplified + call.
(deftest
  (defun foo (x y)
    (declare (xargs :ruler-extenders :all))
    (list (list
           (if (consp y)
               (foo (list (* 3 (+ 1 (+ 1 x)))
                          (* 4 (+ 1 1 (car y))))
                    (cdr y))
             (cons x (* 5 6 (+ 1 1 y)))))))
  (simplify-defun foo
                  :simplify-body (if _1
                                     (foo (list @1 _2)
                                          _3)
                                   (cons _4 (* _5 _6 @2))))
  (must-be-redundant
    (DEFUN FOO{1} (X Y)
      (DECLARE (XARGS :NORMALIZE NIL
                      :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT Y)
                      :VERIFY-GUARDS NIL))
      (LIST (LIST
             (IF (CONSP Y)
                 (FOO{1} (LIST (+ 6 (* 3 X))
                              (* 4 (+ 1 1 (CAR Y))))
                        (CDR Y))
                 (CONS X (* 5 6 (+ 2 Y)))))))))

; Some tests of handling by directed-untranslate of iff flag, OR, IMPLIES,
; COND, <= etc., perhaps more.
(deftest
  (defun f1a (x z)
    (not (or (car (cons x x)) z)))
  (simplify-defun f1a)
  (must-be-redundant
   (DEFUN F1a{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun f1b (x z)
    (not (if (car (cons x x)) (car (cons x x)) z)))
  (simplify-defun f1b)
  (must-be-redundant ; avoid OR; test iff-flg = t under NOT
   (DEFUN F1B{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (IF X T Z))))
  (defun f1c (x z)
    (not (if (car (cons x x)) t z)))
  (simplify-defun f1c)
  (must-be-redundant
   (DEFUN F1C{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (IF X T Z))))
  (defun f2 (x y)
    (implies (car (cons x x)) y))
  (simplify-defun f2)
  (must-be-redundant ; untranslating (IF X (IF Y 'T 'NIL) 'T)
   (DEFUN F2{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES X Y)))
  (defun f3 (x y)
    (implies (car (cons x x)) (not y)))
  (simplify-defun f3)
  (must-be-redundant ; interesting case, seen with (trace{ }directed-untranslate-rec)
   (DEFUN F3{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES X (NOT Y))))
  (defun f4 (x y)
    (implies (not (car (cons x x))) y))
  (simplify-defun f4)
  (must-be-redundant ; directed-untranslate handles (if x 't (if y 't 'nil))
   (DEFUN F4{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES (NOT X) Y)))
  (defun f5a (x y z)
    (cond ((consp x) y)
          (t (car (cons z z)))))
  (simplify-defun f5a)
  (must-be-redundant
   (DEFUN F5A{1} (X Y Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (COND ((CONSP X) Y) (T Z))))
  (defun f5b (x y z)
    (if (consp x)
        y
      (car (cons z z))))
  (simplify-defun f5b)
  (must-be-redundant
   (DEFUN F5B{1} (X Y Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) Y Z)))
  (defun f6 (x y z)
    (cond ((consp x) y)
          ((consp y) x)
          (t (car (cons z z)))))
  (simplify-defun f6)
  (must-be-redundant
   (DEFUN F6{1} (X Y Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (COND ((CONSP X) Y)
           ((CONSP Y) X)
           (T Z))))
  (defun f7a (x y)
    (<= (car (cons x x)) y))
  (simplify-defun f7a)
  (must-be-redundant
   (DEFUN F7A{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (<= X Y)))
  (defun f7b (x y) ; equivalent to f7a, but directed-untranslate should avoid <=
    (not (< y (car (cons x x)))))
  (simplify-defun f7b)
  (must-be-redundant
   (DEFUN F7B{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (< Y X))))
  (defun f8a (x y)
    (>= (car (cons x x)) y))
  (simplify-defun f8a)
  (must-be-redundant
   (DEFUN F8A{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (>= X Y)))
  (defun f8b (x y) ; equivalent to f7a, but directed-untranslate should avoid <=
    (not (< (car (cons x x)) y)))
  (simplify-defun f8b)
  (must-be-redundant
   (DEFUN F8B{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (< X Y))))
  (defun f9a (x y)
    (> (car (cons x x)) y))
  (simplify-defun f9a)
  (must-be-redundant
   (DEFUN F9A{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (> X Y)))
  (defun f9b (x y) ; equivalent to f9a, but directed-untranslate should avoid <=
    (< y (car (cons x x))))
  (simplify-defun f9b)
  (must-be-redundant
   (DEFUN F9B{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (< Y X)))
; Avoid mistakes in macro handling.
  (defun f10a (x)
    (identity (car (cddr x))))
  (simplify-defun f10a)
  (must-be-redundant ; tracking fails when identity is stripped off
   (DEFUN F10A{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (CAR (CDR (CDR X)))))
  (defun f10b (x)
    (identity (car (cddr x))))
  (simplify-defun f10b :untranslate t)
  (must-be-redundant
   (DEFUN F10B{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (CADDR X)))
  (defun f11 (x)
    (cddr (caddar (car (cdar (identity (car (cddr x))))))))
  (simplify-defun f11)
  (must-be-redundant ; as above, no hope for direction under expansion of identity call
   (DEFUN F11{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (CDDR (CADDAR (CAR (CDAR (CAR (CDR (CDR X)))))))))

; The following should preserve (if z z w) rather than converting it to (or z
; w), but since the true and false branches are switched during simplification
; (as seen if you evaluate (trace{ }tool2-fn) first), this requires a bit of
; care by directed-untranslate.
  (defun f12 (x y z w)
    (if (not x) (car (cons y y)) (if z z w)))
  (simplify-defun f12)
  (must-be-redundant
   (DEFUN F12{1} (X Y Z W)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (NOT X) Y (IF Z Z W)))))

; Tests for :untranslate option
(deftest
  (defun g1 (x z)
    (not (or (car (cons x x)) z)))
  (simplify-defun g1)
  (must-be-redundant
   (DEFUN G1{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun g2 (x z)
    (not (or (car (cons x x)) z)))
  (simplify-defun g2 :untranslate t)
  (must-be-redundant
   (DEFUN G2{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun g3 (x z)
    (not (or (car (cons x x)) z)))
  (must-fail (simplify-defun g3 :untranslate :bad-option))
  (simplify-defun g3 :untranslate nil)
  (must-be-redundant
   (DEFUN G3{1} (X Z)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (IF X 'T Z) 'NIL 'T))))

; Require simplification even after untranslate: simplifies by expanding
; implies, but directed-untranslate puts back the implies.
(deftest
  (defun foo (x y)
    (implies x y))
  (must-fail (simplify-defun foo)))

;;; Test :expand hints

(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify-defun foo :expand (append x y))
  (must-be-redundant
   (DEFUN FOO{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL
                     :GUARD-HINTS (("Goal") '(:IN-THEORY :NONE))))
     (CONS 17
           (IF (CONSP X)
               (CONS (CAR X) (APPEND (CDR X) Y))
               Y)))))

; Same as above but slightly different :expand syntax.
(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify-defun foo :expand ((append x y)))
  (must-be-redundant
   (DEFUN FOO{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL
                     :GUARD-HINTS (("Goal") '(:IN-THEORY :NONE))))
     (CONS 17
           (IF (CONSP X)
               (CONS (CAR X) (APPEND (CDR X) Y))
               Y)))))

; Same as above but wilder :expand hint.
(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify-defun foo :expand ((:free (v) (append x v))))
  (must-be-redundant
   (DEFUN FOO{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL
                     :GUARD-HINTS (("Goal") '(:IN-THEORY :NONE))))
     (CONS 17
           (IF (CONSP X)
               (CONS (CAR X) (APPEND (CDR X) Y))
               Y)))))

;;; Tests involving duplicated pattern variables

(deftest

; First a basic test:

  (defun f1 (x y)
    (or (car (cons x y))
        (+ 1 1 y)))
  (simplify-defun f1 :simplify-body (or @ _))
; And just for fun:
  (simplify-defun f1 :simplify-body (or _ @)
; numbered-names mod (new name)
                  :new-name f1{2})
  (simplify-defun f1
; numbered-names mod (new name)
                  :new-name f1{3})
  (must-be-redundant
   (DEFUN F1{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR X (+ 1 1 Y)))
   (DEFUN F1{2} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR (CAR (CONS X Y)) (+ 2 Y)))
   (DEFUN F1{3} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR X (+ 2 Y))))

; Variant where the resulting (if a a b) simplifies to (if a t b).  This tests
; the ability to simplify the "a" in different contexts, since the second
; occurrences simplifies to T only in the context of the first.

  (defun f2 (x y)
    (or (car (cons (symbolp x) y))
        (+ 1 1 y)))
  (simplify-defun f2 :simplify-body (or @ _))
; And just for fun:
  (simplify-defun f2 :simplify-body (or _ @)
; numbered-names mod (new name)
                  :new-name f2{2})
  (simplify-defun f2
; numbered-names mod (new name)
                  :new-name f2{3})
  (must-be-redundant
   (DEFUN F2{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (SYMBOLP X) T (+ 1 1 Y)))
   (DEFUN F2{2} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR (CAR (CONS (SYMBOLP X) Y)) (+ 2 Y)))
   (DEFUN F2{3} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (SYMBOLP X) T (+ 2 Y))))

; A duplicate @-var is OK as long as all occurrences match the same term.  But
; the different terms may simplify differently because they are in different
; contexts.

  (defun f3 (x y)
    (if (car (cons x y))
        (if (booleanp x)
            (car (cons x y))
          (car (cons y x)))
      (cons y y)))
; Just for fun, notice that _-var occurrences must match unless the variable is
; _ itself.
  (must-fail
   (simplify-defun f3 :simplify-body (if @a (if _b @a _b) _)))
  (simplify-defun f3 :simplify-body (if @ (if _ @ _) _))
  (simplify-defun f3 :simplify-body (if @a (if _ @a _) _)
; numbered-names mod (new name)
                  :new-name f3{2})
  (must-be-redundant
   (DEFUN F3{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF X (IF (BOOLEANP X) T (CAR (CONS Y X)))
         (CONS Y Y)))
   (DEFUN F3{2} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF X (IF (BOOLEANP X) T (CAR (CONS Y X)))
         (CONS Y Y))))

; Check that the renaming of every @ avoids all other @-vars, even those that
; come after @.

  (defun f4 (x)
    (list (+ 1 1 x) (+ 1 1 x) (+ 3 4 x)))
  (simplify-defun f4 :simplify-body (list @ @ @0))
  (must-be-redundant
   (DEFUN F4{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ 2 X) (+ 2 X) (+ 7 X))))
  (defun f5 (x)
    (list (+ 3 4 x) (+ 1 1 x) (+ 1 1 x)))
  (simplify-defun f5 :simplify-body (list @0 @ @))
  (must-be-redundant
   (DEFUN F5{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ 7 X) (+ 2 X) (+ 2 X))))

; Check the renaming of dupliate @ occurrences doesn't happen after
; translation.

  (defun f6 (x)
    (if (rationalp (fix x)) (+ 1 1 x) x))

; The following formerly failed, because matching was implemented by renaming
; apart instances of @ only before translation.  Now it succeeds, because it is
; equivalent to the following form, which succeeded previously as well:
; (simplify-defun f6 :simplify-body (if @ @ _))

  (simplify-defun f6 :simplify-body (or @ _))

  (must-be-redundant
   (DEFUN F6{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (RATIONALP (IF (ACL2-NUMBERP X) X 0)) (+ 2 X) X))))

;;; Test :non-executable

(deftest
  (defun f1 (x y)
    (mv x y))
  (defun-nx f2 (x)
    (car (f1 (car x) (cdr x))))
  (simplify-defun f2)
  (must-be-redundant
   (DEFUN-NX F2{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (CAR X))))

;;; Test mv-let

(deftest
  (defund f1 (x y)
    (mv x y))
  (defun f2 (x)
    (mv-let (a b)
      (f1 (car x) (cdr x))
      (cons b (car (cons a a)))))
  (simplify-defun f2)
  (must-be-redundant
   (DEFUN F2{1} (X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV-LET (A B)
       (F1 (CAR X) (CDR X))
       (CONS B A)))))

;; Test mv

(deftest
  (defun f1 (x y)
    (mv y (car (cons x y))))
  (simplify-defun f1)
  (must-be-redundant
   (DEFUN F1{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV Y X))))

;; Test of simplifying a 0-ary function:
(deftest
  (defun foo (x) (+ 1 1 x))
  (defun bar () (foo 2))
  (simplify-defun foo)
  (simplify-defun bar)
  (must-be-redundant
   (DEFUN BAR{1} NIL
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     4)))

;; Tests of :equiv argument:

(deftest ; basic test
  (defun foo (e x)
    (member-equal e (fix-true-listp x)))
  (must-fail (simplify-defun foo))
  (simplify-defun foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO{1} (E X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (MEMBER-EQUAL E X))
   (DEFTHM FOO-BECOMES-FOO{1}
     (IFF (FOO E X) (FOO{1} E X)))))

(deftest ; need suitable context
  (defun foo (e x)
    (cons 3 (member-equal e (fix-true-listp x))))
  (must-fail (simplify-defun foo :equiv iff)))

(deftest ; silly recursive example (works even without :equiv
  (defun foo (e x)
    (cond ((member-equal e (fix-true-listp x))
           e)
          ((endp e) nil)
          (t (foo (cdr e) x))))
  (simplify-defun foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO{1} (E X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :MEASURE (ACL2-COUNT E)
                     :VERIFY-GUARDS NIL))
     (COND ((MEMBER-EQUAL E X) E)
           ((ENDP E) NIL)
           (T (FOO{1} (CDR E) X))))
   (DEFTHM FOO-BECOMES-FOO{1}
     (IFF (FOO E X) (FOO{1} E X)))))

(deftest           ; better recursive example
  (defun foo (a x) ; a occurs in x after first occurrence of 3
    (cond ((endp x) nil)
          ((eql (car x) 3)
           (member-equal a (fix-true-listp x)))
          (t (foo a (cdr x)))))
  (simplify-defun foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO{1} (A X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL
                     :HINTS (("Goal" :USE (:TERMINATION-THEOREM FOO)))))
     (COND ((ENDP X) NIL)
           ((EQL (CAR X) 3)
            (MEMBER-EQUAL A X))
           (T (FOO{1} A (CDR X)))))
   (DEFTHM FOO-BECOMES-FOO{1}
     (IFF (FOO A X) (FOO{1} A X)))))

(deftest           ; recursive example with :assumptions
  (verify-guards fix-true-listp)
  (defun foo (a x) ; a occurs in x after first occurrence of 3
    (declare (xargs :guard (rational-listp x)))
    (cond ((endp x) nil)
          ((eql (fix (car x)) 3)
           (member-equal a (fix-true-listp x)))
          (t (foo a (cdr x)))))
  (defthm car-rational-listp
    (implies (rational-listp x)
             (equal (fix (car x))
                    (if x (car x) 0))))
  (simplify-defun foo :equiv iff
                  :assumptions :guard
                  :disable fix)
  (must-be-redundant
   (DEFUN FOO{1} (A X)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD (RATIONAL-LISTP X)
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (COND ((ENDP X) NIL)
           ((EQL (CAR X) 3) (MEMBER-EQUAL A X))
           (T (FOO{1} A (CDR X)))))
   (DEFTHM FOO-BECOMES-FOO{1}
     (IMPLIES (RATIONAL-LISTP X)
              (IFF (FOO A X) (FOO{1} A X)))
     :HINTS (("Goal" :USE FOO-BECOMES-FOO{1}-LEMMA
              :IN-THEORY '(FOO-HYPS))))))

;; Tests of tranforming a recursive function to a non-recursive function, or
;; vice-versa.

(deftest ; Eric's example, except as extra stress I'll leave lenb enabled

  ;; not recursive:
  (defun lenb (x)
    (if (consp x)
        (+ 1 (len (cdr x)))
      0))

  ;; applying this rule should make it recursive again:
  (defthm len-becomes-lenb
    (equal (len x)
           (lenb x)))

; ;recursive: the call to lenb is get fixed up to be a call to lenb{1}:
  (simplify-defun lenb)

  (must-be-redundant
   (DEFUND LENB{1} (X)
     (DECLARE
      (XARGS :NORMALIZE NIL
             :GUARD T
             :VERIFY-GUARDS NIL))
     (IF (CONSP X) (+ 1 (LENB{1} (CDR X))) 0))
   (DEFTHM LENB-BECOMES-LENB{1}
     (EQUAL (LENB X) (LENB{1} X)))))

(deftest ; essentially Eric's example, but with guard and assumptions

  ;; not recursive:
  (defun lenb (x)
    (declare (xargs :guard (true-listp x)))
    (if (endp x)
        0
      (+ 1 (len (cdr x)))))

  ;; applying this rule should make it recursive again:
  (defthm len-becomes-lenb
    (implies (true-listp x)
             (equal (len x)
                    (lenb x))))

; ;recursive: the call to lenb is get fixed up to be a call to lenb{1}:
  (simplify-defun lenb :assumptions :guard)

  (must-be-redundant
   (DEFUND LENB{1} (X)
     (DECLARE
      (XARGS :NORMALIZE NIL
             :GUARD (TRUE-LISTP X)
             :VERIFY-GUARDS T))
     (IF (ENDP X) 0 (+ 1 (LENB{1} (CDR X)))))
   (DEFTHM LENB-BECOMES-LENB{1}
     (IMPLIES (TRUE-LISTP X)
              (EQUAL (LENB X) (LENB{1} X))))))

;; recursive to non-recursive

(deftest

  (defun lenb (x)
    (declare (xargs :guard (true-listp x)))
    (if (endp x)
        0
      (+ 1 (lenb (cdr x)))))

  ;; applying this rule should make the new function non-recursive:
  (defthm lenb-becomes-len
    (equal (lenb x)
           (len x)))

  (simplify-defun lenb)

  (must-be-redundant
   (DEFUN LENB{1} (X)
     (DECLARE
      (XARGS :NORMALIZE NIL
             :GUARD (TRUE-LISTP X)
             :VERIFY-GUARDS T))
     (IF (ENDP X) 0 (+ 1 (LEN (CDR X)))))
   (DEFTHM LENB-BECOMES-LENB{1}
     (EQUAL (LENB X) (LENB{1} X)))))

;; Test of :measure nil and :measure-hints nil.

(deftest
  (defun bar (x)
    (declare (xargs :measure (nfix x)))
    (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify-defun bar :measure nil :measure-hints nil)
  (must-be-redundant
    (DEFUND BAR{1} (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (ZP X) 0 (+ 2 (BAR{1} (+ -1 X)))))
    (DEFTHM BAR-BECOMES-BAR{1}
      (EQUAL (BAR X) (BAR{1} X)))))

;; Using OR (from the :doc).

(deftest
  (defun foo (x y)
    (if (true-listp (cons 3 x))
        (or (eql (length x) 17) y)
      'dont-care))

  ;; Pattern is actually (if @ @ _), so matches entire body, and test and true
  ;; branch are both simplified.
  (simplify-defun foo :simplify-body (or @ _))

  (must-be-redundant
   (DEFUN FOO{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (TRUE-LISTP X)
         (IF (EQL (LEN X) 17) T Y)
         'DONT-CARE)))

  ;; Pattern is actually (if @1 @1 _), so this time the entire body is not
  ;; matched and the OR call in the body is matched instead.
  (simplify-defun foo :simplify-body (or @1 _)
; numbered-names mod (new name)
                  :new-name foo{2})

  (must-be-redundant
   (DEFUN FOO{2} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (TRUE-LISTP (CONS 3 X))
         (IF (EQL (LEN X) 17) T Y)
         'DONT-CARE))))

;; Matching a specified subterm that has only part of it specified as a
;; simplification site (from the :doc).

(deftest
  (defun g (x y)
    (list (+ (nth 0 x) 3)
          (* (car (cons y y)) 4)
          (* (nth 0 x) 5)))

  (simplify-defun g :simplify-body (* (:@ (nth 0 x)) _))

  (must-be-redundant
   (DEFUN G{1} (X Y)
     (DECLARE (XARGS :NORMALIZE NIL
                     :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ (NTH 0 X) 3)
           (* (CAR (CONS Y Y)) 4)
           (* (AND (CONSP X) (CAR X)) 5)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Some explanation for how simplify-defun works
;;; Matt Kaufmann, Nov. 2015
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Below I'll present a small example that illustrates how simplify-defun works.
; This example includes guards, but the tool only verifies guards for the new
; function if they were already verified for the original function.

; We start with three definitions to support an unsimplified accessor,
; unsimplified hypotheses, and a definition to simplify, respectively.

(defun my-cddr (x)
  (declare (xargs :guard (symbol-listp x)))
  (cddr x))

(defun my-true-listp (x)
; There is no need to supply guards for the assumption.
  (true-listp x))

; The function to be simplified:
(defun f0 (x)
  (declare (xargs :guard (or (atom x)
                             (symbol-listp x))))
  (if (consp x)
      (cons x (f0 (my-cddr x)))
    x))

(simplify-defun f0
; The following two lines are equivalent.
                :hyp-fn my-true-listp
;              :assumptions '((my-true-listp x))
                )

; Here we see what was generated.  Notice that directed-untranslate has no
; real way of knowing that (my-cddr x) somehow generates the macro cddr.
(must-be-redundant
  (defun f0{1} (x)
    (declare (xargs :normalize nil
                    :guard (or (atom x) (symbol-listp x))
                    :MEASURE (ACL2-COUNT X)
                    :verify-guards t
                    :guard-hints (("Goal" :use (:guard-theorem f0)))
                    :hints (("Goal" :use (:termination-theorem f0)))))
    (if (consp x)
        (cons x (f0{1} (cdr (cdr x))))
      nil)))

; The large comment below provides some explanataion about the events
; generated.  For simplicity we ignore wrappers (WITH-OUTPUT, ENCAPSULATE,
; PROGN, and LOCAL); of course, to see those you may simply change the call of
; simplify-defun above to the corresponding call of show-simplify-defun.

; WARNING: Don't be surprised if this is slightly out of date!  (Perhaps with
; some effort we could uncomment the following, adding suitable "wrapper"
; code.)

#||

; Avoid issues regarding normalization of function bodies.
(INSTALL-NOT-NORMALIZED+ F0)

; Next is the new definition, with a simplified body.  The tool2-fn simplifier
; gives us simplified assumptions and then the new body: for the body,
; recursive calls are first replaced by calls of a defstub function, and then
; calls of that function are replaced by calls of the new function.  Note that
; the :GUARD is the same as on F0.  The value of :VERIFY-GUARDS is T becuase F0
; is guard-verified.
(DEFUN F0{1} (X)
  (DECLARE (XARGS :NORMALIZE NIL
                  :GUARD (OR (ATOM X) (SYMBOL-LISTP X))
                  :VERIFY-GUARDS T
                  :GUARD-HINTS (("Goal" :USE (:GUARD-THEOREM F0)))
                  :HINTS (("Goal" :USE (:TERMINATION-THEOREM F0))))
           (IGNORABLE X))
  (AND (CONSP X)
       (CONS X (F0{1} (CDDR X)))))

; The following function provides a convenient wrapper for the assumptions.
; Perhaps it should be avoided if :hyp-fn is supplied.
(DEFUN F0-HYPS (X)
  (DECLARE (IGNORABLE X))
  (MY-TRUE-LISTP X))

; The following key theorem could be proved in advance by the user, if f0-hyps
; is also defined in advance.  In simple examples the proof goes through
; automatically.  The :assumption-theory argument can help.  See the comments
; and code for hyps-preserved-thm and hyps-preserved-thm-1 for details about
; how this theorem is generated.
(DEFTHM F0-HYPS-PRESERVED-FOR-F0
  (IMPLIES (AND (F0-HYPS X) (CONSP X))
           (F0-HYPS (MY-CDDR X)))
  :RULE-CLASSES NIL)

; For efficiency, we save the runes used when simplifying assumptions and the
; body, to give in a hint later.  Perhaps this is overkill; it's also
; potentially a problem since ACL2's tracking isn't perfect (e.g., it doesn't
; track the use of congruence runes).
(DEFCONST *F0-RUNES*
  '((:DEFINITION F0-HYPS)
    (:DEFINITION MY-CDDR)
    (:DEFINITION MY-TRUE-LISTP)))

; Next we constrain a function to be a copy of the original function, under the
; unsimplified assumptions.  The hints should ensure that this event is
; reliably admitted very quickly.
(ENCAPSULATE (((F0-COPY *) => *))
  (LOCAL (DEFUN F0-COPY (X)
           (DECLARE (XARGS :NORMALIZE NIL))
           (F0 X)))
  (DEFTHM F0-COPY-DEF
    (IMPLIES (F0-HYPS X)
             (EQUAL (F0-COPY X)
                    (IF (CONSP X)
                        (CONS X (F0-COPY (MY-CDDR X)))
                        X)))
    :HINTS (("Goal" :IN-THEORY '((:D F0-COPY))
             :EXPAND ((F0 X))))
    :RULE-CLASSES :DEFINITION))

; An induction on the original function, appealing to the preservation theorem
; for the inductive steps, shows that the original function equals its copy
; under the assumptions.
(DEFTHM F0-IS-F0-COPY
  (IMPLIES (F0-HYPS X)
           (EQUAL (F0 X) (F0-COPY X)))
  :HINTS (("Goal" :INDUCT (F0 X)
           :IN-THEORY '(F0 F0-COPY-DEF))
          '(:USE F0-HYPS-PRESERVED-FOR-F0))
  :RULE-CLASSES NIL)

; Now comes the nice trick!  Since (as proved immediately above) the copy
; equals the original, then any other function satisfying the copy's constraint
; also equals the original -- in particular, the simplified function equals the
; original.
(DEFTHM F0-BECOMES-F0{1}-LEMMA
  (IMPLIES (F0-HYPS X)
           (EQUAL (F0 X) (F0{1} X)))
  :HINTS (("Goal"
           :BY (:FUNCTIONAL-INSTANCE F0-IS-F0-COPY (F0-COPY F0{1}))
           :IN-THEORY *F0-RUNES*)
          '(:USE F0{1})))))

; The main theorem is now a trivial corollary, simply by expanding the
; assumptions predicate.
(DEFTHM F0-BECOMES-F0{1}
  (IMPLIES (MY-TRUE-LISTP X)
           (EQUAL (F0 X) (F0{1} X)))
  :HINTS (("Goal" :USE F0-BECOMES-F0{1}-LEMMA
           :IN-THEORY '(F0-HYPS))))))
||#

;; TODO: Get this to work:

;; ;; This failure may have to do with the 1+1 getting turned into 2 when terms
;; ;; are built?  Simplify-defun should detect that the 2 passed to tool2-fn is
;; ;; already different than the 1+1 in the original function and set the
;; ;; MUST-REWRITE-FLG to false to suppress the error.
;; (deftest
;;   (defun bar () (+ 1 1))
;;   (simplify-defun bar))
