; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file was initially based closely on simplify-body-tests.lisp.

; Since the official transformation is simplify, most of the tests here call
; simplify even though this file is about simplifying defun forms, not defun-sk
; forms.  We let a few of the initial ones call simplify-defun just to test
; that simplify-defun continues to work.

; The section at the end is surely out of date, but gives some idea about how
; simplify-defun works.

(in-package "ACL2")

(include-book "simplify")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

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
    (DEFUN FOO$1 (X) (+ 2 X))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;;as above, but testing :eval on the required (first) argument
(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (simplify-defun (:eval (car '(foo))))
  (must-be-redundant
    (DEFUN FOO$1 (X) (+ 2 X))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;;test show-simplify-defun
(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (must-succeed (show-simplify-defun foo))
  (must-succeed (simplify-defun foo :show-only t))
  (must-succeed (show-simplify foo))
  (must-succeed (simplify foo :show-only t)))

; Check that we avoid a name clash for not-normalized function.  This test
; failed until we started using install-not-normalized-event etc. on 5/16/2018.
(deftest
  (defun foo (x) (+ 1 1 x))
  (defun foo$not-normalized (y) (cons y y))
  (simplify foo))

;;simple example of a recursive function
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify bar)
  (must-be-redundant
    (DEFUND BAR$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (ZP X) 0 (+ 2 (BAR$1 (+ -1 X)))))
    (DEFTHM BAR-BECOMES-BAR$1
      (EQUAL (BAR X) (BAR$1 X)))))

;;same as above, but test :thm-name and :new-name arguments, test
;;that results are suitably disabled, and test :print nil (well, not
;;much of a test unless we look at the result!).
(deftest
  (defund bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify bar
            :new-name bar-simp
            :thm-name bar-simplified
            :thm-enable nil
            :print nil)
  (assert-event (disabledp 'bar-simp)) ;disabled because bar is disabled
  (assert-event (disabledp 'bar-simplified))
  (must-be-redundant
    (DEFUND BAR-SIMP (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;;same as above, but create enabled definitions
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify bar
            :new-name bar-simp
            :thm-name bar-simplified)
  (assert-event (not (disabledp 'bar-simp))) ;not disabled because bar is not disabled
  (assert-event (not (disabledp 'bar-simplified)))
  (must-be-redundant
    (DEFUN BAR-SIMP (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;;same as above, but test :new-enable
(deftest
  (defun bar (x) (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify bar
            :new-name bar-simp
            :thm-name bar-simplified
            :new-enable nil
            :thm-enable t)
  (assert-event (disabledp 'bar-simp))
  (assert-event (not (disabledp 'bar-simplified)))
  (must-be-redundant
    (DEFUN BAR-SIMP (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (ZP X)
          0
          (+ 2 (BAR-SIMP (+ -1 X)))))
    (DEFTHM BAR-simplified
      (EQUAL (BAR X) (bar-simp X)))))

;; Test with :assumptions and a non-recursive function
(deftest
  (defun foo (x)
    (ifix x))
  (simplify foo :assumptions ((integerp x)))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      X)
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGERP X)
               (EQUAL (FOO X) (FOO$1 X))))))

;; As above, but evaluating assumptions
(deftest
  (defun foo (x)
    (ifix x))
  (simplify foo :assumptions (:eval (list '(integerp x))))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL ))
      X)
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGERP X)
               (EQUAL (FOO X) (FOO$1 X))))))

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
  (simplify foo :assumptions ((integer-listp x))
; Rules used to simplify the body:
                 :theory '(ifix integerp-of-car)
; Rules used to prove that the assumptions still hold on the recursive call:
                 :hints ; Find simpler :hints syntax in the next test.
                 (:assumptions-preserved
                  (("Goal" :in-theory '(INTEGER-LISTP-of-cdr))))
                 )
  (must-be-redundant

;;; OBSOLETE Comment from Matt K. (now that simplify uses
;;; directed-untranslate):

;;; The original version below, commented out, may be prettier; perhaps I
;;; should change simplify-defun to call reconstruct-macros-in-term, as
;;; does the original simplify-body.  However, here is an argument for why it
;;; might be better to avoid that utility.  Suppose we instead define foo as
;;; follows (logically equivalent, for what it's worth, to the foo just above):
;;; (defun foo (x) (if (consp x) (cons (ifix (first x)) (foo (rest x))) nil)).
;;; Then when we run the original simplify-body exactly as below, the resulting
;;; body is as follows.

;;;   (AND (CONSP X) (CONS (CAR X) (FOO$1 (CDR X))))

;;; The task of deciding whether or not the result should have AND probably
;;; needs to consider not only the translated simplified body, but also the
;;; original untranslated body.  That seems potentially messy.  Moreover, if
;;; the final result isn't more or less "perfect" (whatever that means), then
;;; it may confuse more than it helps because of the unpredictability.  If we
;;; avoid trying to reconstruct, then at least the final result is predictably
;;; something that is returned by untranslate.

    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (if (ATOM X) ;the ifix here gets dropped!
          NIL
        (CONS (CAR X) (FOO$1 (REST X)))))

   (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGER-LISTP x)
               (EQUAL (FOO X) (FOO$1 X))))))

; Same as above, with simpler syntax for :hints.  Comments are deleted below.
(deftest
  (defun foo (x)
    (if (atom x)
        nil
      (cons (ifix (first x))
            (foo (rest x)))))
  (simplify foo
            :assumptions ((integer-listp x))
            :theory '(ifix integerp-of-car)
            :hints (("Goal" :in-theory '(INTEGER-LISTP-of-cdr))))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (if (ATOM X) ;the ifix here gets dropped!
          NIL
        (CONS (CAR X) (FOO$1 (REST X)))))

   (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGER-LISTP x)
               (EQUAL (FOO X) (FOO$1 X))))))

; Same as above, with a computed hint.
(deftest
  (defun foo (x)
    (if (atom x)
        nil
      (cons (ifix (first x))
            (foo (rest x)))))
  (simplify foo
            :assumptions ((integer-listp x))
            :theory '(ifix integerp-of-car)
            :hints ('(:in-theory '(INTEGER-LISTP-of-cdr))))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (if (ATOM X) ;the ifix here gets dropped!
          NIL
        (CONS (CAR X) (FOO$1 (REST X)))))

   (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGER-LISTP x)
               (EQUAL (FOO X) (FOO$1 X))))))

;; Test of mutual recursion (simplifies all functions in the nest)
(deftest
  (mutual-recursion
   (defun foo (x) (if (atom x) (+ 1 1) (cons (ffn-symb x) (foo-lst (rest x)))))
   (defun foo-lst (x)
     (if (atom x)
         nil
       (cons (+ 1 2 (foo (first x)))
             (foo-lst (rest x))))))
  (simplify foo)
  (must-be-redundant
    (MUTUAL-RECURSION
     (DEFUN FOO$1 (X)
       (DECLARE (XARGS :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           2
           (CONS (FFN-SYMB X) (FOO-LST$1 (REST X)))))
     (DEFUN FOO-LST$1 (X)
       (DECLARE (XARGS :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           NIL
           (CONS (+ 3 (FOO$1 (CAR X)))
                 (FOO-LST$1 (REST X))))))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))
    (DEFTHM FOO-LST-BECOMES-FOO-LST$1
      (EQUAL (FOO-LST X) (FOO-LST$1 X)))))

;; As above, but specify the simplification of only one function
(deftest
  (mutual-recursion
   (defun foo (x) (if (atom x) (+ 1 1) (cons (ffn-symb x) (foo-lst (rest x)))))
   (defun foo-lst (x)
     (if (atom x)
         nil
       (cons (+ 1 2 (foo (first x)))
             (foo-lst (rest x))))))
  (simplify foo :simplify-body (:map (foo t) (foo-lst nil)))
  (must-be-redundant
    (MUTUAL-RECURSION
     (DEFUN FOO$1 (X)
       (DECLARE (XARGS :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           2
           (CONS (FFN-SYMB X) (FOO-LST$1 (REST X)))))
     (DEFUN FOO-LST$1 (X)
       (DECLARE (XARGS :GUARD T
                       :MEASURE (ACL2-COUNT X)
                       :VERIFY-GUARDS NIL))
       (IF (ATOM X)
           NIL
           (CONS (+ 1 2 (FOO$1 (FIRST X)))
                 (FOO-LST$1 (REST X))))))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))
    (DEFTHM FOO-LST-BECOMES-FOO-LST$1
      (EQUAL (FOO-LST X) (FOO-LST$1 X)))))

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
  (simplify f1 :assumptions ((integer-listp x)))
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (CONS (CAR X)
                (F2$1 (CDR X)))
          NIL))
    (DEFUN F2$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (CONS (CAR X)
                (F1$1 (CDR X)))
          NIL)))
   (DEFTHM F1-BECOMES-F1$1
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F1 X) (F1$1 X))))
   (DEFTHM F2-BECOMES-F2$1
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F2 X) (F2$1 X))))))

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
  (simplify f1
            :assumptions
; As a test, we switch the order of keys in the :map alist from clique order.
            (:map (f2 ((integer-listp x))) (f1 nil)))
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F1$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (AND (CONSP X) (INTEGER-LISTP X))
                           (CONS (CAR X) (F2$1 (CDR X)))
                           NIL))
                     (DEFUN F2$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (CONSP X)
                           (CONS (CAR X) (F1$1 (CDR X)))
                           NIL)))
   (DEFTHM F1-BECOMES-F1$1
     (EQUAL (F1 X) (F1$1 X)))
   (DEFTHM F2-BECOMES-F2$1
     (IMPLIES (INTEGER-LISTP X)
              (EQUAL (F2 X) (F2$1 X))))))

; Mutual-recursion with more than one recursive call in the same function.
(deftest
  (mutual-recursion
   (defun f1 (x)
     (cond ((endp x) nil)
           ((< 10 (car x))
            (cons (+ 1 -1 (car x))
                  (f2 (cdr x))))
           (t
            (cons (car x)
                  (f1 (cddr x))))))
   (defun f2 (x)
     (if (consp x)
         (cons (+ -1 1 (car x)) (f1 (cdr x)))
       nil)))
; The following rule from community book centaur/fty/baselists.lisp was present
; when this test was developed, but later disappeared; so now we include it
; explicitly.
  (defthm acl2-numberp-of-car-when-acl2-number-listp
    (implies (acl2-number-listp x)
             (iff (acl2-numberp (car x)) (consp x))))
  (simplify f1
            :assumptions ((rational-listp x)))
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F1$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (COND ((ENDP X) NIL)
                             ((< 10 (CAR X))
                              (CONS (CAR X) (F2$1 (CDR X))))
                             (T (CONS (CAR X) (F1$1 (CDDR X))))))
                     (DEFUN F2$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (CONSP X)
                           (CONS (CAR X) (F1$1 (CDR X)))
                           NIL)))
   (DEFTHM F1-BECOMES-F1$1
     (IMPLIES (RATIONAL-LISTP X)
              (EQUAL (F1 X) (F1$1 X))))
   (DEFTHM F2-BECOMES-F2$1
     (IMPLIES (RATIONAL-LISTP X)
              (EQUAL (F2 X) (F2$1 X))))))

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
  (simplify f1
            :simplify-body (:map ((f2 f3) nil)
                                 (f5 (cons x @))
                                 (:otherwise t)))
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X) (F2$1 (CDR X)) X))
    (DEFUN F2$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F3$1 (CDR X))
          (CAR (CONS X (CAR (CONS X X))))))
    (DEFUN F3$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F4$1 (CDR X))
          (CAR (CONS X (CAR (CONS X X))))))
    (DEFUN F4$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X) (F5$1 (CDR X)) X))
    (DEFUN F5$1 (X)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (F1$1 (CDR X))
          (CAR (CONS X X)))))
   (DEFTHM F1-BECOMES-F1$1 (EQUAL (F1 X) (F1$1 X)))
   (DEFTHM F2-BECOMES-F2$1 (EQUAL (F2 X) (F2$1 X)))
   (DEFTHM F3-BECOMES-F3$1 (EQUAL (F3 X) (F3$1 X)))
   (DEFTHM F4-BECOMES-F4$1 (EQUAL (F4 X) (F4$1 X)))
   (DEFTHM F5-BECOMES-F5$1 (EQUAL (F5 X) (F5$1 X)))))

; :Map fails for :verify-guards and :non-executable

(deftest
  (mutual-recursion
   (defun f1 (x)
     (if (consp x)
         (f2 (cdr x))
       (car (cons x (car (cons x x))))))
   (defun f2 (x)
     (if (consp x)
         (f1 (cdr x))
       (car (cons x (car (cons x x)))))))
  (must-fail
   (simplify f1 :verify-guards (:map (f1 t) (f2 nil))))
  (must-fail
   (simplify f1 :non-executable (:map (f1 t) (f2 nil))))
; Just to make sure there's no dumb syntax error above.
  (simplify f1 :untranslate (:map (f1 t) (f2 nil))))

(deftest
  (mutual-recursion
   (defun f1 (x y)
     (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
     (if (or (consp x) (consp y))
         (f2 (cdr x) (cdr y))
       (list x y)))
   (defun f2 (x y)
     (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
     (if (or (consp x) (consp y))
         (f1 (cdr x) (cdr y))
       (list x y))))
  (must-fail ; check manually
   (simplify f1))
  (simplify f1 :must-simplify nil)
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1$1 (X Y)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (+ (ACL2-COUNT X) (ACL2-COUNT Y))
                      :VERIFY-GUARDS NIL))
      (IF (OR (CONSP X) (CONSP Y))
          (F2$1 (CDR X) (CDR Y))
          (LIST X Y)))
    (DEFUN F2$1 (X Y)
      (DECLARE (XARGS :GUARD T
                      :MEASURE (+ (ACL2-COUNT X) (ACL2-COUNT Y))
                      :VERIFY-GUARDS NIL))
      (IF (OR (CONSP X) (CONSP Y))
          (F1$1 (CDR X) (CDR Y))
          (LIST X Y))))))

; Specify that no simplification is done
(deftest

  (defun foo (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (foo (cdr x))
      (car (cons x x))))

  (simplify foo
            :simplify-body nil
            :simplify-guard nil
            :simplify-measure nil)

  (must-be-redundant
    (DEFUND FOO$1 (X)
      (DECLARE (XARGS :GUARD (AND (TRUE-LISTP X) (NOT (ATOM X)))
                      :MEASURE (FIX (LEN X))
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X))
          (FOO$1 (CDR X))
          (CAR (CONS X X))))))

;; test of :enable
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify foo :enable (double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; test of :enable with just a symbol
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify foo :enable double)
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; test of :enable with multiple rules
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify foo :enable (double natp))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

; simple test of :theory
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify foo :theory '(double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

; another test of :theory
(deftest
  (defun foo (x) (+ x x))
  (defthmd double
    (equal (+ x x) (* 2 x)))
  (simplify foo :theory (enable double))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; test of :enable and :disable
(deftest
  (defun foo (x) (+ x x))
  (defthmd double-good
    (equal (+ x x) (* 2 x)))
  (defthm double-bad
    (equal (+ x x) (+ 0 (* 2 x))))
  (simplify foo :enable (double-good) :disable (double-bad))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; reverse of previous test
(deftest
  (defun foo (x) (+ x x))
  (defund zerofn (x) (declare (ignore x)) 0)
  (defthm double-good
    (equal (+ x x) (* 2 x)))
  (defthmd double-bad
    (equal (+ x x) (+ (zerofn x) (* 2 x))))
  (simplify foo :enable (double-bad) :disable (double-good))
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (+  (zerofn x) (* 2 X)))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; as for test before last, but using rulesets
(deftest
  (defun foo (x) (+ x x))
  (defthmd double-good
    (equal (+ x x) (* 2 x)))
  (defthm double-bad
    (equal (+ x x) (+ 0 (* 2 x))))
  (def-ruleset my-enables '(double-good))
  (def-ruleset my-disables '(double-bad))
  (simplify foo :enable my-enables :disable my-disables)
  ;; Expected result:
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (* 2 X))
    (DEFTHM
      FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;; test of :enable nil:
(deftest
  (defun foo (x) (car (cons x x)))
  (simplify foo :enable nil)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     X)))

;; Test where the assumption is hidden inside a function call that we expand
;; before simplifying:
(deftest
  (defund integerp-wrapper (x) (integerp x)) ;this gets expanded below
  (defun foo (x)
    (ifix x))
  (simplify foo
            :assumptions ((integerp-wrapper x))
            :enable (integerp-wrapper))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL ))
      X)
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGERP-wrapper X) ;the unsimplified assumption
               (EQUAL (FOO X)
                      (FOO$1 X))))))


;; Test a bad argument to :theory (causes an error in tool2, which we catch):
(deftest
  (must-fail (simplify natp :theory '(((f)))))
)

;; Test simplification with respect to use of guard as the assumptions.
(deftest

  (defun foo (x)
    (declare (xargs :guard (true-listp x)))
    (if (consp x)
        (foo (cdr x))
      x))

  (simplify foo :assumptions :guard)

  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE
       (XARGS :GUARD (TRUE-LISTP X)
              :MEASURE (ACL2-COUNT X)
              :VERIFY-GUARDS T))
      (IF (CONSP X)
          (FOO$1 (CDR X))
        NIL))
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (TRUE-LISTP X)
               (EQUAL (FOO X) (FOO$1 X))))))

;; As above, but here we have :guard as a member of the :assumptions.
(deftest

  (defun foo (x y)
    (declare (xargs :guard (true-listp x)))
    (if (consp x)
        (foo (cdr x) y)
      (cons y x)))

  (simplify foo :assumptions ((consp y) :guard))

  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE
       (XARGS :GUARD (TRUE-LISTP X)
              :MEASURE (ACL2-COUNT X)
              :VERIFY-GUARDS T))
      (IF (CONSP X)
          (FOO$1 (CDR X) Y)
        (CONS Y NIL)))
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (AND (CONSP Y)
                    (TRUE-LISTP X))
               (EQUAL (FOO X Y) (FOO$1 X Y))))))

;; As above, but here we rely on the old guard-theorem in order for the proof
;; to succeed.
(deftest

  (defun my-cdr (x)
    (declare (xargs :guard (listp x)))
    (cdr x))

  (defun foo (x)
    (declare (xargs :guard (true-listp x)))
    (if (consp x)
        (foo (my-cdr x))
      x))

  (in-theory (disable my-cdr (tau-system)))

  (must-fail (simplify foo :assumptions ((true-listp x))))

; The following is equivalent to what's just above, except that with the use of
; :guard we get a hint to :use the :guard-theorem of foo.

  (simplify foo :assumptions :guard)

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD (TRUE-LISTP X)
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (IF (CONSP X) (FOO$1 (MY-CDR X)) NIL))
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (TRUE-LISTP X)
               (EQUAL (FOO X) (FOO$1 X))))))

;; Test :verify-guards.

;; First, test default for :verify-guards (two tests).
(deftest

  (defun foo (x)
    (car (cons x x)))

  (simplify foo)

  (assert-event (eq (symbol-class 'foo$1 (w state)) :ideal)))

(deftest

  (defun foo (x)
    (declare (xargs :verify-guards t))
    (car (cons x x)))

  (simplify foo)

  (assert-event (eq (symbol-class 'foo$1 (w state)) :common-lisp-compliant)))

;; Next, test :verify-guards t.
(deftest

  (defun foo (x)
    (declare (xargs :verify-guards nil))
    (car (cons x x)))

  (simplify foo :verify-guards t)

  (assert-event (eq (symbol-class 'foo$1 (w state)) :common-lisp-compliant)))

;; Finally, test :verify-guards nil.
(deftest

  (defun foo (x)
    (declare (xargs :verify-guards t))
    (car (cons x x)))

  (simplify foo :verify-guards nil)

  (assert-event (eq (symbol-class 'foo$1 (w state)) :ideal)))

;; Test error from :?.  Error should say the following, though we don't
;; actually test for that here.
#||
ACL2 Error in (APT::SIMPLIFY FOO ...):  Simplify has been called on
function FOO, with the default value :AUTO for :MEASURE.  This is illegal
because the existing definition of FOO uses a measure that is a call
of :?, namely, (:? X).
||#
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

  (must-fail (simplify foo)))

;; Basic test of simplifying guard and measure
(deftest

  (defun foo (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (foo (cdr x))
      x))

  (simplify foo
            :simplify-body nil
            :simplify-guard t
            :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO$1 (X)
      (DECLARE (XARGS :GUARD (AND (TRUE-LISTP X) (CONSP X))
                      :MEASURE (LEN X)
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X)) (FOO$1 (CDR X)) X)))

  (defun bar (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (bar (cdr x))
      x))

  (must-fail ; attempt fails to simplify the body
   (simplify bar
             :simplify-guard t
             :simplify-measure t))

  (simplify bar
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

  (simplify foo
            :simplify-body nil
            :simplify-guard t
            :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO$1 (X)
      (DECLARE (XARGS :GUARD (AND (TRUE-LISTP X) (CONSP X))
                      :MEASURE (LEN X)
                      :VERIFY-GUARDS T))
      (IF (CONSP (CDR X)) (FOO$1 (CDR X)) X)))

  (defun bar (x)
    (declare (xargs :guard (and (true-listp x)
                                (not (atom x)))
                    :measure (fix (len x))))
    (if (consp (cdr x))
        (bar (cdr x))
      x))

  (must-fail ; attempt fails to simplify the body
   (simplify bar
             :must-simplify (:body t)
             :simplify-guard t
             :simplify-measure t))

  (simplify bar
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

  (simplify foo
            :assumptions :guard
            :simplify-guard t
            :simplify-measure t)

  (must-be-redundant
    (DEFUND FOO$1 (X)
      (DECLARE (XARGS :GUARD (AND (INTEGERP X) (NOT (< X 0)))
                      :MEASURE (IF (INTEGERP X) (IF (< X 0) 0 X) 0)
                      :VERIFY-GUARDS T))
      (IF (ZP X) 0 (FOO$1 (1- X))))))

;; Let's test the use of a pattern for :simplify-body.  Here we also test the
;; use of :normalize nil.

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

  (simplify foo
            :assumptions ((p0 x)))

  (simplify foo
            :assumptions ((p0 x))
            :simplify-body (if (p2a x) (cons x x) @))

  (must-be-redundant

    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (G (IF (P1 X)
             (G (IF (P2 X) (CONS X X) X))
             (CONS X X))))

    (DEFUN FOO$2 (X)
      (DECLARE (XARGS :NORMALIZE NIL
                      :GUARD T
                      :VERIFY-GUARDS NIL))
      (G (IF (P1 X)
             (G (IF (P2A X) (CONS X X) X))
             (CONS X X))))))

; Simple test of :normalize xarg.

(deftest
  (mutual-recursion ; based on :doc mutual-recursion
   (defun f1 (x)
     (declare (xargs :normalize nil))
     (if (consp x)
         (f2 (if (natp (car x)) (cdr x) (cddr x)))
       t))
   (defun f2 (x)
     (declare (xargs :normalize t))
     (if (consp x)
         (f3 (if (natp (car x)) (cdr x) (cddr x)))
       nil))
   (defun f3 (x)
     (if (consp x)
         (f1 (if (natp (car x)) (cdr x) (cddr x)))
       nil)))
  (simplify f1)
  (must-be-redundant
   (MUTUAL-RECURSION
    (DEFUN F1$1 (X)
           (DECLARE (XARGS :NORMALIZE NIL
                           :GUARD T
                           :MEASURE (ACL2-COUNT X)
                           :VERIFY-GUARDS NIL))
           (IF (CONSP X)
               (F2$1 (IF (AND (INTEGERP (CAR X))
                              (NOT (< (CAR X) 0)))
                         (CDR X)
                         (CDDR X)))
               T))
    (DEFUN F2$1 (X)
           (DECLARE (XARGS :NORMALIZE T
                           :GUARD T
                           :MEASURE (ACL2-COUNT X)
                           :VERIFY-GUARDS NIL))
           (IF (CONSP X)
               (F3$1 (IF (AND (INTEGERP (CAR X))
                              (NOT (< (CAR X) 0)))
                         (CDR X)
                         (CDDR X)))
               NIL))
    (DEFUN F3$1 (X)
           (DECLARE (XARGS :GUARD T
                           :MEASURE (ACL2-COUNT X)
                           :VERIFY-GUARDS NIL))
           (IF (CONSP X)
               (F1$1 (IF (AND (INTEGERP (CAR X))
                              (NOT (< (CAR X) 0)))
                         (CDR X)
                         (CDDR X)))
               NIL)))))

; Simple test with pattern that failed before fixing fn-is-fn-copy to use
; install-not-normalized-name in its hint:

(deftest
  (defun foo (x) (cons x x))
  (defun bar (x) (cons x x))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo y) (bar y) z)))
  (simplify f
            :simplify-body (if (foo x) @ z))
  (must-be-redundant
    (DEFUN F$1 (X Y Z)
      (DECLARE (XARGS :GUARD T
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
  (simplify f
            :simplify-body (if (foo x) @ z)))

(deftest
  (defun foo (x) x)
  (defun bar (x) (if x (cons x x) 17))
  (defun f (x y z)
    (cons (if (foo x) (bar x) z)
          (if (foo x) (foo y) z)))
; Note that (foo x) is not an instance of (foo a) by instantiating only @-vars
; and _-vars.
  (must-fail (simplify f
                       :simplify-body (if (foo a) @ z)))
  (simplify f
            :simplify-body (if (foo _a) @ _b))
  (must-be-redundant
    (DEFUN F$1 (X Y Z)
      (DECLARE (XARGS :GUARD T
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
  (simplify f
            :simplify-body (if (foo _) @ _))
  (must-be-redundant
    (DEFUN F$1 (X Y Z)
      (DECLARE (XARGS :GUARD T
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
  (simplify f
            :simplify-body (if @ t nil))
  (must-be-redundant
    (DEFUN F$1 (A)
      (DECLARE (XARGS :GUARD T))
      (IF T T NIL))))

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
  (simplify f
            :simplify-body (my-if @ t nil))
  (must-be-redundant
    (DEFUN F$1 (A)
      (DECLARE (XARGS :GUARD T))
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
  (simplify-defun foo
                  :simplify-body nil :simplify-guard t :verify-guards nil

; We enable the blocker for ec-call so that the rule member-fix-true-listp can
; fire.

                  :enable ec-call-fn)
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :GUARD (MEMBER-EQUAL X Y)
                      :VERIFY-GUARDS NIL))
      (CONS X Y))))

; Test of delaying verify-guards until after the "becomes" theorem.
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
  (in-theory (disable my-cdr my-consp (tau-system)))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (IF (CONSP X)
         (IF (MY-CONSP (F1$1 (CDR X)))
             (F1$1 (MY-CDR X))
             X)
         X))))

; Another test of delaying verify-guards until after the "becomes" theorem.
(deftest
  (defstub clausep (x) t)
  (DEFUN ALL-CLAUSEP (X)
    (declare (xargs :guard t))
    (IF (ATOM X)
        T
        (AND (CLAUSEP (FIRST X))
             (ALL-CLAUSEP (REST X)))))
  (DEFUN ADD-TO-CLAUSE-SET (CLAUSE CLAUSE-LIST)
    (DECLARE (XARGS :GUARD (AND (CLAUSEP CLAUSE)
                                (true-listp CLAUSE-LIST)
                                (all-clausep CLAUSE-LIST))))
    (IF (member-equal CLAUSE CLAUSE-LIST)
        CLAUSE-LIST
        (CONS CLAUSE CLAUSE-LIST)))
  (DEFUN UNION-CLAUSE-SETS
    (CLAUSE-SET1 CLAUSE-SET2)
    (DECLARE (XARGS :GUARD (AND (all-clausep CLAUSE-SET1)
                                (true-listp CLAUSE-set1)
                                (all-clausep CLAUSE-SET2)
                                (true-listp CLAUSE-set2))))
    (IF (ENDP CLAUSE-SET1)
        CLAUSE-SET2
        (ADD-TO-CLAUSE-SET (FIRST CLAUSE-SET1)
                           (UNION-CLAUSE-SETS (REST CLAUSE-SET1)
                                              CLAUSE-SET2))))

  ;;This previously failed in guard verification (because the
  ;;guard-theorem of UNION-CLAUSE-SETS mentions UNION-CLAUSE-SETS):
  (simplify UNION-CLAUSE-SETS))

; The following test originally tested :guard-hints, but now, guard
; verification succeeds where formerly it failed without those hints; and
; that's actually fine.  An enabled, earlier "becomes" lemma was causing guard
; verification to fail, but now that guard verification only enables *f1-runes*
; (at least, that's what it tries first), it succeeds.
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
            (cons (car x) (f1 (my-cdr x)))
          x)
      x))
  (defthm f1-id
    (equal (f1 x)
           x))
  (in-theory (disable my-consp my-cdr (tau-system)))
  (simplify f1
            :guard-hints
            (("Goal" :in-theory (enable my-cdr my-consp))))
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (IF (CONSP X)
         (IF (MY-CONSP (CDR X))
             (CONS (CAR X) (MY-CDR X))
             X)
         X))))

; Test of :guard-hints -- unlike the preceding test, we need :guard-hints
; because the original function, f1, is not guard-verified, so we can't use its
; guard-theorem.
(deftest
  (defun my-consp (x)
    (declare (xargs :guard t))
    (consp x))
  (defun my-cdr (x)
    (declare (xargs :guard (my-consp x)))
    (cdr x))
  (defun f1 (x)
    (if (consp x)
        (if (my-consp (f1 (cdr x)))
            (cons (car x) (f1 (my-cdr x)))
          x)
      x))
  (defthm f1-id
    (equal (f1 x)
           x))
  (in-theory (disable my-consp my-cdr (tau-system)))
  (must-fail (simplify f1 :verify-guards t))
  (simplify f1
            :verify-guards t
            :guard-hints
            (("Goal" :in-theory (enable my-cdr my-consp))))
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (IF (CONSP X)
         (IF (MY-CONSP (CDR X))
             (CONS (CAR X) (MY-CDR X))
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
  (simplify foo ; fails (takes awhile) without the following:
            :measure-hints (("Goal" :in-theory (enable k))))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT X)
                      :VERIFY-GUARDS NIL))
      (IF (CONSP X)
          (FOO$1 (K (CDR X) (FOO$1 (CDR X) Y)) Y)
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
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @1)
                                            _1
                                            (* _1 5 @2))))
; @-variables other than @ must be distinct for matches to different terms:
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @1)
                                            _
                                            (* 4 5 @1))))
; This one is fine.
  (simplify foo
            :simplify-body (list (* 3 @1)
                                 _1
                                 (* _2 5 @2)))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :RULER-EXTENDERS :ALL
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
  (simplify foo
            :simplify-body (list (* 3 @)
                                 _1
                                 (* _2 5 @)))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :RULER-EXTENDERS :ALL
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
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @1)
                                            _a
                                            (* _a 5 @2))))
; @-vars other than @ must be distinct for matches to different terms, and we
; want a suitable error message about that even if matching fails:
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @a)
                                            @a
                                            _)))
; This one is fine.
  (simplify foo
            :simplify-body (list (* 3 @1)
                                 _1
                                 (* _2 5 @2)))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :GUARD T
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
  (simplify foo
            :simplify-body (list (* 3 @)
                                 _1
                                 (* _2 5 @)))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :GUARD T
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
  (simplify foo
            :simplify-body (if _1
                               (foo (list @1 _2)
                                    _3)
                             (cons _4 (* _5 _6 @2))))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT Y)
                      :VERIFY-GUARDS NIL))
      (LIST (LIST
             (IF (CONSP Y)
                 (FOO$1 (LIST (+ 6 (* 3 X))
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
  (simplify foo
            :simplify-body (if _1
                               (foo (list @1 _2)
                                    _3)
                             (cons _4 (* _5 _6 @2))))
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :RULER-EXTENDERS :ALL
                      :GUARD T
                      :MEASURE (ACL2-COUNT Y)
                      :VERIFY-GUARDS NIL))
      (LIST (LIST
             (IF (CONSP Y)
                 (FOO$1 (LIST (+ 6 (* 3 X))
                              (* 4 (+ 1 1 (CAR Y))))
                        (CDR Y))
                 (CONS X (* 5 6 (+ 2 Y)))))))))

; Some tests of handling by directed-untranslate of iff flag, OR, IMPLIES,
; COND, <= etc., perhaps more.
(deftest
  (defun f1a (x z)
    (not (or (car (cons x x)) z)))
  (simplify f1a)
  (must-be-redundant
   (DEFUN F1a$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun f1b (x z)
    (not (if (car (cons x x)) (car (cons x x)) z)))
  (simplify f1b)
  (must-be-redundant ; avoid OR; test iff-flg = t under NOT
   (DEFUN F1B$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (IF X T Z))))
  (defun f1c (x z)
    (not (if (car (cons x x)) t z)))
  (simplify f1c)
  (must-be-redundant
   (DEFUN F1C$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (IF X T Z))))
  (defun f2 (x y)
    (implies (car (cons x x)) y))
  (simplify f2)
  (must-be-redundant ; untranslating (IF X (IF Y 'T 'NIL) 'T)
   (DEFUN F2$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES X Y)))
  (defun f3 (x y)
    (implies (car (cons x x)) (not y)))
  (simplify f3)
  (must-be-redundant ; interesting case, seen with (trace$ directed-untranslate-rec)
   (DEFUN F3$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES X (NOT Y))))
  (defun f4 (x y)
    (implies (not (car (cons x x))) y))
  (simplify f4)
  (must-be-redundant ; directed-untranslate handles (if x 't (if y 't 'nil))
   (DEFUN F4$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IMPLIES (NOT X) Y)))
  (defun f5a (x y z)
    (cond ((consp x) y)
          (t (car (cons z z)))))
  (simplify f5a)
  (must-be-redundant
   (DEFUN F5A$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (COND ((CONSP X) Y) (T Z))))
  (defun f5b (x y z)
    (if (consp x)
        y
      (car (cons z z))))
  (simplify f5b)
  (must-be-redundant
   (DEFUN F5B$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) Y Z)))
  (defun f6 (x y z)
    (cond ((consp x) y)
          ((consp y) x)
          (t (car (cons z z)))))
  (simplify f6)
  (must-be-redundant
   (DEFUN F6$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (COND ((CONSP X) Y)
           ((CONSP Y) X)
           (T Z))))
  (defun f7a (x y)
    (<= (car (cons x x)) y))
  (simplify f7a)
  (must-be-redundant
   (DEFUN F7A$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (<= X Y)))
  (defun f7b (x y) ; equivalent to f7a, but directed-untranslate should avoid <=
    (not (< y (car (cons x x)))))
  (simplify f7b)
  (must-be-redundant
   (DEFUN F7B$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (< Y X))))
  (defun f8a (x y)
    (>= (car (cons x x)) y))
  (simplify f8a)
  (must-be-redundant
   (DEFUN F8A$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (>= X Y)))
  (defun f8b (x y) ; equivalent to f7a, but directed-untranslate should avoid <=
    (not (< (car (cons x x)) y)))
  (simplify f8b)
  (must-be-redundant
   (DEFUN F8B$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (< X Y))))
  (defun f9a (x y)
    (> (car (cons x x)) y))
  (simplify f9a)
  (must-be-redundant
   (DEFUN F9A$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (> X Y)))
  (defun f9b (x y) ; equivalent to f9a, but directed-untranslate should avoid <=
    (< y (car (cons x x))))
  (simplify f9b)
  (must-be-redundant
   (DEFUN F9B$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (< Y X)))
; Avoid mistakes in macro handling.
  (defun f10a (x)
    (identity (car (cddr x))))
  (simplify f10a)
  (must-be-redundant ; tracking fails when identity is stripped off
   (DEFUN F10A$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CAR (CDR (CDR X)))))
  (defun f10b (x)
    (identity (car (cddr x))))
  (simplify f10b :untranslate t)
  (must-be-redundant
   (DEFUN F10B$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CADDR X)))
  (defun f11 (x)
    (cddr (caddar (car (cdar (identity (car (cddr x))))))))
  (simplify f11)
  (must-be-redundant ; as above, no hope for direction under expansion of identity call
   (DEFUN F11$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CDDR (CADDAR (CAR (CDAR (CAR (CDR (CDR X)))))))))

; The following should preserve (if z z w) rather than converting it to (or z
; w), but since the true and false branches are switched during simplification
; (as seen if you evaluate (trace$ tool2-fn) first), this requires a bit of
; care by directed-untranslate.
  (defun f12 (x y z w)
    (if (not x) (car (cons y y)) (if z z w)))
  (simplify f12)
  (must-be-redundant
   (DEFUN F12$1 (X Y Z W)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (NOT X) Y (IF Z Z W))))

; This definition drops a conjunct, where the conjunction is expressed using
; IF.  Without special handling for such cases, the result has < instead of the
; desired > .
  (defun f13 (x)
    (if (consp x)
        (if (not (atom x)) (> 3 (car x)) nil)
      nil))
  (simplify f13)
  (must-be-redundant
   (DEFUN F13$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (> 3 (CAR X)) NIL)))

; Here is another test of dropping conjuncts.
  (defun f14 (x y)
    (and (or (atom x) (consp x))
         (cons y nil)))
  (simplify f14)
  (must-be-redundant
   (DEFUN F14$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS Y NIL)))

; The next two are similar to those above, but involve disjunctions.
  (defun f13a (x)
    (if (consp x)
        (if (atom x) t (> 3 (car x)))
      nil))
  (simplify f13a)
  (must-be-redundant
   (DEFUN F13A$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (> 3 (CAR X)) NIL)))

  (defun f14a (x y)
    (or (and (atom x) (consp x))
        (cons y nil)))
  (simplify f14a)
  (must-be-redundant
   (DEFUN F14A$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS Y NIL))))

; Tests for :untranslate option
(deftest
  (defun g1 (x z)
    (not (or (car (cons x x)) z)))
  (simplify g1)
  (must-be-redundant
   (DEFUN G1$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun g2 (x z)
    (not (or (car (cons x x)) z)))
  (simplify g2 :untranslate t)
  (must-be-redundant
   (DEFUN G2$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (NOT (OR X Z))))
  (defun g3 (x z)
    (not (or (car (cons x x)) z)))
  (must-fail (simplify g3 :untranslate :bad-option))
  (simplify g3 :untranslate nil)
  (must-be-redundant
   (DEFUN G3$1 (X Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (IF X 'T Z) 'NIL 'T))))

; Require simplification even after untranslate: simplifies by expanding
; implies, but directed-untranslate puts back the implies.
(deftest
  (defun foo (x y)
    (implies x y))
  (must-fail (simplify foo)))

;;; Test :expand hints

(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify foo :expand (append x y))
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS 17
           (IF (CONSP X)
               (CONS (CAR X) (APPEND (CDR X) Y))
               Y)))))

; Same as above but slightly different :expand syntax.
(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify foo :expand ((append x y)))
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS 17
           (IF (CONSP X)
               (CONS (CAR X) (APPEND (CDR X) Y))
               Y)))))

; Same as above but wilder :expand hint.
(deftest
  (defun foo (x y)
    (cons 17 (append x y)))
  (simplify foo :expand ((:free (v) (append x v))))
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
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
  (simplify f1 :simplify-body (or @ _))
; And just for fun:
  (simplify f1 :simplify-body (or _ @))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR X (+ 1 1 Y)))
   (DEFUN F1$2 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR (CAR (CONS X Y)) (+ 2 Y)))
   (DEFUN F1$3 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR X (+ 2 Y))))

; Variant where the resulting (if a a b) simplifies to (if a t b).  This tests
; the ability to simplify the "a" in different contexts, since the second
; occurrences simplifies to T only in the context of the first.

  (defun f2 (x y)
    (or (car (cons (symbolp x) y))
        (+ 1 1 y)))
  (simplify f2 :simplify-body (or @ _))
; And just for fun:
  (simplify f2 :simplify-body (or _ @))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (SYMBOLP X) T (+ 1 1 Y)))
   (DEFUN F2$2 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (OR (CAR (CONS (SYMBOLP X) Y)) (+ 2 Y)))
   (DEFUN F2$3 (X Y)
     (DECLARE (XARGS :GUARD T
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
   (simplify f3 :simplify-body (if @a (if _b @a _b) _)))
  (simplify f3 :simplify-body (if @ (if _ @ _) _))
  (simplify f3 :simplify-body (if @a (if _ @a _) _))
  (must-be-redundant
   (DEFUN F3$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF X (IF (BOOLEANP X) T (CAR (CONS Y X)))
         (CONS Y Y)))
   (DEFUN F3$2 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF X (IF (BOOLEANP X) T (CAR (CONS Y X)))
         (CONS Y Y))))

; Check that the renaming of every @ avoids all other @-vars, even those that
; come after @.

  (defun f4 (x)
    (list (+ 1 1 x) (+ 1 1 x) (+ 3 4 x)))
  (simplify f4 :simplify-body (list @ @ @0))
  (must-be-redundant
   (DEFUN F4$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ 2 X) (+ 2 X) (+ 7 X))))
  (defun f5 (x)
    (list (+ 3 4 x) (+ 1 1 x) (+ 1 1 x)))
  (simplify f5 :simplify-body (list @0 @ @))
  (must-be-redundant
   (DEFUN F5$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ 7 X) (+ 2 X) (+ 2 X))))

; Check the renaming of dupliate @ occurrences doesn't happen after
; translation.

  (defun f6 (x)
    (if (rationalp (fix x)) (+ 1 1 x) x))

; The following formerly failed, because matching was implemented by renaming
; apart instances of @ only before translation.  Now it succeeds, because it is
; equivalent to the following form, which succeeded previously as well:
; (simplify f6 :simplify-body (if @ @ _))

  (simplify f6 :simplify-body (or @ _))

  (must-be-redundant
   (DEFUN F6$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (RATIONALP (IF (ACL2-NUMBERP X) X 0)) (+ 2 X) X))))

;;; Either expand away or preserve LET.

(deftest
  (defun f1 (x y)
    (cons (first y)
          (let ((z (first x)))
            (cons (first z) (car (cons y y))))))

  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS (FIRST Y)
           (LET ((Z (FIRST X)))
                (CONS (FIRST Z) Y)))))

  (simplify f1 :untranslate t)
  (must-be-redundant
   (DEFUN F1$2 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST* (CAR Y) (CAR (CAR X)) Y)))

  ;; now this one is redundant because :nice is the default:
  (must-be-redundant (simplify f1 :untranslate :nice))

  (simplify f1 :untranslate :nice-expanded)
  (must-be-redundant
   (DEFUN F1$3 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CONS (FIRST Y) (CONS (CAR (CAR X)) Y)))))

;; Test :non-executable

(deftest
  (defun f1 (x y)
    (mv x y))
  (defun-nx f2 (x)
    (car (f1 (car x) (cdr x))))
  (simplify f2)
  (must-be-redundant
   (DEFUN-NX F2$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (CAR X))))

;; At one point we tested here that prog2$ is retained.  Since that turned out
;; to be a bad idea (because the first argument might be invalid in the new
;; context, with different superior let-bindings), we instead define utilities
;; like prog2$ and cw$ that do the job.  (BUT see below this test -- now, on
;; 7/3/2018, I no longer see why retaining prog2$ is a bad idea as long as we
;; allow simplification of its first argument, and indeed we now can preserve
;; prog2$ and cw calls.)

(deftest
  (defun prog2$$ (x y)
    (declare (xargs :guard t :normalize nil))
    (prog2$ x y))
  (defun cw$-fn (str args) ; based on the definition of cw
    (declare (xargs :guard (true-listp args) :normalize nil))
    (fmt-to-comment-window str
                           (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                                       #\5 #\6 #\7 #\8 #\9)
                                     args)
                           0 nil nil))
  (in-theory (disable prog2$$ (:t prog2$$) (:e prog2$$)
                      cw$-fn (:t cw$-fn) (:e cw$-fn)))
; The following isn't necessary here but could be for the termination proof for
; a recursive definition.
  (add-default-hints '((quote (:in-theory (enable prog2$$)))))
  (defmacro cw$ (str &rest args)
    `(cw$-fn ,str (list ,@args)))
  (defun foo (x)
    (prog2$$ (cw$ "hello~%")
             (car (cons x x))))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (PROG2$$ (CW$ "hello~%") X))))

; Test retention of prog2$ and cw.  We test various combinations of quoted and
; unquoted arguments of cw (but probably inadequate untranslate of
; fmt-to-comment-window into cw won't be caught here -- manual inspection of
; results would be better).

(deftest
  (local (in-theory (disable prog2$-fn))) ; avoid blowing away prog2$
  (defun f1 (x)
    (prog2$ (cw "hello ~x0 ~x1~%" 'x 'y)
            (car (cons x x))))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (PROG2$ (CW "hello ~x0 ~x1~%" 'X 'Y) X)))

  (defun f2 (x)
    (prog2$ (cw "hello ~x0 ~x1~%" x 'y)
            (car (cons x x))))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (PROG2$ (CW "hello ~x0 ~x1~%" X 'Y) X)))

  (defun f3 (x)
    (prog2$ (cw "hello ~x0 ~x1~%" 'y x)
            (car (cons x x))))
  (simplify f3)
  (must-be-redundant
   (DEFUN F3$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (PROG2$ (CW "hello ~x0 ~x1~%" 'Y X) X)))

  (defun f4 (x)
    (prog2$ (cw "hello ~x0 ~x1~%" (car x) (cdr x))
            (car (cons x x))))
  (simplify f4)
  (must-be-redundant
   (DEFUN F4$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (PROG2$ (CW "hello ~x0 ~x1~%" (CAR X) (CDR X))
             X))))

; Similar to above, but using b*, and with :disable and :theory keyword
; arguments instead of in-theory event.

(deftest
  (defun f1 (x) (b* ((- (cw "hi")) (y x)) (car (cons y y))))
  (simplify f1 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "hi")) (Y X)) Y)))

  (defun f2 (x) (b* ((- (cw "hi")) (y x)) (car (cons y y))))
  (simplify f2 :disable return-last-blockers)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "hi")) (Y X)) Y)))

  (defun f3 (x) (b* ((- (cw "hi")) (y x)) (car (cons y y))))
  (simplify f3 :theory (disable prog2$-fn))
  (must-be-redundant
   (DEFUN F3$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "hi")) (Y X)) Y)))

  (defun f4 (x) (b* ((- (cw "hi")) (y x)) (car (cons y y))))
  (simplify f4 :theory (disable return-last-blockers))
  (must-be-redundant
   (DEFUN F4$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "hi")) (Y X)) Y))))

; The tests just above passed even before we started ensuring that
; directed-untranslate-rec is called on the arguments for calls of prog2$ and
; mbe, and before we properly handled progn$ by treating the case (progn$ &)
; correctly.  The following tests rely on all of these.

(deftest

; mbe
  (defun f1 (x)
    (mbe :logic (list* (first x) (car (cons nil x)))
         :exec (list (nth 0 x))))
  (simplify f1 :disable mbe-fn)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (MBE :LOGIC (LIST* (FIRST X) NIL)
          :EXEC (LIST (AND (CONSP X) (CAR X))))))

; cw
  (defun f2 (x y)
    (cw "Ouch ~x0 ~x1"
        (list* (first x) (car (cons nil x)))
        (car (cons y y))))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (CW "Ouch ~x0 ~x1" (LIST* (FIRST X) NIL)
         Y)))

; progn$
  (defun f3 (x)
    (progn$ (cw "hi")
            (list* (first x) (car (cons nil x)))))
  (simplify f3 :disable prog2$-fn)
  (DEFUN F3$1 (X)
    (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
    (PROGN$ (CW "hi")
            (LIST* (FIRST X) NIL)))

; progn$, mbe, and cw together
  (defun f4 (x y)
    (progn$
     (cw "Ouch ~x0 ~x1"
         (list* (first x) (car (cons nil x)))
         (mbe :logic (list* (first y) (cdr (list x)))
              :exec (prog2$ (cw "Hi ~s0" (car (cons 'there y)))
                            y)))
     (mbe :logic (list* (first x) (car (cons nil x)))
          :exec (list (nth 0 x)))))
  (simplify f4 :disable (mbe-fn prog2$-fn))
  (DEFUN F4$1 (X Y)
    (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
    (PROGN$
     (CW "Ouch ~x0 ~x1"
         (LIST* (FIRST X) NIL)
         (MBE :LOGIC (LIST* (FIRST Y) NIL)
              :EXEC (PROG2$ (CW "Hi ~s0" 'THERE)
                            Y)))
     (MBE :LOGIC (LIST* (FIRST X) NIL)
          :EXEC (LIST (AND (CONSP X) (CAR X)))))))

; More complex b* examples.

(deftest
  (defun f1 (x y)
    (b* ((- (cw "Maybe keep -"))
         (u (cons x y))
         (v (car u))
         (? (cw "Throw away ?"))
         ((mv ?a b) (mv u v)))
      (list a b)))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((U (CONS X Y))
          (V X)
          ((MV ?A B) (MV U V)))
       (LIST A B))))
  (simplify f1 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F1$2 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "Maybe keep -"))
          (U (CONS X Y))
          (V X)
          ((MV ?A B) (MV U V)))
       (LIST A B)))))

;;; Test mv-let

; NOTE: The following really illustrates a way that the heuristics can fail us.
(deftest
  (defun g (x y)
    (mv-let (a b)
      (mv x y)
      (prog2$ (first x)
              (list (car (cons a b)) b))))
  (simplify g :disable (prog2$-fn mv-nth mv-nth-cons-meta))
; Here is the result, unfortunately without FIRST:
  (DEFUN G$1 (X Y)
    (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
    (LET ((B Y))
         (PROG2$ (CAR X) (LIST X B))))
; ... BUT:
; If we first redefine:
;   (defun simplifiable-mv-nth (term alist)
;      (declare (ignore term alist))
;      (mv nil nil))
; Then we instead get this nice result, with FIRST:
;    (DEFUN G$1 (X Y)
;      (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
;      (MV-LET (A B)
;        (MV X Y)
;        (PROG2$ (FIRST X) (LIST A B))))

; Unfortunately, a b* test in this file (simplify-defun-tests.lisp) fails after
; we make such a redefinition, probably because we are fearless in messing with
; mv-nth in directed-untranslate and/or simplify, and the prover needs to be
; able to remove any mv-nth that we insert.
  )

(deftest
  (defund f1 (x y)
    (mv x y))
  (defun f2 (x)
    (mv-let (a b)
      (f1 (car x) (cdr x))
      (cons b (car (cons a a)))))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV-LET (A B)
       (F1 (CAR X) (CDR X))
       (CONS B A)))))

(deftest
  (defund f (x y)
    (mv x y))
  (defun g (x)
    (mv-let (a b)
      (f x 3)
      (list (car (cons a a)) b)))
  (defun h (x)
    (g x))
  (simplify h)
  (must-be-redundant
   (DEFUN H$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (MV-NTH 0 (MV-LIST 2 (F X 3)))
           (MV-NTH 1 (MV-LIST 2 (F X 3))))))
  (simplify g)
  (must-be-redundant
   (DEFUN G$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV-LET (A B) (F X 3) (LIST A B)))))

(deftest ; needs sublis-expr+ to go inside lambda bodies
  (defstub foo (x y) (mv x y))
  (defun bar (a b)
    (mv-let (x y)
      (foo a b)
      (let ((u (cons x y)))
        (cons (car u) u))))
  (simplify bar)
  (must-be-redundant
   (DEFUN BAR$1 (A B)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (MV-LET (X Y)
       (FOO A B)
       (LET ((U (CONS X Y))) (CONS X U))))))

;; Test mv

(deftest
  (defun f1 (x y)
    (mv y (car (cons x y))))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV Y X))))

;; Test of simplifying a 0-ary function:
(deftest
  (defun foo (x) (+ 1 1 x))
  (defun bar () (foo 2))
  (simplify foo)
  (simplify bar)
  (must-be-redundant
   (DEFUN BAR$1 NIL
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     4)))

;; Tests of :equiv argument:

(deftest ; basic test
  (defun foo (e x)
    (member-equal e (fix-true-listp x)))
  (must-fail (simplify foo))
  (simplify foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO$1 (E X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MEMBER-EQUAL E X))
   (DEFTHM FOO-BECOMES-FOO$1
     (IFF (FOO E X) (FOO$1 E X)))))

(deftest ; need suitable context
  (defun foo (e x)
    (cons 3 (member-equal e (fix-true-listp x))))
  (must-fail (simplify foo :equiv iff)))

(deftest ; silly recursive example (works even without :equiv
  (defun foo (e x)
    (cond ((member-equal e (fix-true-listp x))
           e)
          ((endp e) nil)
          (t (foo (cdr e) x))))
  (simplify foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO$1 (E X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT E)
                     :VERIFY-GUARDS NIL))
     (COND ((MEMBER-EQUAL E X) E)
           ((ENDP E) NIL)
           (T (FOO$1 (CDR E) X))))
   (DEFTHM FOO-BECOMES-FOO$1
     (IFF (FOO E X) (FOO$1 E X)))))

(deftest           ; better recursive example
  (defun foo (a x) ; a occurs in x after first occurrence of 3
    (cond ((endp x) nil)
          ((eql (car x) 3)
           (member-equal a (fix-true-listp x)))
          (t (foo a (cdr x)))))
  (simplify foo :equiv iff)
  (must-be-redundant
   (DEFUN FOO$1 (A X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL))
     (COND ((ENDP X) NIL)
           ((EQL (CAR X) 3) (MEMBER-EQUAL A X))
           (T (FOO$1 A (CDR X)))))
   (DEFTHM FOO-BECOMES-FOO$1
     (IFF (FOO A X) (FOO$1 A X)))))

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
  (simplify foo
            :equiv iff
            :assumptions :guard
            :disable fix)
  (must-be-redundant
   (DEFUN FOO$1 (A X)
     (DECLARE (XARGS :GUARD (RATIONAL-LISTP X)
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (COND ((ENDP X) NIL)
           ((EQL (CAR X) 3) (MEMBER-EQUAL A X))
           (T (FOO$1 A (CDR X)))))
   (DEFTHM FOO-BECOMES-FOO$1
     (IMPLIES (RATIONAL-LISTP X)
              (IFF (FOO A X) (FOO$1 A X))))))

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

; ;recursive: the call to lenb is get fixed up to be a call to lenb$1:
  (simplify lenb)

  (must-be-redundant
   (DEFUND LENB$1 (X)
     (DECLARE
      (XARGS :GUARD T
             :VERIFY-GUARDS NIL))
     (IF (CONSP X) (+ 1 (LENB$1 (CDR X))) 0))
   (DEFTHM LENB-BECOMES-LENB$1
     (EQUAL (LENB X) (LENB$1 X)))))

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

; ;recursive: the call to lenb is get fixed up to be a call to lenb$1:
  (simplify lenb :assumptions :guard)

  (must-be-redundant
   (DEFUND LENB$1 (X)
     (DECLARE
      (XARGS :GUARD (TRUE-LISTP X)
             :VERIFY-GUARDS T))
     (IF (ENDP X)
         0 (+ 1 (LENB$1 (CDR X)))))
   (DEFTHM LENB-BECOMES-LENB$1
     (IMPLIES (TRUE-LISTP X)
              (EQUAL (LENB X) (LENB$1 X))))))

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

  (simplify lenb)

  (must-be-redundant
   (DEFUN LENB$1 (X)
     (DECLARE
      (XARGS :GUARD (TRUE-LISTP X)
             :VERIFY-GUARDS T))
     (IF (ENDP X)
         0 (+ 1 (LEN (CDR X)))))
   (DEFTHM LENB-BECOMES-LENB$1
     (EQUAL (LENB X) (LENB$1 X)))))

;; Test of :measure nil and :measure-hints nil.

(deftest
  (defun bar (x)
    (declare (xargs :measure (nfix x)))
    (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
  (simplify bar :measure nil :measure-hints nil)
  (must-be-redundant
    (DEFUND BAR$1 (X)
      (DECLARE (XARGS :GUARD T
                      :VERIFY-GUARDS NIL))
      (IF (ZP X) 0 (+ 2 (BAR$1 (+ -1 X)))))
    (DEFTHM BAR-BECOMES-BAR$1
      (EQUAL (BAR X) (BAR$1 X)))))

;; Using OR (from the :doc).

(deftest
  (defun foo (x y)
    (if (true-listp (cons 3 x))
        (or (eql (length x) 17) y)
      'dont-care))

  ;; Pattern is actually (if @ @ _), so matches entire body, and test and true
  ;; branch are both simplified.
  (simplify foo :simplify-body (or @ _))

  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (TRUE-LISTP X)
         (IF (EQL (LEN X) 17) T Y)
         'DONT-CARE)))

  ;; Pattern is actually (if @1 @1 _), so this time the entire body is not
  ;; matched and the OR call in the body is matched instead.
  (simplify foo :simplify-body (or @1 _))

  (must-be-redundant
   (DEFUN FOO$2 (X Y)
     (DECLARE (XARGS :GUARD T
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

  (simplify g :simplify-body (* (:@ (nth 0 x)) _))

  (must-be-redundant
   (DEFUN G$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (+ (NTH 0 X) 3)
           (* (CAR (CONS Y Y)) 4)
           (* (AND (CONSP X) (CAR X)) 5)))))

; Dealing with tests on endp and atom

(deftest
  (defun h1 (x y)
    (if (endp x) (car (cons x x)) (car (cons y y))))
  (simplify h1)
  (must-be-redundant
   (DEFUN H1$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (ENDP X) X Y)))
  (defun h2 (x y)
    (if (atom x) (car (cons x x)) (car (cons y y))))
  (simplify h2)
  (must-be-redundant
   (DEFUN H2$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (ATOM X) X Y)))
  (defun h3 (x y)
    (if (not (endp x)) (car (cons x x)) (car (cons y y))))
  (simplify h3)
  (must-be-redundant
   (DEFUN H3$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (NOT (ENDP X)) X Y)))
  (defun h4 (x y)
    (if (not (atom x)) (car (cons x x)) (car (cons y y))))
  (simplify h4)
  (must-be-redundant
   (DEFUN H4$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (NOT (ATOM X)) X Y)))
  (defun h5 (x y)
    (if (not (consp x)) (car (cons x x)) (car (cons y y))))
  (simplify h5)
  (must-be-redundant
   (DEFUN H5$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (NOT (CONSP X)) X Y))))

; null, =, etc.

(deftest
  (defun h (x y)
    (list (null x) (= x y) (eql x y) (eq x y) (car (cons x x))))
  (must-fail
   (simplify h :disable car-cons))
  (simplify h)
  (must-be-redundant
   (DEFUN H$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LIST (NULL X)
           (= X Y)
           (EQL X Y)
           (EQ X Y)
           X))))

; A nice big test of let*, mbt, etc. from Stephen Westfold (slightly modified
; to avoid skip-proofs that was needed for termination proof).

(deftest
  (defstub triangle-product1 (x) t)
  (defstub clause-listp (x) t)
  (defstub all-resolvents-of-pairs (x) t)
  (defstub add-factors (x) t)
  (defstub empty-clause () t)
  (defstub clause-set-contains-answer-clausep (x) t)
  (defstub get-answer-clause (x) t)
  (defstub clause-set-difference (x y) t)
  (defstub keep-pairs-that-contain-units (x y) t)
  (defstub exists-resolving-pair-with-resolvent-p (x) t)

  (defun foo (resolvents clauses hinfo)
    (declare (ignore hinfo))
    (append resolvents clauses))

  (defun select-pairs (clauses hinfo)
    (declare (ignore hinfo)
             (xargs :guard (clause-listp clauses)))
    (let* ((all-pairs (triangle-product1 clauses))
           (unit-pairs (keep-pairs-that-contain-units all-pairs nil)))
      (if (exists-resolving-pair-with-resolvent-p unit-pairs)
          unit-pairs all-pairs)))

  (defstub answer-search-stub (clauses hinfo count) t)

  (defun answer-search (clauses hinfo count)
    (if (mbt (clause-listp clauses))
        (if (or (zp count)
                (null clauses))
            :timed-out
          (let* ((pairs (select-pairs clauses hinfo))
                 (all-resolvents (all-resolvents-of-pairs pairs))
                 (all-resolvents (add-factors all-resolvents)))
            (if (member-equal (empty-clause) all-resolvents)
                (empty-clause)
              (if (clause-set-contains-answer-clausep all-resolvents)
                  (get-answer-clause all-resolvents)
                (let* ((new-resolvents
                        (clause-set-difference all-resolvents clauses))
                       (resolvents new-resolvents))
                  (if (null resolvents)
                      :fail
                    (let* ((next-clauses (foo resolvents clauses hinfo))
                           (hinfo nil)
                           (count (+ -1 count)))
                      (answer-search-stub next-clauses hinfo count))))))))
      :fail))

  (simplify answer-search)

  (must-be-redundant
   (DEFUN
     ANSWER-SEARCH$1 (CLAUSES HINFO COUNT)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF
      (MBT (CLAUSE-LISTP CLAUSES))
      (IF
       (OR (ZP COUNT) (NULL CLAUSES))
       :TIMED-OUT
       (LET*
        ((PAIRS
          (IF (EXISTS-RESOLVING-PAIR-WITH-RESOLVENT-P
               (KEEP-PAIRS-THAT-CONTAIN-UNITS (TRIANGLE-PRODUCT1 CLAUSES)
                                              NIL))
              (KEEP-PAIRS-THAT-CONTAIN-UNITS (TRIANGLE-PRODUCT1 CLAUSES)
                                             NIL)
              (TRIANGLE-PRODUCT1 CLAUSES)))
         (ALL-RESOLVENTS (ALL-RESOLVENTS-OF-PAIRS PAIRS))
         (ALL-RESOLVENTS (ADD-FACTORS ALL-RESOLVENTS)))
        (IF
         (MEMBER-EQUAL (EMPTY-CLAUSE)
                       ALL-RESOLVENTS)
         (EMPTY-CLAUSE)
         (IF
          (CLAUSE-SET-CONTAINS-ANSWER-CLAUSEP ALL-RESOLVENTS)
          (GET-ANSWER-CLAUSE ALL-RESOLVENTS)
          (LET*
           ((NEW-RESOLVENTS (CLAUSE-SET-DIFFERENCE ALL-RESOLVENTS CLAUSES))
            (RESOLVENTS NEW-RESOLVENTS))
           (IF (NULL RESOLVENTS)
               :FAIL (LET* ((NEXT-CLAUSES (APPEND RESOLVENTS CLAUSES))
                            (HINFO NIL)
                            (COUNT (+ -1 COUNT)))
                           (ANSWER-SEARCH-STUB NEXT-CLAUSES HINFO COUNT))))))))
      :FAIL))))

; Here's another test from Stephen Westfold that formerly caused problems
; related to capture.

(deftest
  (defun update-hinfo.x (resolvents clauses hinfo)
    (declare (ignore clauses)
             (xargs :guard (and (true-listp resolvents)
                                (true-listp hinfo))))
    (append resolvents hinfo))
  (defstub all-resolvents-of-pairs.x (*) => *)
  (defun answer-search.x (clauses hinfo count)
    (declare (xargs :guard (and (true-listp clauses)
                                (true-listp hinfo)
                                (natp count))
                    :verify-guards nil
                    :measure (acl2-count count)))
    (if (zp count)
        :timed-out
      (let* ((resolvents (all-resolvents-of-pairs.x clauses))
             (hinfo (update-hinfo.x resolvents clauses hinfo))
             (count (+ -1 count)))
        (answer-search.x clauses hinfo count))))
  (simplify answer-search.x)
  (must-be-redundant
   (DEFUN ANSWER-SEARCH.X$1 (CLAUSES HINFO COUNT)
     (DECLARE (XARGS :GUARD (AND (TRUE-LISTP CLAUSES)
                                 (TRUE-LISTP HINFO)
                                 (NATP COUNT))
                     :MEASURE (ACL2-COUNT COUNT)
                     :VERIFY-GUARDS NIL))
     (IF (ZP COUNT)
         :TIMED-OUT
         (LET* ((RESOLVENTS (ALL-RESOLVENTS-OF-PAIRS.X CLAUSES))
                (HINFO (APPEND RESOLVENTS HINFO))
                (COUNT (+ -1 COUNT)))
               (ANSWER-SEARCH.X$1 CLAUSES HINFO COUNT))))))

; Here's yet another test from Stephen Westfold that led us to introduce
; bind-?-initial in directed-untranslate (moved from former file
; simplify-defun-let-issue.lisp in April 2017).
(deftest
  (defun update-hinfo.y (resolvents clauses hinfo)
    (declare (ignore clauses)
             (xargs :guard (and (true-listp resolvents)
                                (true-listp hinfo))))
    (append resolvents hinfo))
  (defstub all-resolvents-of-pairs.y (*) => *)
  (defun answer-search.y (clauses hinfo count)
    (declare (xargs :guard (and (true-listp clauses)
                                (true-listp hinfo)
                                (natp count))
                    :verify-guards nil
                    :measure (acl2-count count)))
    (if (zp count)
        :timed-out
      (let* ((resolvents (all-resolvents-of-pairs.y clauses))
             (clauses (append resolvents clauses))
             (hinfo (update-hinfo.y resolvents clauses hinfo))
             (count (+ -1 count)))
        (answer-search.y clauses hinfo count))))
  (simplify answer-search.y)
  (must-be-redundant
   (DEFUN ANSWER-SEARCH.Y$1 (CLAUSES HINFO COUNT)
     (DECLARE (XARGS :GUARD (AND (TRUE-LISTP CLAUSES)
                                 (TRUE-LISTP HINFO)
                                 (NATP COUNT))
                     :MEASURE (ACL2-COUNT COUNT)
                     :VERIFY-GUARDS NIL))
     (IF (ZP COUNT)
         :TIMED-OUT (LET* ((RESOLVENTS (ALL-RESOLVENTS-OF-PAIRS.Y CLAUSES))
                           (CLAUSES (APPEND RESOLVENTS CLAUSES))
                           (HINFO (APPEND RESOLVENTS HINFO))
                           (COUNT (+ -1 COUNT)))
                          (ANSWER-SEARCH.Y$1 CLAUSES HINFO COUNT))))))

; The following test was derived from the first of Stephen's above when a
; preliminary change to directed-untranslate failed to handle the test
; immediately above.  In fact, the following test has failed without that
; change, too.

(deftest
  (defstub f1 (x) t)
  (defun app3 (r c ign)
    (declare (ignore ign))
    (append r c))
  (defun f2 (c)
    (f1 c))
  (defun g (c)
    (let* ((all-r (f2 c))
           (r all-r))
      (app3 r c 17)))
  (simplify g)
  (must-be-redundant
   (DEFUN G$1 (C)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))

; At one time we got (APPEND (F1 C) C) here.  However, the improvement to
; apt::simplify-term based on augmented terms gives this improved
; result.

     (LET* ((ALL-R (F1 C)) (R ALL-R))
           (APPEND R C)))))

; The next test shows that sometimes we appropriately expand away LET
; expressions.  With a preliminary handling of LET expressions by
; directed-untranslate, the body of F1$1 below was (LET ((Y (ACL2-NUMBERP X)))
; (IF Y X 0)), which was unfortunate because that binding of Y had nothing to
; do with the orignal binding, hence was potentially confusing.

(deftest
  (defun f1 (x)
    (let ((y (+ x x)))
      (- y x)))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (ACL2-NUMBERP X) X 0))))


; Test that we don't get an error when directed-untranslate encounters ignored
; let-bound variables (with check-du-inv).

(deftest
  (set-ignore-ok t)
  (defun foo (x)
    (let ((y (car (cons x x))) (z x))
      (cons y y)))
  (set-ignore-ok nil)
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y X)) (CONS Y Y)))))

; Here is an example from Eric Smith.  It was intended to show that
; directed-untranslate is careful in its generalization; indeed, at one time we
; got the "correct" answer.  Then we found that the next example wasn't as
; satisfying with that same implementation.  Ultimately, the heuristics for
; reconstituting LET expressions may never be totally satisfactory; for now we
; punt on getting really good results for these two examples.  In a sense,
; that's the price we pay for the freedom provided by a type-free logic.

(deftest
  (defun starting-account-balance () 0)
  (defun new-client-info (address)
    (let ((account-balance (starting-account-balance))
          (years-as-a-customer 0))
      (list account-balance
            years-as-a-customer
            address)))
  (simplify new-client-info)
  (must-be-redundant
   (DEFUN NEW-CLIENT-INFO$1 (ADDRESS)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((ACCOUNT-BALANCE 0)
           (YEARS-AS-A-CUSTOMER 0))
          (LIST ACCOUNT-BALANCE
                YEARS-AS-A-CUSTOMER ADDRESS)))))

(deftest

; See the comment on the preceding test.  The only change here is the
; replacement of let by let*.

  (defun starting-account-balance () 0)
  (defun new-client-info (address)
    (let* ((account-balance (starting-account-balance))
           (years-as-a-customer 0))
      (list account-balance
            years-as-a-customer
            address)))
  (simplify new-client-info)
  (must-be-redundant
   (DEFUN NEW-CLIENT-INFO$1 (ADDRESS)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET* ((ACCOUNT-BALANCE 0)
; The following binding is gross...
            (YEARS-AS-A-CUSTOMER ACCOUNT-BALANCE))
           (LIST ACCOUNT-BALANCE
; ... but at least we have the "right" thing here:
                 YEARS-AS-A-CUSTOMER
                 ADDRESS)))))

; The following example shows why we need a call of sublis-expr in function
; lambdafy-rec in system book kestrel/utilities/directed-untranslate.lisp.

(deftest
  (defun foo (x)
    (let ((u (list x x x x))
          (v (list x x x)))
      (cons (cdr u) v)))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((V (LIST X X X))) (CONS V V)))))

; Tests of evaluation and programmatic interface

(deftest

  (defun foo (x)
    (declare (xargs :measure (car (cons (acl2-count x) 17))))
    (if (consp x)
        (foo (car (cons (cdr x) x)))
      x))

; Use simplify not programmatically:

  (make-event (er-progn (simplify foo)
                        (value (get-event 'foo$1 (w state)))))

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (CAR (CONS (ACL2-COUNT X) 17))
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (FOO$1 (CDR X)) X)))

; Similarly, but with trans-eval-error-triple on programmatic call:

  (make-event (er-let* ((res (simplify-programmatic
                              'foo
                              :simplify-measure
                              (not (not t))))
                        (form (value (manage-screen-output nil res)))
                        (ignore
                         (trans-eval-error-triple form 'my-ctx state)))

; The output about "The admission of FOO$2 is trivial" is from after make-event
; expansion, when the defun event is finally submitted.

                (value (get-event 'foo$2 (w state)))))

  (must-be-redundant
   (DEFUN FOO$2 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (FOO$2 (CDR X)) X)))

  ;; TODO: Perhaps check that :eval is illegal for simplify-programmatic.

; Check for propagation of expected error (:bad-arg isn't a valid pattern):

  (make-event (mv-let (erp val state)
                (simplify-defun-programmatic 'foo :simplify-body :bad-arg)
                (value (list 'defconst '*c0* (list 'quote (list erp val))))))

  (assert-event (equal *c0* '(:WRONG-FORM NIL)))

  (defun bar (x) x)

  (make-event (mv-let (erp val state)
                (simplify-defun-programmatic 'bar)
                (value (list 'defconst '*c1* (list 'quote (list erp val))))))

  (assert-event (equal *c1* '(:CONDITION-FAILED NIL)))

  )

; An extra test from Eric Smith of copy-def (which failed before 7/25/2017):

(deftest
  (simplify pseudo-termp :must-simplify nil))

; A simple test with nested LETs:

(deftest
  (defun f (x y z)
    (let ((y (cons x z))
          (w (cons x y)))
      (let ((u (equal y w)))
        (list u y w))))
  (simplify f)

  (must-be-redundant
   (DEFUN F$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{2} (CONS X Z)) (W (CONS X Y)))
          (LET ((U (EQUAL Z Y)) (Y Y{2}))
               (LIST U Y W))))))

; Another simple test with nested LETs (actually, a LET*):

(deftest
  (defun f (x) (car x))
  (defun g (x) (car x))
  (defthm f-is-g
    (implies (consp x)
             (equal (f x) (g x))))
  (in-theory (disable f g))
  (defun h (x)
    (and (consp x)
         (let* ((y x)
                (z y)
                (w z))
           (f (car (cons w w))))))
  (simplify h)
  (must-be-redundant
   (DEFUN H$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (AND (CONSP X)
          (LET* ((Y X) (Z Y) (W Z)) (G W))))))

; Next we include some tests of patterns that go into bodies of LET (LAMBDA)
; expressions.

; Just a very simple test of patterns in LET bodies:
(deftest
  (defun f (x y z)
    (let ((y (cons x z))
          (w (cons x y)))
      (list (equal y w) y w)))
; Both of the following work.
  (simplify f :simplify-body (cons @ (cons _ _)))
  (simplify f :simplify-body (list @ _ _))
  (must-be-redundant
   (DEFUN F$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{1} (CONS X Z)) (W (CONS X Y)))
          (LIST (EQUAL Z Y) Y{1} W))))
  (must-be-redundant
   (DEFUN f$2 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{1} (CONS X Z)) (W (CONS X Y)))
          (LIST (EQUAL Z Y) Y{1} W)))))

; Just a simple test of patterns in LET bodies:
(deftest
  (defun f (x y z)
    (let ((y (cons x z))
          (w (cons x y)))
      (let ((u (equal y w)))
        (list u y w))))
; Both of the following work.
  (simplify f :simplify-body (cons @ (cons _ _)))
  (simplify f :simplify-body (list @ _ _))
  (must-be-redundant
   (DEFUN F$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{1} (CONS X Z)) (W (CONS X Y)))
          (LET ((U (EQUAL Z Y)) (Y Y{1}))
               (LIST U Y W)))))
  (must-be-redundant
   (DEFUN F$2 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{1} (CONS X Z)) (W (CONS X Y)))
          (LET ((U (EQUAL Z Y)) (Y Y{1}))
               (LIST U Y W)))))
; As above, but defeat directed-untranslate:
  (simplify f :simplify-body (cons @ (cons _ _)) :untranslate t)
  (must-be-redundant
   (DEFUN F$3 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y{1} (CONS X Z)) (W (CONS X Y)))
          (LIST (EQUAL Z Y) Y{1} W)))))

; Just another simple test of patterns in LET bodies:
(deftest
  (defun f (x y)
    (let ((z (car (cons y y)))
          (x (cons (car (cons y 3)) (car (cons x y)))))
      (cons z x)))

; Be careful when thinking about the following!  The pattern's reference (:@ x)
; indicates an exact match to the variable x, so the match is with (cons z x),
; not with (car (cons x y)).  The next test shows why this matters.
  (simplify f :simplify-body (cons _ (:@ x)))

  (DEFUN F$1 (X Y)
    (DECLARE (XARGS :GUARD T
                    :VERIFY-GUARDS NIL))
    (LET ((Z (CAR (CONS Y Y))))
         (CONS Z (CONS Y X)))))

; This is a slight variant of the preceding test; see the comment above the
; simplify in that test.
(deftest
  (defun f (x y)
    (let ((z (car (cons y y)))
          (x (cons (car (cons y 3)) (car (cons x y)))))
      (cons z x)))
  (simplify f :simplify-body (cons _ (:@ (car _))))
  (DEFUN F$1 (X Y)
    (DECLARE (XARGS :GUARD T
                    :VERIFY-GUARDS NIL))
    (LET ((Z (CAR (CONS Y Y)))
          (X (CONS (CAR (CONS Y 3)) X)))
         (CONS Z X))))

; Here we revisit a test based on material from Stephen Westfold.
(deftest
  (defstub triangle-product1 (x) t)
  (defstub clause-listp (x) t)
  (defstub all-resolvents-of-pairs (x) t)
  (defstub add-factors (x) t)
  (defstub empty-clause () t)
  (defstub clause-set-contains-answer-clausep (x) t)
  (defstub get-answer-clause (x) t)
  (defstub clause-set-difference (x y) t)
  (defstub keep-pairs-that-contain-units (x y) t)
  (defstub exists-resolving-pair-with-resolvent-p (x) t)

  (defun foo (resolvents clauses hinfo)
    (declare (ignore hinfo))
    (append resolvents clauses))

  (defun select-pairs (clauses hinfo)
    (declare (ignore hinfo)
             (xargs :guard (clause-listp clauses)))
    (let* ((all-pairs (triangle-product1 clauses))
           (unit-pairs (keep-pairs-that-contain-units all-pairs nil)))
      (if (exists-resolving-pair-with-resolvent-p unit-pairs)
          unit-pairs all-pairs)))

  (defstub answer-search-stub (clauses hinfo count) t)

  (defun answer-search (clauses hinfo count)
    (if (mbt (clause-listp clauses))
        (if (or (zp count)
                (null clauses))
            :timed-out
          (let* ((pairs (select-pairs clauses hinfo))
                 (all-resolvents (all-resolvents-of-pairs pairs))
                 (all-resolvents (add-factors all-resolvents)))
            (if (member-equal (empty-clause) all-resolvents)
                (empty-clause)
              (if (clause-set-contains-answer-clausep all-resolvents)
                  (get-answer-clause all-resolvents)
                (let* ((new-resolvents
                        (clause-set-difference all-resolvents clauses))
                       (resolvents new-resolvents))
                  (if (null resolvents)
                      :fail
                    (let* ((next-clauses (foo resolvents clauses hinfo))
                           (hinfo nil)
                           (count (+ -1 count)))
                      (answer-search-stub next-clauses hinfo count))))))))
      :fail))

  (simplify answer-search
            :simplify-body (:@ (add-factors all-resolvents)))

  (must-be-redundant
   (defun answer-search$1 (clauses hinfo count)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (if (mbt (clause-listp clauses))
         (if (or (zp count)
                 (null clauses))
             :timed-out
           (let* ((all-resolvents
                   (ADD-FACTORS
                    (ALL-RESOLVENTS-OF-PAIRS
                     (IF (EXISTS-RESOLVING-PAIR-WITH-RESOLVENT-P
                          (KEEP-PAIRS-THAT-CONTAIN-UNITS
                           (TRIANGLE-PRODUCT1 CLAUSES)
                           NIL))
                         (KEEP-PAIRS-THAT-CONTAIN-UNITS
                          (TRIANGLE-PRODUCT1 CLAUSES)
                          NIL)
                         (TRIANGLE-PRODUCT1 CLAUSES))))))
             (if (member-equal (empty-clause) all-resolvents)
                 (empty-clause)
               (if (clause-set-contains-answer-clausep all-resolvents)
                   (get-answer-clause all-resolvents)
                 (let* ((new-resolvents
                         (clause-set-difference all-resolvents clauses))
                        (resolvents new-resolvents))
                   (if (null resolvents)
                       :fail
                     (let* ((next-clauses (foo resolvents clauses hinfo))
                            (hinfo nil)
                            (count (+ -1 count)))
                       (answer-search-stub next-clauses hinfo count))))))))
       :fail))))

; Here we revisit another test also based on material from Stephen Westfold.
(deftest
  (defun update-hinfo.x (resolvents clauses hinfo)
    (declare (ignore clauses)
             (xargs :guard (and (true-listp resolvents)
                                (true-listp hinfo))))
    (append resolvents hinfo))
  (defstub all-resolvents-of-pairs.x (*) => *)
  (defun answer-search.x (clauses hinfo count)
    (declare (xargs :guard (and (true-listp clauses)
                                (true-listp hinfo)
                                (natp count))
                    :verify-guards nil
                    :measure (acl2-count count)))
    (if (zp count)
        :timed-out
      (let* ((resolvents (all-resolvents-of-pairs.x clauses))
             (hinfo (update-hinfo.x resolvents clauses hinfo))
             (count (+ -1 count)))
        (answer-search.x clauses hinfo count))))
  (simplify answer-search.x
            :simplify-body
            (let* ((resolvents _)
                   (hinfo @)
                   (count _))
              _))
  (must-be-redundant
   (DEFUN ANSWER-SEARCH.X$1 (CLAUSES HINFO COUNT)
     (DECLARE (XARGS :GUARD (AND (TRUE-LISTP CLAUSES)
                                 (TRUE-LISTP HINFO)
                                 (NATP COUNT))
                     :MEASURE (ACL2-COUNT COUNT)
                     :VERIFY-GUARDS NIL))
     (IF (ZP COUNT)
         :TIMED-OUT
         (LET* ((RESOLVENTS (ALL-RESOLVENTS-OF-PAIRS.X CLAUSES))
                (HINFO (APPEND RESOLVENTS HINFO))
                (COUNT (+ -1 COUNT)))
               (ANSWER-SEARCH.X$1 CLAUSES HINFO COUNT)))))

; Same result this way:

  (simplify answer-search.x
            :simplify-body
            (:@ (update-hinfo.x resolvents clauses hinfo)))

  (must-be-redundant
   (DEFUN ANSWER-SEARCH.X$2 (CLAUSES HINFO COUNT)
     (DECLARE (XARGS :GUARD (AND (TRUE-LISTP CLAUSES)
                                 (TRUE-LISTP HINFO)
                                 (NATP COUNT))
                     :MEASURE (ACL2-COUNT COUNT)
                     :VERIFY-GUARDS NIL))
     (IF (ZP COUNT)
         :TIMED-OUT
         (LET* ((RESOLVENTS (ALL-RESOLVENTS-OF-PAIRS.X CLAUSES))
                (HINFO (APPEND RESOLVENTS HINFO))
                (COUNT (+ -1 COUNT)))
               (ANSWER-SEARCH.X$2 CLAUSES HINFO COUNT))))))

; Next we test patterns inside LET bindings.

(deftest
  (defun foo (x)
    (let ((y (cdr (cons x 3))))
      (car y)))
  (simplify foo
            :simplify-body
            (let ((y @))
              (car y)))
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y 3)) (CAR Y)))))

(deftest
  (defun foo (v)
    (let* ((x (+ v v))
           (y (cdr (cons x 3))))
      (cons x (car y))))
  (simplify foo
            :simplify-body
            (let ((y @))
              _))
  (must-be-redundant
   (DEFUN FOO$1 (V)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET* ((X (+ V V))
            (Y 3))
           (CONS X (CAR Y))))))

; Test rewriting with respect to strong contexts: attachment to
; assume-true-false-aggressive-p of constant-t-function-arity-0.

(deftest
  (defun foo (x y z)
    (if (or (consp x) (consp y))
        (if (or (consp x) (consp z))
            (if (consp x)
                0
              (cons (cons (car y) (cdr y))
                    (cons (car z) (cdr z))))
          0)
      0))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X Y Z)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (IF (OR (CONSP X) (CONSP Y))
         (IF (OR (CONSP X) (CONSP Z))
             (IF (CONSP X) 0 (CONS Y Z))
             0)
         0))))

; Here is an example that tests both the introduction of MV and the dropping of
; unused LET bindings.  It is essentially from Stephen Westfold.  Before
; 4/3/2018 the result was as shown below in a comment.

(deftest
  (encapsulate
    (((dr-state *) => *)
     ((dr-state-ext * *) => *)
     ((coord-state *) => *)
     ((to-dr-state-ext *) => *))
    (local (defun dr-state (x)
             x))
    (local (defun dr-state-ext (x y)
             (declare (ignore y))
             x))
    (local (defun coord-state (x)
             x))
    (local (defun to-dr-state-ext (x)
             x))
    (defthm to-dr-state-ext-of-dr-state
      (equal (to-dr-state-ext (dr-state drn-st))
             (dr-state-ext drn-st 0))))
  (defun add-foo1 (drn-st coord-st)
    (mv (dr-state drn-st) (coord-state coord-st)))
  (defun add-foo (drn-st coord-st)
    (mv-let (drnst coordst)
      (add-foo1 drn-st coord-st)
      (mv (to-dr-state-ext drnst) coordst)))

; Before the change:
  #+skip ; make a comment
  (DEFUN ADD-FOO$1 (DRN-ST COORD-ST)
    (DECLARE (XARGS :GUARD T
                    :VERIFY-GUARDS NIL))
    (LET ((DRNST (DR-STATE DRN-ST))
          (COORDST (COORD-STATE COORD-ST)))
         (LIST (DR-STATE-EXT DRN-ST 0) COORDST)))

  (simplify add-foo)
  (must-be-redundant
   (DEFUN ADD-FOO$1 (DRN-ST COORD-ST)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((COORDST (COORD-STATE COORD-ST)))
          (MV (DR-STATE-EXT DRN-ST 0) COORDST)))))

; Next we test the insertion of MV for quoted objects.

(deftest
  (defun f1 (x)
    (mv (car (cons nil x)) nil nil))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV NIL NIL NIL)))

  (defun f2 (x)
    (mv (car (cons x x)) nil nil))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV X NIL NIL)))

  (defun f3 (x)
    (mv (car (cons x x)) nil 3 :abc 'd))
  (simplify f3)
  (must-be-redundant
   (DEFUN F3$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV X NIL 3 :ABC 'D))))

;;; The following test for handling mv was inspired by an example of Stephen
;;; Westfold (the next test, with foo9, below).  The problem had been with the
;;; function mv-marker-args, which had returned nil for
;;;   (MV-MARKER-ARGS 2 '(CONS 'Y '(NIL)))
;;; insted of ('Y NIL).

(deftest
  (defun f1 (y)
    (mv (car (cons y y)) nil))
  (simplify f1)

; The body was (CONS Y '(NIL)) until 4/10/2018.

  (must-be-redundant
   (DEFUN F1$1 (Y)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (MV Y NIL))))

;;; The next test, from Stephen Westfold, failed before 4/10/2018, both because
;;; of the mv-marker-args issue covered in the preceding test and because, as
;;; Stephen noted, the stobjs-out needed to be available for foo9$1.

(deftest
  (defun foo9 (x y)
    (if (endp x)
        (mv y nil)
      (mv-let (x y)
        (foo9 (cdr x) y)
        (mv x (cons (car (list y)) (cdr y))))))
  (simplify foo9)
  (must-be-redundant
   (DEFUN
     FOO9$1 (X Y)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL
                     :HINTS (("Goal" :USE (:TERMINATION-THEOREM FOO9))
                             '(:IN-THEORY (DISABLE* FOO9 (:E FOO9) (:T FOO9))))))
     (IF (NOT (CONSP X))
         (MV Y NIL)
         (MV-LET (X Y)
           (FOO9$1 (CDR X) Y)
           (MV X (CONS Y (CDR Y))))))))

(deftest
; The simplify call below failed with an error until a fix to copy-def
; was made on 5/12/2018.
  (defun foo (x) (cons x x))
  (defun bar (x) (cons x x))
  (mutual-recursion
   (defun f1 (x)
     (if (foo x) (bar x) (if (consp x) (f2 (cdr x)) x)))
   (defun f2 (x)
     (if (foo x) (bar x) (if (consp x) (f1 (cdr x)) x))))
  (simplify f1
            :simplify-body (if (foo x) @ _))
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F1$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (FOO X)
                           (CONS X X)
                           (IF (CONSP X) (F2$1 (CDR X)) X)))
                     (DEFUN F2$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (FOO X)
                           (CONS X X)
                           (IF (CONSP X) (F1$1 (CDR X)) X))))))

(deftest

; Here we test an error message, which is better based on an improvement to the
; expander function, simplify-hyps, made on 5/13/2018.

; Further comment from Matt K.:

; Some controversy may be possible here.  What should we do when attempting to
; simplify an unreachable part of the body?  Currently, the error message just
; reports a contradictory list of hypotheses for simplification.  One can
; imagine modifying the expander's function simplify-hyps so that it provides
; this information, rather than printing an error, so that simplify-defun can
; print a more informative error message, or perhaps heuristically compute a
; suitable replacement for the term based on the computed type of the function
; (e.g., nil or 0), which however might be weird for the user.  Rather than get
; into all this, my approach was to improve the error message from the expander
; so that it's (I think) good enough.  This seems like a pretty rare case
; that's perhaps taken more than its deserved share of my time already.

  (defun foo (x) (cons x x))
  (mutual-recursion
   (defun f1 (x)
     (if (consp x)
         (if (foo x)
             (f2 (cdr x))
           (natp x))
       x))
   (defun f2 (x)
     (if (consp x)
         (if (foo x)
             (f1 (cdr x))
           (natp x))
       x)))
  (must-fail
   (simplify f1
             :simplify-body (if (foo x) _ @))))

;;; Failure test: The following isn't very interesting unless we remove each
;;; must-fail and inspect the generated output.
(deftest
  (defun my-consp (x)
    (declare (xargs :guard t))
    (consp x))
  (defun my-car (x)
    (declare (xargs :guard (my-consp x)))
    (car x))
  (defun foo (x)
    (declare (xargs :guard t))
    (and (my-consp x)
         (natp (my-car x))
         (+ 2 3 (my-car x))))

; The following failed until late November, 2020.  The failure was in guard
; verification, and that failure was overcome by making a final proof attempt
; in the current-theory.
  (simplify foo
            :theory (disable my-consp (:e tau-system))
            :print :info)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
     (AND (MY-CONSP X)
          (AND (INTEGERP (CAR X))
               (NOT (< (CAR X) 0)))
          (+ 5 (CAR X)))))

; also succeeds
  (simplify foo
            :theory (disable my-consp (:e tau-system))
            :guard-hints nil)
  (must-be-redundant
   (DEFUN FOO$2 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
     (AND (MY-CONSP X)
          (AND (INTEGERP (CAR X))
               (NOT (< (CAR X) 0)))
          (+ 5 (CAR X))))))

; Next we test the ability of simplify-defun to handle guard verification
; automatically when the function is used in a test, a challenge pointed out by
; Eric Smith (in particular when there are :assumptions, but this test does not
; have assumptions; that may be considered later).
(deftest
  (defun my-integer-listp (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (integerp (car x))
             (my-integer-listp (cdr x)))
      (null x)))
  (defstub p (x) t)
  (defun foo (x)
    (declare (xargs :guard (my-integer-listp x)))
    (if (consp x)
        (if (p (foo (cdr x)))
            (+ 3 4 (car x))
          5)
      6))
  (deftheory my-theory
    (disable* foo (:e foo) (:t foo)
              my-integer-listp))
  (simplify foo :theory (theory 'my-theory))
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD (MY-INTEGER-LISTP X)
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS T))
     (IF (CONSP X)
         (IF (P (FOO$1 (CDR X))) (+ 7 (CAR X)) 5)
         6))))

; Currently simplify doesn't preserve type declarations.  Here we test that at
; least it handles their semantics correctly.

(deftest
  (defun f1 (x)
    (declare (type integer x)
             (xargs :guard (natp x)))
    (cons (+ 2 3 x) x))
  (simplify f1)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD (AND (INTEGERP X)
                                 (NATP X))
                     :VERIFY-GUARDS T))
     (CONS (+ 5 X) X)))
  (defun f2 (x)
    (declare (type integer x)
             (xargs :split-types t
                    :guard (natp x)))
    (cons (+ 2 3 x) x))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD (NATP X)
                     :VERIFY-GUARDS T))
     (CONS (+ 5 X) X))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Some explanation for how simplify-defun works
;;; Matt Kaufmann, Nov. 2015
;;; (So some of this might be out of date.)
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
;              :assumptions ((my-true-listp x))
                )

; Here we see what was generated.  Notice that directed-untranslate has no
; real way of knowing that (my-cddr x) somehow generates the macro cddr.
(must-be-redundant
  (DEFUN F0$1 (X)
    (DECLARE (XARGS :GUARD (OR (ATOM X) (SYMBOL-LISTP X))
                    :MEASURE (ACL2-COUNT X)
                    :VERIFY-GUARDS T))
    (IF (CONSP X)
        (CONS X (F0$1 (CDR (CDR X))))
      NIL)))

; The large comment below provides some explanataion about the events
; generated.  For simplicity we ignore wrappers (WITH-OUTPUT, ENCAPSULATE,
; PROGN, and LOCAL); of course, to see those you may simply change the call of
; simplify-defun above to the corresponding call of show-simplify-defun.

; WARNING: Don't be surprised if this is rather out of date!  (Perhaps with
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
(DEFUN F0$1 (X)
  (DECLARE (XARGS :GUARD (OR (ATOM X) (SYMBOL-LISTP X))
                  :VERIFY-GUARDS T
                  :GUARD-HINTS (("Goal" :USE (:GUARD-THEOREM F0)))
                  :HINTS (("Goal" :USE (:TERMINATION-THEOREM F0))))
           (IGNORABLE X))
  (AND (CONSP X)
       (CONS X (F0$1 (CDDR X)))))

; The following function provides a convenient wrapper for the assumptions.
; Perhaps it should be avoided if :hyp-fn is supplied.
(DEFUN F0-HYPS (X)
  (DECLARE (IGNORABLE X))
  (MY-TRUE-LISTP X))

; The following key theorem could be proved in advance by the user, if f0-hyps
; is also defined in advance.  In simple examples the proof goes through
; automatically.  The :hints argument can help.  See the comments
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
(DEFTHM F0-BECOMES-F0$1-LEMMA
  (IMPLIES (F0-HYPS X)
           (EQUAL (F0 X) (F0$1 X)))
  :HINTS (("Goal"
           :BY (:FUNCTIONAL-INSTANCE F0-IS-F0-COPY (F0-COPY F0$1))
           :IN-THEORY *F0-RUNES*)
          '(:USE F0$1)))))

; The main theorem is now a trivial corollary, simply by expanding the
; assumptions predicate.
(DEFTHM F0-BECOMES-F0$1
  (IMPLIES (MY-TRUE-LISTP X)
           (EQUAL (F0 X) (F0$1 X)))
  :HINTS (("Goal" :USE F0-BECOMES-F0$1-LEMMA
           :IN-THEORY '(F0-HYPS))))))
||#

; Test (from Eric S. I think) that simplify-defun is happy even when translated
; definition isn't different, as long as untranslated definition has changed.
(deftest
  (defun bar () (+ 1 1))
  (simplify-defun bar))

(deftest
  (defun foo (x)
    (let ((v (car (cons (* x x) 5))))
      (+ v v)))

  (simplify-defun foo)

  ;; ;; result before directed-untranslate handled lambdas:
  ;;   (DEFUN FOO$1 (X)
  ;;     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
  ;;     (+ (* X X) (* X X)))

  ;; desired result:
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (let ((v (* x x)))
       (+ v v)))))

; The following tests preservation of let under a blocker.  It also exercises a
; fix to augment-term (defined in simplify-defun-impl.lisp), in which a lambda
; application L whose body isn't augmented was returned with an augmentedp flag
; of nil were t would be appropriate instead.
(deftest
  (defun foo (x)
    (prog2$ (cw "Hi")
            (let ((x (+ 3 4 x)))
              (cons x x))))
  (in-theory (disable prog2$-fn))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (PROG2$ (CW "Hi")
             (LET ((X (+ 7 X))) (CONS X X))))))

; B* tests:
(deftest
  (defun mv2 (x y) (mv x y))
  (defun foo (x y)
    (b* ((u (cons y y))
         (z (car u))
         (- (cw "Hello.  X = ~x0~%" z))
         ((mv a b) (mv2 u x)))
      (cons a b)))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((U (CONS Y Y)) ((MV A B) (MV U X)))
       (CONS A B))))
  (encapsulate
    ()
    (local (in-theory (disable prog2$-fn)))
    (simplify foo :new-name foo$2))
  (must-be-redundant
   (DEFUN FOO$2 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((U (CONS Y Y))
          (Z Y)
          (- (CW "Hello.  X = ~x0~%" Z))
          ((MV A B) (MV U X)))
       (CONS A B))))

; And now, here are a bunch of tests that benefit from a change made
; to adjust-sterm-for-tterm by adding the case
;      (('lambda (mv-var)
;         (('lambda formals &) . mv-nths))
;       &)
; and a corresponding change to du-make-mv-let by adding a call of
; make-mv-args.

  (defun f1 (x y)
    (b* ((v (car (cons x y)))
         ((mv a b) (mv v v))
         )
      (list a b)))
  (simplify f1 :disable (prog2$-fn mv-nth mv-nth-cons-meta) :print :info)
; The following result is unfortunate.  The situation seems to be very much
; like the one somewhat earlier in this file around the comment that also
; mentions simplifiable-mv-nth.
; If instead we first redefine:
;   (defun simplifiable-mv-nth (term alist)
;     (declare (ignore term alist))
;     (mv nil nil))
; then we get a nicer result:
;   (DEFUN F1$1 (X Y)
;          (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
;          (B* ((V X) ((MV A B) (MV V V)))
;              (LIST A B)))
; But sadly, a b* test in simplify-defun-tests.lisp fails after we make such a
; redefinition, I think because we are fearless in messing with mv-nth in
; directed-untranslate and/or simplify, and the prover needs to be able to
; remove any mv-nth that we insert.
; Anyhow, we leave this test, and the comment above, in case this sort of
; inadequacy is ever considered in the future.  The other tests below in this
; deftest go much better.
  (must-be-redundant
   (DEFUN F1$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((V X))
       (LET ((MV (LIST V V)))
            MV))))

  (defun f2 (x y)
    (b* (((mv a b) (mv (car (cons x y)) y))
         (- (cw "Second -")))
      (list a b)))
  (simplify f2 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F2$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* (((MV A B) (MV X Y))
          (- (CW "Second -")))
       (LIST A B))))

  (defun f3 (x y)
    (b* (((mv a b) (mv x y))
         (- (cw "Second -")))
      (list (car (cons a b)) b)))
  (simplify f3 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F3$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* (((MV A B) (MV X Y))
          (- (CW "Second -")))
       (LIST A B))))

  (defun f4 (x y)
    (b* ((- (cw "First -"))
         (u (cons x y))
         (v (car u))
         ((mv ?a b) (mv u v))
         (- (cw "Second -"))
         (? (cw "Throw away ?")))
      (list a b)))
  (simplify f4 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F4$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "First -"))
          (U (CONS X Y))
          (V X)
          ((MV ?A B) (MV U V))
          (- (CW "Second -")))
       (LIST A B))))

  (defun f5 (x y)
    (b* ((- (cw "First -"))
         (u (cons x y))
         (v (car u))
         (? (cw "Throw away ?"))
         ((mv ?a b) (mv u (first v)))
         (- (cw "Second -")))
      (list a b)))
  (simplify f5 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F5$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "First -"))
          (U (CONS X Y))
          (V X)
          ((MV ?A B) (MV U (FIRST V)))
          (- (CW "Second -")))
       (LIST A B))))

  (defun f6 (x y)
    (b* ((- (cw "First -"))
         (u (cons x y))
         (v (car u))
         (? (cw "Throw away ?"))
         ((mv ?a b) (mv u v))
         (- (cw "Second -")))
      (list a b)))
  (simplify f6 :disable prog2$-fn)
  (must-be-redundant
   (DEFUN F6$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (B* ((- (CW "First -"))
          (U (CONS X Y))
          (V X)
          ((MV ?A B) (MV U V))
          (- (CW "Second -")))
       (LIST A B))))
  )

; Avoid creating bound variable in the "COMMON-LISP" package.  (This failed at
; one point due to a bug in ext-new-formal, fixed 8/9/2018.)
; This example is from Eric Smith.
(deftest
  (defun foo (count)
    (let* ((count (+ -1 count)))
      (list count (+ 1 count))))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (COUNT)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (LET* ((COUNT{2} (+ -1 COUNT)))
           (LIST COUNT{2}
                 (IF (ACL2-NUMBERP COUNT) COUNT 0))))))

; The following test shows a shortcoming of simplify in the case of an
; equivalence relation other than EQUAL in the presence of recursion.  See :doc
; apt::simplify-failure, section "Recursion and equivalence relations".
(deftest
  (defun f (x)
    (and x 3))
  (defun g (x)
    (if (consp x)
        (equal (g (cdr x)) (car (cons 3 x)))
      (f x)))
; We avoid must-fail because we want to see the output.
  (make-event '(:or (simplify g :equiv iff)
                    (value-triple :failed))))

; Test of forcing
(deftest
  (defun f (x)
    (car (cons x x)))
  (defthm car-f
    (implies (force (equal (append (append x y) z)
                           (append x y z)))
             (equal (car (cons x x)) x)))
  (in-theory (disable associativity-of-append f car-cons))
  (simplify f)
  (must-be-redundant
   (DEFUND F$1 (X) (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL)) X)
   (DEFTHM F-BECOMES-F$1 (EQUAL (F X) (F$1 X)))))

; When the function is called in the guard or measure, it isn't replaced by the
; new function.
(deftest
  (defun f (x)
    (declare (xargs :guard (f x) :verify-guards nil))
    (cons (car (cons x x)) 3))
  (verify-guards f)
  (simplify f)
  (must-be-redundant
   (DEFUN F$1 (X) (DECLARE (XARGS :GUARD (F X) :VERIFY-GUARDS T)) (CONS X 3))
   (DEFTHM F-BECOMES-F$1 (EQUAL (F X) (F$1 X))))

  (defun f2 (x)
    (declare (xargs :measure (if (f x) (acl2-count x) (len x))))
    (if (consp x) (f2 (cdr x)) (car (cons x x))))
  (simplify f2)
  (must-be-redundant
   (DEFUN F2$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (IF (F X) (ACL2-COUNT X) (LEN X))
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (F2$1 (CDR X)) X))
   (DEFTHM F2-BECOMES-F2$1 (EQUAL (F2 X) (F2$1 X)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Avoid problems when default defun-mode is :program.  This is awkward to test,
; because deftest creates local events, which are skipped when the default
; defun-mode is :program.  So we test non-locally below.

(defun program-mode-test (x)
  (declare (xargs :guard (integerp x)))
  (+ 2 3 x))
(program)
(simplify program-mode-test)
(logic)
(must-be-redundant
 (DEFUN PROGRAM-MODE-TEST$1 (X)
   (DECLARE (XARGS :GUARD (INTEGERP X)
                   :mode :logic ; added manually
                   :VERIFY-GUARDS T))
   (+ 5 X)))
