; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Since the official transformation is simplify, most of the tests here call
; simplify even though this file is about simplifying defun-sk forms, not defun
; forms.  We let a few of the initial ones call simplify-defun-sk just to test
; that simplify-defun-sk continues to work.

(in-package "ACL2")

(include-book "simplify")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplify-defun-sk tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fix-true-listp (lst)
  (if (consp lst)
      (cons (car lst)
            (fix-true-listp (cdr lst)))
    nil))

(defthm member-fix-true-listp
  (iff (member a (fix-true-listp lst))
       (member a lst)))

; Basic exists test for one bound variable
(deftest
  (defun-sk foo (lst)
    (exists x (member-equal x (fix-true-listp lst))))
  (simplify-defun-sk foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (EXISTS (X) (MEMBER-EQUAL X LST))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; As above, but with member, which introduces a LET.  We can probably live with
; that.  NOTE: We are blowing away prog2$ here; otherwise this test fails.
(deftest
  (defun-sk foo (lst)
    (exists x (member x (fix-true-listp lst))))
  (simplify-defun-sk foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (EXISTS (X)
              (MEMBER-EQUAL X LST))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Basic exists test for more than one bound variable
(deftest
  (defun-sk foo (lst)
    (exists (x y) (member-equal (cons x y) (fix-true-listp lst))))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (EXISTS (X Y)
              (MEMBER-EQUAL (CONS X Y) LST))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Basic forall test for one bound variable
(deftest
  (defun-sk foo (lst)
    (forall x (not (member-equal x (fix-true-listp lst)))))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (FORALL (X) (NOT (MEMBER-EQUAL X LST)))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Basic forall test for more than one bound variable
(deftest
  (defun-sk foo (lst)
    (forall (x y) (not (member-equal (cons x y) (fix-true-listp lst)))))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (FORALL (X Y)
              (NOT (MEMBER-EQUAL (CONS X Y) LST)))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Test for empty formals.
(deftest
  (defun-sk foo ()
    (forall (x y) (not (member-equal (cons x y) (fix-true-listp y)))))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 ()
      (FORALL (X Y)
              (NOT (MEMBER-EQUAL (CONS X Y) Y)))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO) (FOO$1)))))

; Test for more than one formal; also tests that UNTRANSLATE is called with IFF
; flag, so that result uses OR.
(deftest
  (defun-sk foo (u v)
    (exists (x y) (or (member-equal (cons x y) (fix-true-listp u))
                      (member-equal (cons x y) (fix-true-listp v)))))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (U V)
      (EXISTS (X Y)
              (OR (MEMBER-EQUAL (CONS X Y) U)
                  (MEMBER-EQUAL (CONS X Y) V)))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO U V) (FOO$1 U V)))))

; Test of pattern for :simplify-body
(deftest
  (defun-sk foo (u v)
    (exists (x y) (or (member-equal (cons x y) (fix-true-listp u))
                      (member-equal (cons x y) (fix-true-listp v)))))
  (simplify foo
            :simplify-body (or _ @))
  (must-be-redundant
    (DEFUN-SK FOO$1 (U V)
      (EXISTS (X Y)
              (OR (MEMBER-EQUAL (CONS X Y) (FIX-TRUE-LISTP U))
                  (MEMBER-EQUAL (CONS X Y) V)))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO U V) (FOO$1 U V)))))

; Test some options
(deftest
  (defun-sk foo (lst)
    (declare (xargs :non-executable nil))
    (forall x (not (member-equal x (fix-true-listp lst))))
    :strengthen t
    :rewrite :direct)
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (DECLARE (XARGS :NON-EXECUTABLE NIL))
      (FORALL (X) (NOT (MEMBER-EQUAL X LST)))
      :QUANT-OK T
      :STRENGTHEN T
      :REWRITE :DIRECT)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Test of :new-enable

(deftest
  (defun-sk foo (lst)
    (exists x (member-equal x (fix-true-listp lst))))
  (simplify foo)
  (assert-event (not (disabledp '(:definition foo$1))))
  (simplify foo :new-enable nil)
  (assert-event (disabledp '(:definition foo$2)))
  (simplify foo :new-enable t)
  (assert-event (not (disabledp '(:definition foo$3)))))

(deftest
  (defun-sk foo (lst)
    (exists x (member-equal x (fix-true-listp lst))))
  (in-theory (disable foo))
  (simplify foo)
  (assert-event (disabledp '(:definition foo$1)))
  (simplify foo :new-enable t)
  (assert-event (not (disabledp '(:definition foo$2))))
  (simplify foo :new-enable nil)
  (assert-event (disabledp '(:definition foo$3))))

; Test of :guard-hints.

(deftest
  (defun-sk foo (lst)
    (exists x (member-equal x (fix-true-listp lst))))
  (verify-guards fix-true-listp)
  (verify-guards foo)
  (defun my-true-listp (x)
    (declare (xargs :guard t))
    (true-listp x))
  (in-theory (disable my-true-listp (tau-system)))
  (must-fail
; This test is only of interest for its output.  To see the output, submit it
; without the surrounding call of must-fail.  The output should consist of the
; following clean and succinct error message.
#||
ACL2 Error in event processing:  Guard verification has failed for
FOO$1.  See :DOC apt::simplify-failure for some ways to address this
failure.
||#
   (simplify foo
             :guard (my-true-listp lst)))
  (simplify foo
            :guard (my-true-listp lst)
            :guard-hints (("Goal" :in-theory (enable my-true-listp))))
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (DECLARE (XARGS :GUARD (MY-TRUE-LISTP LST)
                      :VERIFY-GUARDS NIL))
      (EXISTS (X) (MEMBER-EQUAL X LST))
      :QUANT-OK T))
  (assert-event (eq (symbol-class 'foo$1 (w state)) :common-lisp-compliant)))

; Tests for more than one match

(deftest
  (defstub stub0 (x y z) t)
  (defun-sk foo (x y)
    (exists z
            (equal (list (list (list
                                (* 3 (+ 1 (+ 1 x)))
                                (* 3 (+ 1 (+ 1 x)))
                                (* 4 5 (+ 1 (+ 1 y))))))
                   (stub0 x y z))))
; Underscore variables other than _ must be distinct for matches to different
; terms:
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @1)
                                            _a
                                            (* _a 5 @2))))
; @-variables other than @ must be distinct for matches to different terms:
  (must-fail (simplify foo
                       :simplify-body (list (* 3 @a)
                                            @a
                                            _)))
; This one is fine.
  (simplify foo
            :simplify-body (list @1
                                 _1
                                 (* _2 5 @2)))
; So is this.
  (simplify foo
            :simplify-body (list @
                            _
                            (* _ 5 @)))
  (must-be-redundant
    (DEFUN-SK FOO$1 (X Y)
      (EXISTS (Z)
              (EQUAL (LIST (LIST (LIST (+ 6 (* 3 X))
                                       (* 3 (+ 1 (+ 1 X)))
                                       (* 4 5 (+ 2 Y)))))
                     (STUB0 X Y Z)))
      :QUANT-OK T))
  (must-be-redundant
    (DEFUN-SK FOO$2 (X Y)
      (EXISTS (Z)
              (EQUAL (LIST (LIST (LIST (+ 6 (* 3 X))
                                       (* 3 (+ 1 (+ 1 X)))
                                       (* 4 5 (+ 2 Y)))))
                     (STUB0 X Y Z)))
      :QUANT-OK T)))

; Test the use of directed-untranslate.

(deftest
  (defun-sk foo (lst)
    (exists x (if (consp x)
                  (member-equal x (fix-true-listp lst))
                nil)))
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (EXISTS (X) (IF (CONSP X)
                      (MEMBER-EQUAL X LST)
                    NIL))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST))))
  (defun-sk foo2a (lst)
    (exists x (if (consp x)
                  (member-equal x (fix-true-listp lst))
                nil)))
  (simplify foo2a)
  (must-be-redundant
    (DEFUN-SK FOO2A$1 (LST)
      (EXISTS (X) (IF (CONSP X)
                      (MEMBER-EQUAL X LST)
                      NIL))
      :QUANT-OK T)
    (DEFTHM FOO2A-BECOMES-FOO2A$1
      (IFF (FOO2A LST) (FOO2A$1 LST))))
  (defun-sk foo2b (lst) ; same as foo2a
    (exists x (if (consp x)
                  (member-equal x (fix-true-listp lst))
                nil)))
  (simplify foo2b :untranslate t)
  (must-be-redundant
    (DEFUN-SK FOO2B$1 (LST)
      (EXISTS (X) (AND (CONSP X) (MEMBER-EQUAL X LST)))
      :QUANT-OK T)
    (DEFTHM FOO2B-BECOMES-FOO2B$1
      (IFF (FOO2B LST) (FOO2B$1 LST)))))

;;; Test :untranslate hint.
;;; NOTE: We are blowing away prog2$ here; otherwise this test fails.
(deftest
  (defun-sk g1 (lst)
    (exists x (car (cdr (or (member 3 lst)
                            (member x lst))))))
  (simplify g1)
  (must-be-redundant
   (DEFUN-SK G1$1 (LST)
     (EXISTS (X)
             (CAR (CDR (OR (MEMBER-EQUAL 3 LST)
                           (MEMBER-EQUAL X LST)))))
     :QUANT-OK T))
  (defun-sk g2 (lst)
    (exists x (car (cdr (or (member 3 lst)
                            (member x lst))))))
  (simplify g2 :untranslate t)
  (must-be-redundant
   (DEFUN-SK G2$1 (LST)
     (EXISTS (X)
             (CADR (OR (MEMBER-EQUAL 3 LST)
                       (MEMBER-EQUAL X LST))))
     :QUANT-OK T))
  (defun-sk g3 (lst)
    (exists x (car (cdr (or (member 3 lst)
                            (member x lst))))))
  (simplify g3 :untranslate nil)
  (must-be-redundant
   (DEFUN-SK G3$1 (LST)
     (EXISTS (X)
             (CAR (CDR (IF (MEMBER-EQUAL '3 LST)
                           (MEMBER-EQUAL '3 LST)
                           (MEMBER-EQUAL X LST)))))
     :QUANT-OK T)))

;;; Test :expand hints

(deftest
  (defun-sk foo (y z)
    (exists x (equal (append y z)
                     (append z x y))))
  (simplify foo :expand (append y z))
  (must-be-redundant
   (DEFUN-SK FOO$1 (Y Z)
     (EXISTS (X)
             (EQUAL (IF (CONSP Y)
                        (CONS (CAR Y) (APPEND (CDR Y) Z))
                        Z)
                    (APPEND Z X Y)))
     :QUANT-OK T)))

; Same as above but slightly different :expand syntax.
(deftest
  (defun-sk foo (y z)
    (exists x (equal (append y z)
                     (append z x y))))
  (simplify foo :expand ((append y z)))
  (must-be-redundant
   (DEFUN-SK FOO$1 (Y Z)
     (EXISTS (X)
             (EQUAL (IF (CONSP Y)
                        (CONS (CAR Y) (APPEND (CDR Y) Z))
                        Z)
                    (APPEND Z X Y)))
     :QUANT-OK T)))

; Same as above but wilder :expand hint.
(deftest
  (defun-sk foo (y z)
    (exists x (equal (append y z)
                     (append z x y))))
  (simplify foo :expand ((:free (z) (append y z))))
  (must-be-redundant
   (DEFUN-SK FOO$1 (Y Z)
     (EXISTS (X)
             (EQUAL (IF (CONSP Y)
                        (CONS (CAR Y) (APPEND (CDR Y) Z))
                        Z)
                    (APPEND Z X Y)))
     :QUANT-OK T)))

;;; Test :must-simplify

(deftest
  (defun-sk foo (y)
    (exists x (member-equal x y)))
  (must-fail (simplify foo))
  (must-fail (simplify foo :must-simplify t))
  (simplify foo :must-simplify nil)
  (must-be-redundant
   (DEFUN-SK FOO$1 (Y)
     (EXISTS (X) (MEMBER-EQUAL X Y))
     :QUANT-OK T)))

;;; The following test fails without the use of :extra-bindings-ok in the
;;; computed hint that proves F-BECOMES-F$1 from F-BECOMES-F$1-LEMMA.  This
;;; problem cannot arise for defun (as opposed to defun-sk), because the
;;; implementation of simplify-defun does not generate any uses of :instance.

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
  (defun-sk f (x y)
    (forall a (my-if (member-equal a (foo a)) x y)))
  (simplify f
            :simplify-body (my-if @ _ _))
  (must-fail
; I initially wrote the following incorrectly.  The error message was wrong --
; ACL2 complained that the error message isn't an embedded event form.  This is
; actually a problem with defun-sk, with a fix expected in April 2018.  Adding
; this must-fail form actually does no good in regression testing, since
; failure is silent; that is, the must-fail form succeeded quietly even before
; fixing the complaint.  But we include it here as a reminder, and in case one
; wants to test manually.
   (DEFUN-SK F$1 (A)
     (FORALL (A) (MY-IF T X Y))
     :QUANT-OK T))
  (must-be-redundant
   (DEFUN-SK F$1 (X Y)
     (FORALL (A) (MY-IF T X Y))
     :QUANT-OK T))
  )

; Test of preserving prog2$ and cw.
(deftest
  (local (in-theory (disable prog2$-fn))) ; avoid blowing away prog2$
  (defun-sk foo (x)
    (exists y (equal (cons x y)
                     (cons (prog2$ (cw "Hello ~x0 ~x1" x y) (car y))
                           y))))
  (simplify foo)
  (must-be-redundant
   (DEFUN-SK FOO$1 (X)
     (EXISTS (Y)
             (EQUAL X
                    (PROG2$ (CW "Hello ~x0 ~x1" X Y)
                            (CAR Y))))
     :QUANT-OK T)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplify-defun-sk2 tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest
  (include-book "kestrel/soft/top" :dir :system)
  (defunvar ?f1 (* *) => *)
  (defun-sk2 g1[?f1] (x y)
    (forall z
            (equal (cdr (cons 3 (?f1 x z)))
                   (?f1 y z))))
  (simplify g1[?f1])
  (MUST-BE-REDUNDANT
    (DEFUN-SK2 G1[?F1]$1 (X Y)
      (FORALL (Z)
              (EQUAL (?F1 X Z)
                     (?F1 Y Z)))
      :QUANT-OK T)))
