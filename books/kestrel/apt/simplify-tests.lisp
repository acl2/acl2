; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides a few very simple tests of simplify.  Many more tests
; may be found in simplify-defun-tests.lisp and simplify-defun-sk-tests.lisp,
; which also test simplify, since calls of simplify-defun and
; simplify-defun-sk expand immediately into calls of simplify.  In fact,
; these "few very simple tests" are lifted from those two books.

(in-package "ACL2")

(include-book "simplify")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;;; From simplify-defun-tests.lisp (changing "simplify-defun" to
;;; "simplify"):

(deftest
  (defun foo (x) (+ 1 1 x))

  ;; Illegal nesting in pattern
  (must-fail (simplify foo :simplify-body (:@ (+ 1 (:@ (+ 1 x))))))

  ;; Illegal nesting in pattern
  (must-fail (simplify foo :simplify-body (:@ (+ 1 @))))

  ;; No @-vars or calls of :@.
  (must-fail (simplify foo :simplify-body _))
  )

(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (simplify (:eval (car '(foo))))
  (must-be-redundant
    (DEFUN FOO$1 (X) (+ 2 X))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X) (FOO$1 X)))))

;;test show-simplify
(deftest
  (defun foo (x) (+ 1 1 x)) ;;simplifying the body just add 1+1, giving 2
  (must-succeed (show-simplify foo))
  (must-succeed (simplify foo :show-only t)))

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

(deftest
  (defun foo (x)
    (ifix x))
  (simplify foo :assumptions (:eval (list '(integerp x))))
  (must-be-redundant
    (DEFUN FOO$1 (X)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      X)
    (DEFTHM FOO-BECOMES-FOO$1
      (IMPLIES (INTEGERP X)
               (EQUAL (FOO X) (FOO$1 X))))))

(defthm integer-listp-of-cdr
  (implies (integer-listp x)
           (integer-listp (cdr x))))

(defthm integerp-of-car
  (implies (and (not (atom x))
                (integer-listp x))
           (INTEGERP (CAR X))))

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

;; Test a bad argument to :theory (causes an error in tool2, which we catch):
(deftest
  (must-fail (simplify natp :theory '(((f)))))
)

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

  (simplify foo :assumptions ((p0 x)))

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
                (simplify-programmatic 'foo :simplify-body :bad-arg)
                (value (list 'defconst '*c0* (list 'quote (list erp val))))))

  (assert-event (equal *c0* '(:WRONG-FORM NIL)))

  (defun bar (x) x)

  (make-event (mv-let (erp val state)
                (simplify-programmatic 'bar)
                (value (list 'defconst '*c1* (list 'quote (list erp val))))))

  (assert-event (equal *c1* '(:CONDITION-FAILED NIL)))

  )

;;; From simplify-defun-sk-tests.lisp (changing "simplify-defun-sk" to
;;; "simplify"):

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
  (simplify foo)
  (must-be-redundant
    (DEFUN-SK FOO$1 (LST)
      (EXISTS (X) (MEMBER-EQUAL X LST))
      :QUANT-OK T)
    (DEFTHM FOO-BECOMES-FOO$1
      (IFF (FOO LST) (FOO$1 LST)))))

; Test of pattern for :simplify-body (compare with the above; but here we use
; member-equal to avoid the mess we would get from the unsimplified member
; call).
(deftest
  (defun-sk foo (u v)
    (exists (x y) (or (member-equal (cons x y) (fix-true-listp u))
                      (member-equal (cons x y) (fix-true-listp v)))))
  (simplify foo :simplify-body (or _ @))
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
    (forall x (not (member x (fix-true-listp lst))))
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

; Test handling of defun-sk2.
(deftest
  (include-book "kestrel/soft/top" :dir :system)
  (defunvar ?f1 (* *) => *)
  (defun-sk2 g1[?f1] (x y)
    (forall z
            (equal (cdr (cons 3 (?f1 x z)))
                   (?f1 y z))))
  (simplify g1[?f1])
  (must-be-redundant
    (DEFUN-SK2 G1[?F1]$1 (X Y)
      (FORALL (Z)
              (EQUAL (?F1 X Z)
                     (?F1 Y Z)))
      :QUANT-OK T)))

; Next we include tests of the ability to rename local functions to avoid name
; conflicts.

(deftest ; test fn-hyps-name
  (defun foo (x) (if (consp x) (foo (cdr x)) (car (cons x x))))
  (defun abc (x) (true-listp x))
  (defun foo-hyps (x) (stringp x))

; Formerly, before using fresh-logical-name-with-$s-suffix:

; ACL2 Error in ( DEFUN FOO-HYPS ...):  The name FOO-HYPS is in use as
; a function.

  (simplify-defun foo :hyp-fn abc)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (FOO$1 (CDR X)) NIL))))

(deftest ; test hyps-preserved-thm-name
  (defun foo (x) (if (consp x) (foo (cdr x)) (car (cons x x))))
  (defun abc (x) (true-listp x))
  (defun foo-hyps-preserved-for-foo (x) x)

; Formerly, before using fresh-logical-name-with-$s-suffix:

; ACL2 Error in ( DEFTHM FOO-HYPS-PRESERVED-FOR-FOO ...):  The name
; FOO-HYPS-PRESERVED-FOR-FOO is in use as a function.

  (simplify-defun foo :hyp-fn abc)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL))
     (IF (CONSP X) (FOO$1 (CDR X)) NIL))))

(deftest ; test fn-runes-name
  (defun foo (x) (car (cons x x)))
  (defconst *foo-runes* nil)

; Formerly, before using fresh-logical-name-with-$s-suffix:

; ACL2 Error in ( DEFCONST *FOO-RUNES* ...):  The name *FOO-RUNES* is
; in use as a constant.

  (simplify-defun foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     X)))

(deftest ; test before-vs-after-name
  (defun foo (x) (car (cons x x)))
  (defun foo-before-vs-after-0 (x) (list x x))

; Formerly, before using fresh-logical-name-with-$s-suffix:

; ACL2 Error in ( DEFTHM FOO-BEFORE-VS-AFTER-0 ...):  The name
; FOO-BEFORE-VS-AFTER-0 is in use as a function.

  (simplify-defun foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     X)))

(deftest ; test fn-simp-is-fn-lemma-name
  (defun foo (x) (car (cons x x)))
  (defthm foo-becomes-foo$1-lemma (equal x x) :rule-classes nil)

; Formerly, before using fresh-logical-name-with-$s-suffix:

; ACL2 Error in ( DEFTHM FOO-BECOMES-FOO$1-LEMMA ...):  The name
; FOO-BECOMES-FOO$1-LEMMA is in use as a theorem.

  (simplify-defun foo)
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     X)))

; Next we include tests of the :hints argument, for preservation of
; assumptions.

(deftest ; This test is adapted from a similar one in simplify-defun-tests.lisp.
  (defun foo (x)
    (if (atom x)
        nil
      (cons (ifix (first x))
            (foo (rest x)))))
  (simplify foo :assumptions ((integer-listp x))
            :theory '(ifix integerp-of-car)
            :hints ; Find simpler :hints syntax in the next test.
            (:assumptions-preserved (("Goal" :in-theory '(INTEGER-LISTP-of-cdr)))))
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

; Same as just above, but tests simpler syntax for :hints.
(deftest ; This test is adapted from a similar one in simplify-defun-tests.lisp.
  (defun foo (x)
    (if (atom x)
        nil
      (cons (ifix (first x))
            (foo (rest x)))))
  (simplify foo :assumptions ((integer-listp x))
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

(deftest ; This test must fail since :hints is illegal for defun-sk.
  (defun-sk foo (lst)
    (exists x (member-equal x (fix-true-listp lst))))
  (must-fail
   (simplify foo
             :hints (:assumptions-preserved (("Goal" :in-theory (enable nth)))))))

(deftest

; At one time the following test failed, because an invariant check failed for
; directed-untranslate-rec (check-du-inv-fn) due to the way declare forms are
; handled in let, let*, and mv-let.

  (defun foo (x)
    (let ((y (+ 0 x)) (z x))
      (declare (ignore z))
      (+ y y)))

  (simplify foo)

  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :GUARD T
                     :VERIFY-GUARDS NIL))
     (LET ((Y (IF (ACL2-NUMBERP X) X 0)))
          (+ Y Y))))

  (defun foo2 (x x2)
    (declare (type integer x x2))
    (let ((y (+ 0 (* x x))) (y2 (* x2 x2)))
      (declare (type integer y y2))
      (+ y y2)))

  (simplify foo2)

  (must-be-redundant
   (DEFUN FOO2$1 (X X2)
     (DECLARE (XARGS :GUARD (AND (INTEGERP X) (INTEGERP X2))
                     :VERIFY-GUARDS NIL))
     (LET ((Y (* X X)) (Y2 (* X2 X2)))
          (+ Y Y2))))

; It would be nice to add an mv-let test as well.  That seems a bit difficult
; perhaps, probably because of how simplify works to restore let bindings.
  )

; The following will fail if return-last isn't automatically enabled during the
; before-vs-after lemma proof (as is done near the end of the definition of
; simplify-defun-term).
(deftest
  (defun bar (x y) (car (prog2$ (cw "Hello%") (cons x y))))
  (simplify bar)
  (must-be-redundant
   (DEFUND BAR$1 (X Y)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     X)))

; We next test that a bug in untranslate's handling for time$ has been fixed,
; using an example from Eric Smith.  More generally, this test shows how to
; control return-last.
(deftest
  (defun foo (x)
    (time$ (len x)
           :msg "~t0 seconds"
           :args (list 38)))
  (simplify foo)
  (must-be-redundant
   (DEFUN FOO$1 (X) (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL)) (LEN X)))
  (must-be-redundant
   (DEFTHM FOO-BECOMES-FOO$1 (EQUAL (FOO X) (FOO$1 X))))
  (simplify foo :disable time$-fn)
  (must-be-redundant
   (DEFUN FOO$2 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (TIME$ (LEN X)
            :MSG "~t0 seconds"
            :ARGS '(38))))
  (must-be-redundant
   (DEFTHM FOO-BECOMES-FOO$2 (EQUAL (FOO X) (FOO$2 X)))))

(deftest

; Here we check that simplification is considered to have effect in the
; following case: the original function is recursive, simplification of the
; translated body produced a change, and there the untranslated source and
; final functions are identical except for the name change.  Since the
; comparison is on untranslated bodies, we can't use sublis-fn or its variants,
; so we use sublis instead.  Note that soundness is not an issue since we do
; all necessary proofs, and heuristically this should do what we want in
; virtually all cases.  It even does what we want in the case of defun-nx,
; where the untranslated body is of the form (PROG2$ (THROW-NONEXEC-ERROR 'fn
; ...) ...) where fn is the function being defined.

  (defun f1 (x)
    (if (endp x)
        x
      (f1 (cdr x))))
  (must-fail ; Consider checking the error message manually.
   (simplify f1))
  (simplify f1 :must-simplify nil)
  (must-be-redundant
   (DEFUN F1$1 (X)
     (DECLARE (XARGS :GUARD T
                     :MEASURE (ACL2-COUNT X)
                     :VERIFY-GUARDS NIL))
     (IF (ENDP X) X (F1$1 (CDR X)))))
  (mutual-recursion
   (defun f2 (x)
     (if (endp x)
         x
       (f3 (cdr x))))
   (defun f3 (x)
     (if (endp x)
         x
       (f2 (cdr x)))))
  (must-fail ; Consider checking the error message manually.
   (simplify f2))
  (simplify f2 :must-simplify nil)
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F2$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ENDP X) X (F3$1 (CDR X))))
                     (DEFUN F3$1 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ENDP X) X (F2$1 (CDR X))))))
  (simplify f2 :simplify-body nil)
  (must-be-redundant
   (MUTUAL-RECURSION (DEFUN F2$2 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ENDP X) X (F3$2 (CDR X))))
                     (DEFUN F3$2 (X)
                       (DECLARE (XARGS :GUARD T
                                       :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ENDP X) X (F2$2 (CDR X))))))
  (defun-sk f4 (x)
    (exists y (if (endp x) (< x y) (equal x y))))
  (must-fail ; Consider checking the error message manually.
   (simplify f4))
  (simplify f4 :must-simplify nil)
  (defun f5 (x) ; not recursive
    (if (endp x)
        x
      (cons x x)))
  (must-fail ; Consider checking the error message manually.
   (simplify f5))
  (simplify f5 :must-simplify nil)
  (must-be-redundant
   (DEFUN F5$1 (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
     (IF (ENDP X) X (CONS X X))))
  )
