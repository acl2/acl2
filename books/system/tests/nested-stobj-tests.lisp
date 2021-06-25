; Matt Kaufmann and Sol Swords
; Copyright (C) 2013, Regents of the University of Texas
; and
; Copyright (C) 2017, Centaur Technology
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This is a file created to test nested stobjs, i.e., stobj fields of stobjs,
; and stobj-let.  No claim is made about its elegance: in particular, some of
; the function names are kind of funky; and some of the proofs use heavy
; nesting of inductions, suggesting considering formulation of additional
; lemmas.

; See also nested-stobj-errors-input.lsp for additional error testing.

; See also ACL2 community book demos/modeling/nested-stobj-toy-isa.lisp for a
; nicer, self-contained example.

; To run this in the loop in batch mode:
;   :q
;   (push :demo *features*)
;   (lp)
;   (ld "nested-stobj-tests.lisp")

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defmacro local-test (&key defs run check)

; This is a convenient macro for our testing: evaluate defs (using progn rather
; than er-progn, so that we don't get a translate error in the make-event
; form), run a form, and then check that the check is true.

  `(make-event
    (progn
     ,@defs
     (make-event
      (er-progn (trans-eval ',run 'top state t)
                (mv-let (erp val state)
                  (trans-eval ',check 'top state t)
                  (if (and (null erp) val)
                      (value '(value-triple '(value-triple :success)))
                    (er soft 'top "Check failed!"))))))))

; As promised in :doc stobj-let, we begin with an example from that :doc.

; WARNING: Many of these events appear in :DOC NESTED-STOBJS.  If they are
; changed below, then we should make corresponding changes to that :doc topic.

(defstobj kid1 fld1)

(defstobj kid2 fld2)

(defstobj mom
  (kid1-field :type kid1)
  (kid2-ar-field :type (array kid2 (5)))
  last-op)

; We need some lemmas in order to admit mom-swap-fields.

(defthm kid2-ar-fieldp-forward-to-true-list-listp
  (implies (kid2-ar-fieldp x)
           (true-list-listp x))
  :rule-classes :forward-chaining)

(defthm true-listp-nth
  (implies (true-list-listp x)
           (true-listp (nth n x)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth n x)))))

(defthm update-mom-guard-lemma-1
  (implies (kid2-ar-fieldp kid2-ar)
           (equal (cdr (nth index kid2-ar))
                  nil)))

(defthm update-mom-guard-lemma-2
  (implies (and (kid2-ar-fieldp kid2-ar)
                (natp index)
                (< index (len kid2-ar)))
           (consp (nth index kid2-ar))))

; The next function takes a given index and a mom stobj, and swaps the value
; stored in the stobj in mom's kid2-ar-field array at that index with the value
; stored in the stobj in mom's kid1-field field.

(defun mom-swap-fields (index mom)
  (declare (xargs :stobjs mom
                  :guard (and (natp index)
                              (< index (kid2-ar-field-length mom)))))
  (stobj-let
   ((kid1 (kid1-field mom))
    (kid2 (kid2-ar-fieldi index mom)))
   (kid1 kid2)
   (let* ((val1 (fld1 kid1))
          (val2 (fld2 kid2))
          (kid1 (update-fld1 val2 kid1))
          (kid2 (update-fld2 val1 kid2)))
     (mv kid1 kid2))
   (update-last-op 'swap mom)))

; Function mom.kid1-fld1 stores a given value in the given mom's kid1-fld1
; field.

(defun mom.kid1-fld1 (val mom)
  (declare (xargs :stobjs mom))
  (stobj-let
   ((kid1 (kid1-field mom)))
   (kid1)
   (update-fld1 val kid1)
   (update-last-op val mom)))

; (Update-mom op mom) calls mom-swap-fields or mom.kid1-fld1, according to op,
; as is clear from the body of update-mom.

(defun update-mom (op mom)
  (declare (xargs :stobjs mom))
  (cond ((and (consp op)
              (eq (car op) 'swap)
              (natp (cdr op))
              (< (cdr op) (kid2-ar-field-length mom)))
         (mom-swap-fields (cdr op) mom))
        (t (mom.kid1-fld1 op mom))))

; We define a function that checks kid1-field of stobj mom against expected
; value val1, checks the value at the given index of kid1-ar-field of stobj mom
; against expected value val2, and checks the value of the last-op field
; against expected value last-op.

(local-test
 :defs
 ((defun check-update-mom (index val1 val2 last-op mom)
    (declare (xargs :stobjs mom
                    :mode :program
                    :guard
                    (or (null index)
                        (and (natp index)
                             (< index (kid2-ar-field-length mom))))))
    (and (equal (last-op mom) last-op)
         (stobj-let
          ((kid1 (kid1-field mom))
           (kid2 (kid2-ar-fieldi index mom)))
          (val)
          (and (equal val1 (fld1 kid1))
               (equal val2 (fld2 kid2)))
          val))))
 :run
 (let* ((mom ; set mom to (3 (x0 x1 x2 x3 x4))
         (update-mom 3 mom))
        (mom ; set mom to (x1 (x0 3 x2 x3 x4))
         (update-mom '(swap . 1) mom))
        (mom ; set mom to (7 (x0 3 x2 x3 x4))
         (update-mom 7 mom))
        (mom ; set mom to (x0 (7 3 x2 x3 x4))
         (update-mom '(swap . 0) mom))
        (mom ; set mom to (5 (7 3 x2 x3 x4))
         (update-mom 5 mom))
        (mom ; set mom to (7 (5 3 x2 x3 x4))
         (update-mom '(swap . 0) mom)))
   mom)
 :check
 (and (check-update-mom 0 7 5 'swap mom)
      (check-update-mom 1 7 3 'swap mom)))

; This time let's define a function mom-swap-indices, to swap values at two
; distinct indices of the kid2-ar-field array of stobj mom.  In order to do
; that, we need to bind two variables both of "type" kid2; so we define a stobj
; kid2a that is congruent to kid2, to use as a second such stobj-let-bound
; variable in our stobj-let form.

(defstobj kid2a fld2a :congruent-to kid2)

(defun mom-swap-indices (i1 i2 mom)
  (declare (xargs :stobjs mom
                  :guard (and (natp i1)
                              (< i1 (kid2-ar-field-length mom))
                              (natp i2)
                              (< i2 (kid2-ar-field-length mom))
                              (not (equal i1 i2)))))
  (stobj-let
   ((kid2 (kid2-ar-fieldi i1 mom))
    (kid2a (kid2-ar-fieldi i2 mom)))
   (kid2 kid2a)
   (let* ((val2 (fld2 kid2))
          (val2a (fld2 kid2a))
          (kid2 (update-fld2 val2a kid2))
          (kid2a (update-fld2 val2 kid2a)))
     (mv kid2 kid2a))
   mom))

; And finally, here is a checker much like our preceding local-test.  But this
; time we don't want to bother with the effort of verifying guards.  One way to
; avoid that effort is to put the checker in :program mode, and that's what we
; do.

(local-test
 :defs
 ((defun check-update-mom-2 (i j val-i val-j mom)
    (declare (xargs :stobjs mom
                    :mode :program
                    :guard (and (natp j)
                                (< j (kid2-ar-field-length mom))
                                (natp j)
                                (< j (kid2-ar-field-length mom))
                                (not (equal i j)))))
    (stobj-let
     ((kid2 (kid2-ar-fieldi i mom))
      (kid2a (kid2-ar-fieldi j mom)))
     (val)
     (and (equal (fld2 kid2) val-i)
          (equal (fld2a kid2a) val-j))
     val)))
 :run
 (let* ((mom ; set mom to (10 (x0 x1 x2 x3 x4))
         (update-mom 10 mom))
        (mom ; set mom to (x1 (x0 10 x2 x3 x4))
         (update-mom '(swap . 1) mom))
        (mom ; set mom to (20 (x0 10 x2 x3 x4))
         (update-mom 20 mom))
        (mom ; set mom to (x0 (20 10 x2 x3 x4))
         (update-mom '(swap . 0) mom))
        (mom ; set mom to (30 (20 10 x2 x3 x4))
         (update-mom 30 mom))
        (mom ; set mom to (20 (30 10 x2 x3 x4))
         (update-mom '(swap . 0) mom)))
   mom)
 :check
 (check-update-mom-2 0 1 30 10 mom))

; Now we move on to a bunch of little tests.

(defstobj sub1 sub1-fld1)

(defstobj top1 (top1-fld :type sub1))

; It is illegal to call an accessor or updater directly for a stobj field.

(must-fail
 (defun f (top1)
   (declare (xargs :stobjs top1))
   (top1-fld top1)))

(must-fail
 (defun f (sub1 top1)
   (declare (xargs :stobjs (sub1 top1)))
   (update-top1-fld sub1 top1)))

#|| For the following, note:

ACL2 !>:trans1 (stobj-let
		((sub1 (top1-fld top1)))  ; bindings
		(sub1)                    ; producer variables
		(update-sub1-fld1 x sub1) ; producer
		top1)                     ; consumer
 (LET ((SUB1 (TOP1-FLD TOP1)))
      (DECLARE (IGNORABLE SUB1))
      (LET ((SUB1 (CHECK-VARS-NOT-FREE (TOP1)
                                       (UPDATE-SUB1-FLD1 X SUB1))))
           (LET* ((TOP1 (UPDATE-TOP1-FLD SUB1 TOP1)))
                 (CHECK-VARS-NOT-FREE (SUB1) TOP1))))
ACL2 !>

Or in short, without the "decorations":

 (LET ((SUB1 (TOP1-FLD TOP1)))
      (LET ((SUB1 (UPDATE-SUB1-FLD1 X SUB1)))
           (LET ((TOP1 (UPDATE-TOP1-FLD SUB1 TOP1)))
                TOP1)))

||#

(defun top1-fld.update-fld1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (sub1)
   (update-sub1-fld1 x sub1)
   top1))

(local-test
 :defs
 ((defun f1 (x top1)
    (declare (xargs :stobjs top1))
    (stobj-let
     ((sub1 (top1-fld top1)))
     (val)
     (sub1-fld1 sub1)
     (equal val x))))
 :run
 (top1-fld.update-fld1 17 top1)
 :check
 (f1 17 top1))

; Test inlining and congruence together:

(local-test
 :defs
 ((defun f1 (x top1)
    (declare (xargs :stobjs top1))
    (stobj-let
     ((sub1 (top1-fld top1)))
     (val)
     (sub1-fld1 sub1)
     (equal val x)))
  (defstobj top1-inline
    (top1-fld-inline :type sub1)
    :inline t
    :congruent-to top1))
 :run
 (top1-fld.update-fld1 18 top1-inline)
 :check
 (f1 18 top1-inline))

; Introduce a stobj sub1a that is congruent to sub1.
(defstobj sub1a sub1a-fld1 :congruent-to sub1)

(defun new-top1-fld.update-fld1 (x top1)
; Note that use of a congruent stobj: sub1a in place of sub1.
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1a (top1-fld top1)))
   (sub1a)
   (update-sub1-fld1 x sub1a)
   top1))

(defstobj top2
; This stobj has two fields of the same type, which is fine.
  (top2-fld1 :type sub1)
  (top2-fld2 :type sub1))

(defun top2.test1 (top2)
; In order to bind two stobjs to fields of the same type, we use a congruent
; stobj, binding sub1 and sub1a.
  (declare (xargs :stobjs top2))
  (stobj-let ((sub1 (top2-fld1 top2))
              (sub1a (top2-fld2 top2)))
             (sub1 sub1a)
             (let* ((sub1 (update-sub1-fld1 3 sub1))
                    (sub1a (update-sub1-fld1 4 sub1a)))
               (mv sub1 sub1a))
             top2))

(must-fail
; Error: This is just like top2.test1 above, except that this time the
; stobj-let bindings fail to include sub1a.
 (defun top2.test1-bad (top2)
   (declare (xargs :stobjs top2))
   (stobj-let ((sub1 (top2-fld1 top2)))
              (sub1 sub1a)
              (let* ((sub1 (update-sub1-fld1 3 sub1))
                     (sub1a (update-sub1-fld1 4 sub1a)))
                (mv sub1 sub1a))
              top2)))

(defstobj sub2 sub2-fld1) ; Note: *not* congruent to sub1

(must-fail
; Error: Same as top1-fld.update-fld1 and new-top1-fld.update-fld1, except that
; we operate on sub2 where we should be operating on sub1 or sub1a.  (Note that
; unlike sub1a, sub2 is not congruent to sub1.)
 (defun newer-top1-fld.update-fld1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub2 (top1-fld top1)))
   (sub2)
   (update-sub1-fld1 x sub2)
   top1)))

; A stobj with an array field:
(defstobj top3 (top3-fld :type (array sub1 (10))))

(defconst *i1* 1)
(defconst *i2* 2)

(local-test
; This is just a simple test of array update in a stobj field of a stobj.
; It uses constants just to make this a bit more interesting.
 :defs
 ((defun f1 (top3)
    (declare (xargs :stobjs top3))
    (stobj-let ((sub1 (top3-fldi *i1* top3))
                (sub1a (top3-fldi *i2* top3)))
               (sub1 sub1a)
               (let* ((sub1 (update-sub1-fld1 'x sub1))
                      (sub1a (update-sub1-fld1 'y sub1a)))
                 (mv sub1 sub1a))
               top3))
  (defun f2 (top3)
    (declare (xargs :stobjs top3))
    (stobj-let ((sub1 (top3-fldi *i1* top3))
                (sub1a (top3-fldi *i2* top3)))
               (val1 val2)
               (mv (sub1-fld1 sub1) (sub1-fld1 sub1a))
               (and (eq val1 'x)
                    (eq val2 'y)))))
 :run
 (f1 top3)
 :check
 (f2 top3))

(local-test
; This is similar to the above, but with numbers instead of constants for the
; indices.
 :defs
 ((defun f1 (top3)
    (declare (xargs :stobjs top3))
    (stobj-let ((sub1 (top3-fldi 3 top3))
                (sub1a (top3-fldi 4 top3)))
               (sub1 sub1a)
               (let* ((sub1 (update-sub1-fld1 'a sub1))
                      (sub1a (update-sub1-fld1 'b sub1a)))
                 (mv sub1 sub1a))
               top3))
  (defun f2 (top3)
    (declare (xargs :stobjs top3))
    (stobj-let ((sub1 (top3-fldi 3 top3))
                (sub1a (top3-fldi 4 top3)))
               (val3 val4)
               (mv (sub1-fld1 sub1) (sub1-fld1 sub1a))
               (and (eq val3 'a)
                    (eq val4 'b)))))
 :run
 (f1 top3)
 :check
 (f2 top3))

(must-fail
; The producer updates a stobj field, but the parent stobj is not returned.
 (defun foo (top3)
   (declare (xargs :stobjs top3))
   (stobj-let ((sub1 (top3-fldi 5 top3)))
              (sub1)
              (update-sub1-fld1 'x sub1) ; producer
              (top3p top3))))

(must-fail
; This is similar to the preceding test, but for more than one producer
; variable.
 (defun foo (top3)
   (declare (xargs :stobjs top3))
   (stobj-let ((sub1 (top3-fldi 5 top3))
               (sub1a (top3-fldi 6 top3)))
              (sub1 sub1a)
              (let* ((sub1 (update-sub1-fld1 'x sub1))
                     (sub1a (update-sub1-fld1 'x sub1a)))
                (mv sub1 sub1a))
              (top3p top3))))

(must-fail
; Don't allow the same index to occur twice.  Otherwise we get the problem
; shown in a comment just below.
 (defun foo (top3)
   (declare (xargs :stobjs top3))
   (stobj-let ((sub1 (top3-fldi 5 top3))
               (sub1a (top3-fldi 5 top3)))
              (sub1 sub1a)
              (let* ((sub1a (update-sub1-fld1 'x sub1a))
                     (sub1 (update-sub1-fld1 'y sub1)))
                (mv sub1 sub1a))
              top3)))

#||
; NOT TRUE!  But proves without the no-duplicatesp check generated by
; expanding the stobj form, after admitting foo just aBove.
(thm (implies (top3p top3)
              (let ((top3 (foo top3)))
                (stobj-let ((sub1 (top3-fldi 5 top3)))
                           (val)
                           (sub1-fld1 sub1)
                           (equal val 'x)))))

||#

; Here come some lemmas to help with guard verification of
; top3.fldi.update-sub1-fld1/i1/i2, defined below.  Maybe it would be good to
; create a library of helpful lemmas for reasoning about nested stobjs.

#|| ; optional
(defthm sub1p-open
  (equal (sub1p x)
         (and (consp x)
              (null (cdr x))))
  :hints (("Goal" :expand ((len x) (len (cdr x))))))
||#

(defthm sub1p-update-sub1-fld1-lemma
  (implies (sub1p sub1)
           (sub1p (update-sub1-fld1 any sub1))))

(defthm sub1p-nth
  (implies (and (top3-fldp x)
                (natp index)
                (< index (len x)))
           (sub1p (nth index x))))

(in-theory (disable sub1p update-sub1-fld1))

(defthm sub1p-top3-fldi
  (implies (and (top3p top3)
                (natp index)
                (< index 10))
           (sub1p (top3-fldi index top3))))

(defthm sub1p-update-sub1-fld1
  (implies (and (top3p top3)
                (natp index)
                (< index 10))
           (sub1p (update-sub1-fld1 any
                                    (top3-fldi index top3)))))

(defun top3.fldi.update-sub1-fld1/i1/i2 (i1 v1 i2 v2 top3)
; Here we update an stobj array field of a stobj, at two distinct indices.
  (declare (type (integer 0 9) i1 i2)
           (xargs :stobjs top3
                  :guard (not (eql i1 i2))))
  (stobj-let ((sub1 (top3-fldi i1 top3))
              (sub1a (top3-fldi i2 top3)))
             (sub1 sub1a)
             (let* ((sub1a (update-sub1-fld1 v2 sub1a))
                    (sub1 (update-sub1-fld1 v1 sub1)))
               (mv sub1 sub1a))
             top3))

(must-fail
; This is as above, except we omit the requirement that i1 and i2 are distinct.
 (defun top3.fldi.update-sub1-fld1/i1/i2 (i1 v1 i2 v2 top3)
   (declare (type (integer 0 9) i1 i2)
            (xargs :stobjs top3
                   ;; :guard (not (eql i1 i2))
                   ))
   (stobj-let ((sub1 (top3-fldi i1 top3))
               (sub1a (top3-fldi i2 top3)))
              (sub1 sub1a)
              (let* ((sub1a (update-sub1-fld1 v2 sub1a))
                     (sub1 (update-sub1-fld1 v1 sub1)))
                (mv sub1 sub1a))
              top3)))

(must-fail
; This is as above, except we omit the requirement that i2 is in range.
 (defun top3.fldi.update-sub1-fld1/i1/i2 (i1 v1 i2 v2 top3)
   (declare (type (integer 0 9) i1) ; i2
            (xargs :stobjs top3
                   :guard (not (eql i1 i2))))
   (stobj-let ((sub1 (top3-fldi i1 top3))
               (sub1a (top3-fldi i2 top3)))
              (sub1 sub1a)
              (let* ((sub1a (update-sub1-fld1 v2 sub1a))
                     (sub1 (update-sub1-fld1 v1 sub1)))
                (mv sub1 sub1a))
              top3)))

(local-test
; Let's try our new function and check the result.
 :defs
 ((defun f1 (top3)
    (declare (xargs :stobjs top3))
    (stobj-let ((sub1 (top3-fldi 3 top3))
                (sub1a (top3-fldi 4 top3)))
               (v1 v2)
               (let* ((v2 (sub1-fld1 sub1a))
                      (v1 (sub1-fld1 sub1)))
                 (mv v1 v2))
               (and (equal v1 'three)
                    (equal v2 'four)))))
 :run
 (top3.fldi.update-sub1-fld1/i1/i2 3 'three 4 'four top3)
 :check
 (f1 top3))

; J Moore has wondered whether we can subvert the check-vars-not-free for the
; parent stobj around the producer, by binding another stobj to the parent
; about the stobj-let and then modifying that stobj.  The following examples
; illustrate an important fact: One cannot bind a stobj to another stobj (even
; a congruent one) using let or mv-let.

(defstobj top1a
  (top1a-fld :type sub1)
; Here we have a congruent stobj with stobj fields.
  :congruent-to top1)

(must-fail
 (defstobj top1b
   (top1b-fld :type sub1a)
; Fails, because the field types don't match (even though they are congruent):
; sub1a here, sub1 in top1.
   :congruent-to top1))

(must-fail (trans-eval '(let ((top1a top1))
                          top1a)
                       'top state t))

(must-fail (trans-eval '(mv-let (top1a x)
                                (mv top1 3)
                                (mv top1a x))
                       'top state t))

(must-fail
; Nested stobjs cannot have fields of type state.
 (defstobj top1-bad (top1-bad-fld :type state)))

(must-fail
; Nested stobjs cannot have a field that is state (this is goofy actually).
 (defstobj bad-stobj state))

; We can define abstract stobjs for concrete stobjs with stobj fields.
; There is a bit of an issue, though.  If we uncomment the first export in the
; defabsstobj below, we get the following error (and there is also such an
; error if we uncomment the second export instead).

#||
ACL2 Error in ( DEFABSSTOBJ TOP1{ABS} ...):  The output signatures
of the :LOGIC and :EXEC functions for a field must have the same length
and must agree at each position, except for the position of concrete
stobj (TOP1) in the outputs of the :EXEC function.  For that position,
the :LOGIC function should return the type of the object (stobj or
not) that is at the position of TOP1 in the inputs of the :EXEC function.
However, the criteria above are not all met for field
(TOP1{ABS}-FLD :LOGIC TOP1-FLD$A :EXEC TOP1-FLD), as the output signatures
are as follows.

TOP1-FLD$A (:LOGIC):
(*)

TOP1-FLD (:EXEC):
(SUB1)
||#

; We can probably get around this issue for updaters by passing the sub-stobj
; in as a stobj argument to the :logic version of the updater.  But for
; accessors, I don't see a workaround at this point.  If it becomes an issue, I
; can think about relaxing requirements such as the above, perhaps by declaring
; the :logic function non-executable if that becomes necessary (though that
; could be unfortunate for proofs).

; First, recall:
; (defstobj top1 (top1-fld :type sub1))

(defun top1$ap (x)
  (declare (xargs :guard t))
  (sub1p x))

(defun create-top1$a ()
  (declare (xargs :guard t))
  '(nil))

(defun-nx corr (concrete abs)
  (equal (car concrete) abs))

(defun top1-fld$a (x)
  (declare (xargs :guard (top1$ap x)
                  :verify-guards t))
  x)

(defun update-top1-fld$a (v x)
  (declare (xargs :guard (and (sub1p v)
                              (top1$ap x))
                  :verify-guards t))
  (declare (ignore x))
  v)

(defun top1-fld.update-fld1$a (x top1)
  (declare (xargs :guard
                  (top1$ap top1)
                  :guard-hints
                  (("Goal" :expand ((sub1p top1)
                                    (sub1p (cons x (cdr top1))))))))
  (let* ((sub1 (top1-fld$a top1))
         (sub1 (update-nth 0 x sub1)))
    (update-top1-fld$a sub1 top1)))

(DEFTHM CREATE-TOP1{ABS}{CORRESPONDENCE}
        (CORR (CREATE-TOP1) (CREATE-TOP1$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-TOP1{ABS}{PRESERVED}
        (TOP1$AP (CREATE-TOP1$A))
        :RULE-CLASSES NIL)

(DEFTHM TOP1{ABS}-FLD.UPDATE-FLD1{CORRESPONDENCE}
        (IMPLIES (AND (CORR TOP1 TOP1{ABS})
                      (TOP1$AP TOP1{ABS}))
                 (CORR (TOP1-FLD.UPDATE-FLD1 X TOP1)
                       (TOP1-FLD.UPDATE-FLD1$A X TOP1{ABS})))
        :hints (("Goal"
                 :in-theory (enable update-sub1-fld1)))
        :RULE-CLASSES NIL)

(DEFTHM TOP1{ABS}-FLD.UPDATE-FLD1{PRESERVED}
        (IMPLIES (TOP1$AP TOP1{ABS})
                 (TOP1$AP (TOP1-FLD.UPDATE-FLD1$A X TOP1{ABS})))
        :hints (("Goal" :expand ((:free (x) (sub1p x)))))
        :RULE-CLASSES NIL)

(defabsstobj top1{abs}
  :foundation top1
  :recognizer (top1{abs}p :exec top1p :logic top1$ap)
  :creator (create-top1{abs} :exec create-top1 :logic create-top1$a)
  :corr-fn corr
  :exports
; See the comments about "a bit of an issue" for why the next two lines are
; commented out.
  (;; (top1{abs}-fld :logic top1-fld$a :exec top1-fld)
   ;; (update-top1{abs}-fld :logic update-top1-fld$a :exec update-top1-fld)
   (top1{abs}-fld.update-fld1
    :logic top1-fld.update-fld1$a
    :exec top1-fld.update-fld1)))

; Let's look at printing of error messages regarding stobj fields (as opposed
; to global stobjs).  WARNING: Do not delete from here through the local-test
; form just below, as these events support a comment in
; defstobj-field-fns-raw-defs.

(defun stobj-er-test-aux (x sub1)
  (declare (xargs :stobjs sub1 :guard (consp x)))
  (mv (car x) sub1))

(defun stobj-er-test (x top1)
  (declare (xargs :stobjs top1 :verify-guards nil))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (val sub1)
   (stobj-er-test-aux x sub1)
   top1))

(local-test
; No guard violation, so this succeeds:
 :defs
 ((defun f1 (top1)
    (declare (xargs :stobjs top1 :verify-guards nil))
    (stobj-er-test '(4 5) top1)))
 :run
 (f1 top1)
 :check
 t)

(must-fail
; And now the error message:
 (local-test
  :defs
  ((defun f1 (top1)
     (declare (xargs :stobjs top1 :verify-guards nil))
     (stobj-er-test '3 top1)))
  :run
  (with-guard-checking t (f1 top1))
  :check
  t))

; Let's look at the error message when we attempt to call trans-eval in the
; context of a stobj-let.  (Maybe it would be better to cause the error
; statically, but imagine replacing trans-eval with a function that calls
; trans-eval.  Tracing all that down might be awkward.)

(must-fail
 (defun bad-top1-fld.update-fld1 (top1 state)
   (declare (xargs :mode :program :stobjs (top1 state)))
   (stobj-let
    ((sub1 (top1-fld top1)))
    (erp val state)
    (update-sub1-fld1 17 sub1)
    (mv erp val state))))

#||
ACL2 !>(bad-top1-fld.update-fld1 top1 state)


ACL2 Error in ACL2-INTERFACE:  It is illegal to run ACL2 evaluators
trans-eval and simple-translate-and-eval on any term that mentions
a stobj that has been bound by with-local-stobj.  The reason is that
those evaluators expect each stobj to match perfectly the corresponding
global stobj that is stored in the ACL2 state.  The offending stobj
name is:  SUB1.


***********************************************
************ ABORTING from raw Lisp ***********
Error:  ACL2 Halted
***********************************************

To enable breaks into the debugger (also see :DOC acl2-customization):
(SET-DEBUGGER-ENABLE T)
ACL2 !>
||#

; How are stobj-let-bound stobjs printed by tracing?

#+demo
(trace$ update-sub1-fld1)
#+demo
(top1-fld.update-fld1 17 top1)

; Next, let's test interaction of local stobjs and stobj-let.

(defun top1-fld.fld1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (val)
   (sub1-fld1 sub1)
   val))

; Stobj-let in the scope of with-local-stobj:
(local-test
 :defs
 ((defun f1 (x)
    (with-local-stobj
     top1
     (mv-let (val top1)
             (let* ((top1 (stobj-let
                           ((sub1 (top1-fld top1)))
                           (sub1)
                           (update-sub1-fld1 x sub1)
                           top1))
                    (val  (stobj-let
                           ((sub1 (top1-fld top1)))
                           (val)
                           (sub1-fld1 sub1)
                           val)))
               (mv val top1))
             val))))
 :run
 (top1-fld.update-fld1 17 top1)
 :check
 (and (eql (f1 3) 3)
      (eql (top1-fld.fld1 top1) 17)))

; Implementation note: Now that we've tested (f1 3) above, which takes
; advantage of live-stobj binding in the handling of stobj-let in oneify, we
; turn off tracing.
#+demo
(untrace$)

; Next, with-local-stobj is in the scope of stobj-let.  The inner update of
; top1 is irrelevant.
(local-test
 :defs
 ((defun f1 (x y top1) ; y is irrelevant
    (declare (xargs :stobjs top1))
    (stobj-let
     ((sub1 (top1-fld top1)))
     (sub1)
     (with-local-stobj top1
                       (mv-let (sub1 top1)
                               (let ((top1 (top1-fld.update-fld1 y top1)))
                                 (let ((sub1 (update-sub1-fld1 x sub1)))
                                   (mv sub1 top1)))
                               sub1))
     top1)))
 :run
 (f1 10 20 top1)
 :check
 (eql (top1-fld.fld1 top1) 10))

; With-local-stobj in the scope of stobj-let, as above; but this time we update
; top1 and sub1 in the opposite order.  The inner update of top1 is still
; irrelevant.
(local-test
 :defs
 ((defun f1 (x y top1) ; y is irrelevant
    (declare (xargs :stobjs top1))
    (stobj-let
     ((sub1 (top1-fld top1)))
     (sub1)
     (with-local-stobj top1
                       (mv-let (sub1 top1)
                               (let ((sub1 (update-sub1-fld1 x sub1)))
                                 (let ((top1 (top1-fld.update-fld1 y top1)))
                                   (mv sub1 top1)))
                               sub1))
     top1)))
 :run
 (f1 30 40 top1)
 :check
 (eql (top1-fld.fld1 top1) 30))

; Next, a silly test just to check that we are paying attention to particular
; stobj types.

(defstobj top4
  (top4-fld1 :type sub1)
  (top4-fld2 :type sub2))

(defun top4.test1 (top4)
  (declare (xargs :stobjs top4))
  (stobj-let ((sub1 (top4-fld1 top4))
              (sub2 (top4-fld2 top4)))
             (sub1 sub2)
             (let* ((sub1 (update-sub1-fld1 3 sub1))
                    (sub2 (update-sub2-fld1 4 sub2)))
               (mv sub1 sub2))
             top4))

; As above, but fields are switched.  We use skip-proofs in order to be
; confident that the error is from translation, rather from a proof failure.
(must-fail
 (skip-proofs
  (defun bad-top4.test1 (top4)
    (declare (xargs :stobjs top4))
    (stobj-let ((sub2 (top4-fld1 top4))
                (sub1 (top4-fld2 top4)))
               (sub1 sub2)
               (let* ((sub1 (update-sub1-fld1 3 sub1))
                      (sub2 (update-sub2-fld1 4 sub2)))
                 (mv sub1 sub2))
               top4))))

; Resizability is OK.

(defstobj top3a (top3a-fld :type (array sub1 (10))
                           :resizable t))

(must-fail
 (defun top3a.fldi.update-sub1-fld1/i1/i2 (i1 v1 i2 v2 top3a)
; This succeeded for top3.  But now the size could be less than 10 after
; resizing.
   (declare (type (integer 0 9) i1 i2)
            (xargs :stobjs top3a
                   :guard (not (eql i1 i2))))
   (stobj-let ((sub1 (top3a-fldi i1 top3a))
               (sub1a (top3a-fldi i2 top3a)))
              (sub1 sub1a)
              (let* ((sub1a (update-sub1-fld1 v2 sub1a))
                     (sub1 (update-sub1-fld1 v1 sub1)))
                (mv sub1 sub1a))
              top3a)))

; Towards admitting top3a.fldi.update-sub1-fld1/i1/i2:

(in-theory (enable sub1p update-sub1-fld1))

(defthm true-listp-update-sub1-fld1
  (implies (true-listp x)
           (true-listp (update-sub1-fld1 v1 x))))

#||
(defthm sub1p-member-top3a-fldp
  (implies (and (top3a-fldp x)
                (natp i)
                (< i (len x)))
           (sub1p (nth i x))))

(defthm sub1p-member-car-top3a
  (implies (and (top3ap top3a)
                (natp i)
                (< i (len (car top3a))))
           (sub1p (nth i (car top3a)))))
||#

(defthm true-listp-cdr-nth-i-car-top3a
  (implies (and (top3ap top3a)
                (natp i)
                (< i (len (car top3a))))
           (equal (cdr (nth i (car top3a)))
                  nil)))

(defun top3a.fldi.update-sub1-fld1/i1/i2 (i1 v1 i2 v2 top3a)
; Here we replace the type declaration just above with a suitable extension of
; the guard.
   (declare (xargs :stobjs top3a
                   :guard (and (natp i1)
                               (natp i2)
                               (< i1 (top3a-fld-length top3a))
                               (< i2 (top3a-fld-length top3a))
                               (not (eql i1 i2)))
                   :guard-hints (("Goal" :in-theory (enable sub1p)))))
   (stobj-let ((sub1 (top3a-fldi i1 top3a))
               (sub1a (top3a-fldi i2 top3a)))
              (sub1 sub1a)
              (let* ((sub1a (update-sub1-fld1 v2 sub1a))
                     (sub1 (update-sub1-fld1 v1 sub1)))
                (mv sub1 sub1a))
              top3a))

(defun top3a.sub1-fld1/i (i top3a)
; Here we replace the type declaration just above with a suitable extension of
; the guard.
   (declare (xargs :stobjs top3a
                   :guard (and (natp i)
                               (< i (top3a-fld-length top3a)))
                   :guard-hints (("Goal" :in-theory (enable sub1p)))))
   (stobj-let ((sub1 (top3a-fldi i top3a)))
              (val)
              (sub1-fld1 sub1)
              val))

(local-test
 :defs
 nil
 :run
 (let ((top3a (resize-top3a-fld 20 top3a)))
   (top3a.fldi.update-sub1-fld1/i1/i2 3 'three 15 'fifteen top3a))
 :check
 (and (equal (top3a.sub1-fld1/i 15 top3a) 'fifteen)
; Check that new array elements after resizing don't share structure.
      (equal (top3a.sub1-fld1/i 16 top3a) nil)))

; Next, test stobj fields of stobj fields of stobjs.

(defstobj super1 (super1-fld :type top1))

(defun super1-update (x super1)
  (declare (xargs :stobjs super1))
  (stobj-let
   ((top1 (super1-fld super1)))
   (top1)
   (stobj-let
    ((sub1 (top1-fld top1)))
    (sub1)
    (update-sub1-fld1 x sub1)
    top1)
   super1))

(defun super1-access (super1)
  (declare (xargs :stobjs super1))
  (stobj-let
   ((top1 (super1-fld super1)))
   (val)
   (stobj-let
    ((sub1 (top1-fld top1)))
    (val)
    (sub1-fld1 sub1)
    val)
   val))

(local-test
 :defs
 nil
 :run
 (super1-update 'abc super1)
 :check
 (eq (super1-access super1) 'abc))

; Test :renaming.

(defstobj top1c (top1c-fld :type sub1)
  :renaming ((top1c-fld get-top1c-sub1)
             (update-top1c-fld set-top1c-sub1))
  :congruent-to top1)

(local-test
 :defs
 ((defun f1 (x top1c)
    (declare (xargs :stobjs top1c))
    (stobj-let
     ((sub1 (get-top1c-sub1 top1c) set-top1c-sub1))
     (val)
     (sub1-fld1 sub1)
     (equal val x))))
 :run
 (top1-fld.update-fld1 17 top1c)
 :check
 (f1 17 top1c))

; Test the case where stobj fields are abstract stobjs.

; Fails in Version 6.2: Bug from :doc note-6-3 says "Fixed a bug in the case of
; a field of a (concrete) stobj that is an abstract stobj".
(defstobj parent
  (abs-child :type top1{abs}))

; We do some tests involving the :non-memoizable argument of defstobj.

(must-fail ; Fails because kid2a has :NON-MEMOIZABLE T, unlike kid2.
 (defstobj kid2a fld2a
   :congruent-to kid2
   :non-memoizable t))

(must-fail ; Fails because kid2a has :NON-MEMOIZABLE T, unlike kid2.
 (defstobj new-mom
   (new-kid1-field :type kid1)
   (new-kid2-ar-field :type (array kid2 (5)))
   new-last-op
   :non-memoizable t))

(defstobj kid2b fld2b
   :non-memoizable t)

(defstobj new-mom ; It's fine to be memoizable even when some child is not.
   (new-kid1-field :type kid1)
   (new-kid2-ar-field :type (array kid2b (5)))
   new-last-op)

;;; The next example illustrates a soundness bug (now fixed): With the
;;; must-fail wrapper removed below, this proof of nil succeeded in Version 7.4
;;; (and probably many preceding versions).

(encapsulate () (local (progn

(defstobj a (a-fld))

(defstobj aa (aa-fld) :congruent-to a)

(defstobj c
  (c-a :type a))

;; just returns the a-fld of the c-a of c
(defun c-a-fld (c)
  (declare (xargs :stobjs c))
  (stobj-let
   ((a (c-a c)))
   (x)
   (a-fld a)
   x))

(must-fail
 (progn
   ;; Logically, gets the C-A field of C as both A and AA; modifies A by negating
   ;; its A-FLD, then updates the C-A field of C with A, but then again with AA,
   ;; which hasn't been changed.
   ;; Execution actually negates the A-FLD of the C-A field of C.
   (defun c-hidden-a-fld-update (c)
     (declare (xargs :stobjs c))
     (stobj-let
      ((a (c-a c))
       (aa (c-a c)))
      (a aa)
      (let* ((a (update-a-fld (not (a-fld a)) a)))
        (mv a aa))
      c))

   ;; Returns the equality of the C-A-FLD before and after the hidden update.
   ;; This will be true in the logic and false in execution.
   (defun true-and-false ()
     (declare (xargs :guard t))
     (with-local-stobj c
       (mv-let (x c)
         (let* ((before (c-a-fld c))
                (c (c-hidden-a-fld-update c))
                (after (c-a-fld c)))
           (mv (equal after before) c))
         x)))

   (defthm true-and-false-is-true
     (true-and-false)
     :hints(("Goal" :in-theory (disable (true-and-false)
                                        (c-a-fld)
                                        (c-hidden-a-fld-update)))))

   (defthm true-and-false-is-contradictory
     nil
     :hints (("goal" :use true-and-false-is-true
              :in-theory (disable true-and-false-is-true)))
     :rule-classes nil)))
)))

;;; The next test illustrates another soundness bug in ACL2 7.4 (and probably
;;; several preceding versions), in which the final defthm -- a proof of nil --
;;; succeeded.  The problem again pertained to aliasing; see comments below.
;;; This time we exploit a lack of guard verification for logic-mode functions.
;;; (An initial bug fix for the issue shown in the preceding example didn't
;;; handle this case.)

(encapsulate () (local (progn

(defstobj a (a-fld))

(defstobj aa (aa-fld) :congruent-to a)

(defstobj c
  (as :type (array a (2))))

(defun c-a-fld (c)
  (declare (xargs :stobjs c))
  (stobj-let
   ((a (asi 0 c)))
   (x)
   (a-fld a)
   x))

(defun c-hidden-a-fld-update (i j c)

; Below, a and aa refer to the same stobj when i = j, and that aliasing is
; problematic.  We now do a robust check to ensure at runtime that this can't
; happen.

  (declare (xargs :stobjs c :verify-guards nil))
  (stobj-let
   ((a (asi i c))
    (aa (asi j c)))
   (a aa)
   (let* ((a (update-a-fld (not (a-fld a)) a)))
     (mv a aa))
   c))

(defun true-and-false ()
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj c
    (mv-let (x c)
      (let* ((before (c-a-fld c))
             (c (c-hidden-a-fld-update 0 0 c))
             (after (c-a-fld c)))
        (mv (equal after before) c))
      x)))

(defthm true-and-false-is-true
  (true-and-false)
  :hints(("Goal" :in-theory (disable (true-and-false)
                                     (c-a-fld)
                                     (c-hidden-a-fld-update)))))

(must-fail
 (defthm true-and-false-is-contradictory-2
   nil
   :hints (("goal" :use true-and-false-is-true
            :in-theory (disable true-and-false-is-true)))
   :rule-classes nil))
)))

;;; The next test also illustrates potential unsoundness, which occurred with a
;;; preliminary fix for the kind of aliasing behavior that took place in the
;;; preceding test.

(encapsulate () (local (progn

(defstobj n (n-fld :type (integer 0 *) :initially 0))
(defstobj nn (nn-fld :type (integer 0 *) :initially 0)
  :congruent-to n)

(defun violate-invariant-if-aliased (n nn)
  (declare (xargs :stobjs (n nn)))
  (let* ((nfld1 (n-fld n))
         (nn (update-n-fld (+ 1 (n-fld nn)) nn))
         (nfld2 (n-fld n)))
    (if (equal nfld1 nfld2) ;; always true unless aliased
        nn
      (update-n-fld -1 nn))))

(defstobj n-arr
  (ns :type (array n (2))))

(defun cause-invariant-violation (i j n-arr)
  (declare (xargs :stobjs n-arr
                  :verify-guards nil))
  (stobj-let
   ((n (nsi i n-arr))
    (nn (nsi j n-arr)))
   (nn)
   (violate-invariant-if-aliased n nn)
   n-arr))

(defun cause-invariant-violation-program (n-arr)
  (declare (xargs :mode :program
                  :stobjs (n-arr)))
  (cause-invariant-violation 1 1 n-arr))

(defun n-arr-has-natp-field (n-arr)
  (declare (xargs :stobjs (n-arr)
                  :guard-hints (("goal" :expand ((nsp (car n-arr)))))))
  (stobj-let
   ((n (nsi 1 n-arr)))
   (ok)
   (mbe :logic t
        :exec (natp (n-fld n)))
   ok))

(defthm n-arr-has-natp-field-true
  (n-arr-has-natp-field n-arr))

(must-fail

; The following should cause an error, or else the next assertion coudl fail:

 (cause-invariant-violation-program n-arr)
 :expected :hard)

; In Version 7.4 this assertion failed, showing that stobj recognizer n-arrp is
; false for the live n-arr.
(assert! (n-arr-has-natp-field n-arr))

)))

;;; The next test shows how congruent stobjs may be used in stobj-let.

(encapsulate () (local (progn

(defstobj a (a-fld))
(defstobj b (b-fld))

(defstobj d
  (d-a :type a)
  (d-b :type b))

(defstobj dd
  (dd-a :type a)
  (dd-b :type b)
  :congruent-to d)

(defun access-dd-as-d (dd)
  (declare (xargs :stobjs dd))
  (stobj-let
   ((a (d-a dd))
    (b (d-b dd)))
   (x)
   (list (a-fld a) (b-fld b))
   x))

(defun update-dd-as-d (dd)
  (declare (xargs :stobjs dd))
  (stobj-let
   ((a (d-a dd))
    (b (d-b dd)))
   (a b)
   (let* ((afld (a-fld a))
          (bfld (b-fld b))
          (a (update-a-fld bfld a))
          (b (update-b-fld (not afld) b)))
     (mv a b))
   dd))

;; want these both to remain illegal
(must-fail
 (defun access-dd-as-both (dd)
   (declare (xargs :stobjs dd))
   (stobj-let
    ((a (d-a dd))
     (b (dd-b dd)))
    (x)
    (list (a-fld a) (b-fld b))
    x))
 :with-output-off nil)

(defstobj aa (aa-fld) :congruent-to a)

(must-fail
 (defun access-dd-as-both-aliasing (dd)
   (declare (xargs :stobjs dd))
   (stobj-let
    ((a (d-a dd))
     (aa (dd-a dd)))
    (x)
    (list (a-fld a) (a-fld aa))
    x))
 :with-output-off nil)

;; want this to remain legal

(defstobj a-arr
  (as :type (array a (2))))

(defun access-a-arr (n m a-arr)
  (declare (xargs :stobjs a-arr
                  :guard (and (natp n)
                              (natp m)
                              (< n 2)
                              (< m 2)
                              (not (eql n m)))))
  (stobj-let
   ((a (asi n a-arr))
    (aa (asi m a-arr)))
   (x)
   (list (a-fld a) (a-fld aa))
   x))

;; want this to be legal
(defstobj aa-arr
  (aas :type (array a (2)))
  :congruent-to a-arr)

(defun access-aa-arr-as-a-arr (n m aa-arr)
  (declare (xargs :stobjs aa-arr
                  :guard (and (natp n)
                              (natp m)
                              (< n 2)
                              (< m 2)
                              (not (eql n m)))))
  (stobj-let
   ((a (asi n aa-arr))
    (aa (asi m aa-arr)))
   (x)
   (list (a-fld a) (a-fld aa))
   x))

;; This formerly failed its guard verification because aliasing in array
;; accesses is possible when n = m.  But starting in May 2021 (at the same time
;; that ACL2 was changed to support stobj fields of abstract stobjs), such
;; aliasing is permitted provided there is no updating involved.
(defun access-aa-arr-as-a-arr-with-possible-aliasing (n m aa-arr)
  (declare (xargs :stobjs aa-arr
                  :guard (and (natp n)
                              (natp m)
                              (< n 2)
                              (< m 2))))
  (stobj-let
   ((a (asi n aa-arr))
    (aa (asi m aa-arr)))
   (x)
   (list (a-fld a) (a-fld aa))
   x))

(defstobj scal-and-arr
  (saa-sc1 :type a)
  (saa-sc2 :type a)
  (saa-arr :type (array a (4))))

(defstobj aaa (aaa-fld) :congruent-to a)
(defstobj aaaa (aaaa-fld) :congruent-to a)

(defun update-scal-and-arr (n m scal-and-arr)
  (declare (xargs :stobjs scal-and-arr
                  :guard (and (natp n)
                              (natp m)
                              (< n 4)
                              (< m 4)
                              (not (eql n m)))))
  (stobj-let
   ((a (saa-arri n scal-and-arr))
    (aa (saa-sc1 scal-and-arr))
    (aaa (saa-arri m scal-and-arr))
    (aaaa (saa-sc2 scal-and-arr) update-saa-sc2))
   (x aaaa)
   (let ((aaaa (update-a-fld (not (a-fld aaaa)) aaaa)))
     (mv (list (a-fld a) (a-fld aa) (a-fld aaa)) aaaa))
   (mv x scal-and-arr)))

)))
