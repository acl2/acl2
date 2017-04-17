; Utilities for nested stobjs
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

;; As of 04/2017 this only contains stobj-get, which is in the ACL2
;; package, but someday we may want to put more stuff in here and have it in
;; the stobjs package.
(in-package "STOBJS")

(include-book "std/util/bstar" :dir :system)


(defun stobj-get-stobj-return-vars (vars bindings)
  (declare (xargs :mode :program))
  (b* (((when (atom vars)) nil)
       (look (assoc (car vars) bindings))
       ((unless look) (stobj-get-stobj-return-vars (cdr vars) bindings))
       (stobj (car (last (cadr look)))))
    (add-to-set-eq stobj (stobj-get-stobj-return-vars (cdr vars) bindings))))
       



#!acl2
(def-b*-binder stobj-get
  :short "Syntactic sugar for using stobj-let to get some fields from a sub-stobj."
  :long "<p>This b* binder provides a way to code accesses to nested stobjs
within a b* form, as an alternative to @(see stobj-let). Here is an an
example:</p>

@({
 (b* (((stobj-get data-obj child-stobj1) ;; extracted data and updated child stobjs

       ;; bindings for subform :
       ((child-stobj1 (child-field parent-stobj))
        (child-stobj2 (child-arr n parent-stobj)))

       ;; subform:
       (b* ((data (child-stobj2-data child-stobj2))
            (child-stobj1 (update-child-stobj1-data newdata child-stobj1)))
          (mv data child-stobj1))))
   (mv data-obj parent-stobj))
 })

<p>The above extracts @('child-stobj1') and @('child-stobj2') from
@('parent-stobj') and binds them while evaluating the subform, which extracts
a (non-stobj) data object from child-stobj2 and updates a field of child-stobj1
with some new data.  We then return the data object and (implicitly) the
parent-stobj, which must be returned since one of its child stobjs was updated.
More explicitly, this macroexpands (more or less) to the following:</p>

@({
 (b* (((mv data-obj parent-stobj) ;; returned values: data and modified parent stobj
       (stobj-let ((child-stobj1 (child-field parent-stobj))
                   (child-stobj2 (child-arr n parent-stobj))) ;; bindings
                  (data-obj child-stobj1) ;; producer variables
                  ;; subform:
                  (b* ((data (child-stobj2-data child-stobj2))
                       (child-stobj1 (update-child-stobj1-data newdata child-stobj1)))
                    (mv data child-stobj1))
                  ;; returned values:
                  (mv data-obj parent-stobj))))
   (mv data-obj parent-stobj))
 })

<p>The general form of a stobj-get binding is:</p>

@({
  (b* (...
       ((stobj-get VARS)
        BINDINGS
        . SUBFORMS)
       ...)
   ...)
 })

<p>@('BINDINGS') are bindings of stobj names to stobj accessors.  @('SUBFORMS')
are the forms that are evaluated under the bindings, in an implicit progn (so
all but the last are just for side effects).  The @('VARS') correspond to
the values returned by the last subform.</p>

"

  :decls
  ((declare (xargs :guard (and (symbol-listp args)
                               (consp forms)
                               (doublet-listp (car forms))
                               (consp (cdr forms))))))
  :body
  (b* (((cons bindings implicit-progn$) forms)
       (bound-stobjs  (strip-cars bindings))
       (data-return-vars (set-difference-eq args bound-stobjs))
       (stobj-return-vars (stobjs::stobj-get-stobj-return-vars args bindings))
       (return-vars (append stobj-return-vars data-return-vars))
       (return-binder (cond ((atom return-vars) '-)
                            ((atom (cdr return-vars)) (car return-vars))
                            (t `(mv . ,return-vars))))
       (return-val (cond ((atom return-vars) nil)
                         ((atom (cdr return-vars)) (car return-vars))
                         (t `(mv . ,return-vars)))))
  `(b* ((,return-binder
         (stobj-let ,bindings
                    ,args
                    (progn$ . ,implicit-progn$)
                    ,return-val)))
     ,rest-expr)))

#!acl2
(local
 (encapsulate nil
   (local (in-theory (enable nth)))
   ;; copied example from misc/nested-stobj-tests.lisp
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
     (b* (((stobj-get kid1 kid2)
           ((kid1 (kid1-field mom))
            (kid2 (kid2-ar-fieldi index mom)))
           (let* ((val1 (fld1 kid1))
                  (val2 (fld2 kid2))
                  (kid1 (update-fld1 val2 kid1))
                  (kid2 (update-fld2 val1 kid2)))
             (mv kid1 kid2))))
       (update-last-op 'swap mom)))

; Function mom.kid1-fld1 stores a given value in the given mom's kid1-fld1
; field.

   (defun mom.kid1-fld1 (val mom)
     (declare (xargs :stobjs mom))
     (b* (((stobj-get kid1)
           ((kid1 (kid1-field mom)))
           (update-fld1 val kid1)))
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

   (defun check-update-mom (index val1 val2 last-op mom)
     (declare (xargs :stobjs mom
                     :mode :program
                     :guard
                     (or (null index)
                         (and (natp index)
                              (< index (kid2-ar-field-length mom))))))
     (and (equal (last-op mom) last-op)
          (b* (((stobj-get val)
                ((kid1 (kid1-field mom))
                 (kid2 (kid2-ar-fieldi index mom)))
                (and (equal val1 (fld1 kid1))
                     (equal val2 (fld2 kid2)))))
            val)))

   (make-event
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
      (if (and (check-update-mom 0 7 5 'swap mom)
               (check-update-mom 1 7 3 'swap mom))
          (mv nil '(value-triple :ok) state mom)
        (mv "Check-update-mom failed" nil state mom))))

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
     (b* (((stobj-get kid2 kid2a)
           ((kid2 (kid2-ar-fieldi i1 mom))
            (kid2a (kid2-ar-fieldi i2 mom)))
           (let* ((val2 (fld2 kid2))
                  (val2a (fld2 kid2a))
                  (kid2 (update-fld2 val2a kid2))
                  (kid2a (update-fld2 val2 kid2a)))
             (mv kid2 kid2a))))
       mom))

; And finally, here is a checker much like our preceding local-test.  But this
; time we don't want to bother with the effort of verifying guards.  One way to
; avoid that effort is to put the checker in :program mode, and that's what we
; do.

   (defun check-update-mom-2 (i j val-i val-j mom)
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
      val))

   (make-event
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
      (if (check-update-mom-2 0 1 30 10 mom)
          (mv nil `(value-triple :ok) state mom)
        (mv "Error in check-update-mom-2" nil state mom))))))
