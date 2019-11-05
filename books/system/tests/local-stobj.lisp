; Copyright (C) 2019, ForrestHunt, Inc. and Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; These tests were originally, in essence, in a comment in the #-acl2-loop-only
; definition of macro with-local-stobj in the ACL2 source code.  They were
; modified in October 2019 to be suitable for a book, and this is the result.
; At the time of that conversion only minor editing was done; no deep thought
; was given to the nature of the tests at that time.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

(defstobj foo bar xxx)

(thm (equal (create-foo) '(nil nil))) ; succeeds

(defun up1 (x foo)
  (declare (xargs :stobjs foo))
  (update-bar x foo))

(assert-event (equal (bar foo) nil))

(make-event
 (er-progn (trans-eval-no-warning '(up1 3 foo) 'top state nil) ; <foo>
           (value '(assert-event (equal (bar foo) 3))))
 :check-expansion t)

(must-fail
(defun test (x) ; should fail; must use with-local-stobj explicitly
  (mv-let (a b foo)
          (let ((foo (create-foo)))
            (let ((foo (up1 (1+ x) foo)))
              (mv (bar foo) (xxx foo) foo)))
          (declare (ignore foo))
          (mv a b x)))
)

(defun test1 (x)
  (declare (xargs :guard (acl2-numberp x) :verify-guards nil))
  (with-local-stobj
   foo
   (mv-let (a b foo)
           (let ((foo (up1 (1+ x) foo)))
             (mv (bar foo) (xxx foo) foo))
           (mv a b x))))

(assert-event (equal (mv-list 3 (test1 17)) '(18 nil 17)))

(assert-event (equal (bar foo) 3))

(thm (equal (test1 x) (list (1+ x) nil x))) ; succeeds

(thm (equal (test1 x) (list (1+ x) nil x)) ; succeeds
     :hints (("Goal"
              :in-theory
              (enable
               (:executable-counterpart create-foo)))))

(must-fail
; fails, creating (NOT (CADR (HIDE (CREATE-FOO))))
(thm (equal (test1 x) (list (1+ x) nil x))
     :hints (("Goal"
              :in-theory
              (set-difference-theories
               (enable
                (:executable-counterpart create-foo))
               '(create-foo)))))
)

(verify-guards test1)

(assert-event (equal (mv-list 3 (test1 20)) '(21 nil 20)))

(assert-event (equal (bar foo) 3))

(defun test2 (x)
  (with-local-stobj
   foo
   (mv-let (a foo)
           (let ((foo (up1 (1+ x) foo))) (mv (bar foo) foo))
           (mv a x))))

(assert-event (equal (mv-list 2 (test2 12)) '(13 12)))

(assert-event (equal (bar foo) 3))

(thm (equal (test1 x)
            (mv-let (x y) (test2 x) (mv x nil y))))

; (create-foo) ; should get graceful error

(defun test3 (x)
  (with-local-stobj
   foo
   (mv-let (a foo)
           (let ((foo (up1 (1+ x) foo))) (mv (bar foo) foo))
           a)))

(assert-event (equal (test3 11) 12))

(assert-event (equal (bar foo) 3))

(defun test4 (x foo)
  (declare (xargs :stobjs foo
                  :verify-guards nil))
  (let* ((x+1
         (with-local-stobj
          foo
          (mv-let (a foo)
                  (let ((foo (up1 (1+ x) foo))) (mv (bar foo) foo))
                  a)))
         (foo (up1 92 foo)))
    (mv x+1 foo)))

(make-event
 (mv-let (x foo)
   (test4 19 foo)
   (assert$ (equal x 20)
            (mv nil '(value-triple t) state foo))))

(assert-event (equal (bar foo) 92))

(defun test5 (x foo)
  (declare (xargs :stobjs foo
                  :verify-guards nil))
  (let* ((foo (up1 23 foo))
         (x+1
          (with-local-stobj
           foo
           (mv-let (a foo)
                   (let ((foo (up1 (1+ x) foo))) (mv (bar foo) foo))
                   a))))
    (mv x+1 foo)))

(make-event
 (mv-let (x foo)
   (test5 35 foo)
   (assert$ (equal x 36)
            (mv nil '(value-triple t) state foo))))

(assert-event (equal (bar foo) 23))

(must-fail
 (defun bad-test ()
   (with-local-stobj ; should get macroexpansion error or the equivalent
     foo
     (mv foo 3))))

(defun trans-eval-test1 (x foo state)
  (declare (xargs :stobjs (foo state)
                  :mode :program))
  (mv-let (erp val state)
          (trans-eval '(update-bar (cons 3 (bar foo)) foo) 'top state t)
          (declare (ignore erp val))
          (mv x foo state)))

(must-fail
 (with-local-stobj ; should fail; cannot use with-local-stobj in top level loop
   foo
   (mv-let (x foo state)
     (trans-eval-test1 3 foo state)
     (mv x state)))
 :expected :hard)

(assert-event (equal (bar foo) 23))

(defun test6 (a state)
  (declare (xargs :mode :program :stobjs state))
  (with-local-stobj
   foo
   (mv-let (x foo state)
           (trans-eval-test1 a foo state)
           (mv x state))))

; We now allow trans-eval involving stobjs even when there is a local binding
; of the stobj.  But trans-eval references the global stobj.
(make-event (mv-let (x state)
              (test6 100 state)
              (declare (ignore x))
              (value '(value-triple t))))

; Check that global stobj was updated:
(assert-event (equal (bar foo) '(3 . 23)))

; The following test is new in Oct. 2019, to check that we do allow trans-eval
; under with-local-stobj when the form in question doesn't involve the local
; stobj.

(defstobj foo-cong bar-cong xxx-cong :congruent-to foo)

(defun test7 (a foo state)
  (declare (xargs :mode :program :stobjs (state foo)))
  (with-local-stobj
    foo-cong
    (mv-let (x foo-cong y state foo)
      (let* ((foo-cong (update-bar (cons 3 (bar foo-cong)) foo-cong))
             (y (bar foo-cong)))
        (mv-let (x foo state)
          (trans-eval-test1 a foo state)
          (mv x foo-cong y state foo)))
      (mv x y state foo))))

; The following causes a trans-eval warning, but that's OK.
(make-event
 (mv-let (x y state foo)
   (test7 100 foo state)
   (assert$ (and (equal x 100)
                 (equal y '(3)))
            (mv nil '(value-triple t) state foo))))

; Here is another test added October, 2019.  It doesn't add much when
; certifying this book.  But interactively, one can evaluate the form inside
; the must-fail wrapper to see a guard violation message that mentions
; "<some-stobj>".  First here are a couple of supporting definitions.

(defun test8-aux (a foo foo-cong state)
  (declare (xargs :stobjs (state foo foo-cong)
                  :guard (consp a)))
  (declare (ignore foo foo-cong state))
  (car a))

(defun test8 (foo state)
  (declare (xargs :stobjs (state foo) :verify-guards nil))
  (with-local-stobj
    foo-cong
    (mv-let (a foo-cong)
      (mv (test8-aux '3 foo foo-cong state) foo-cong)
      (mv a state foo))))

(must-fail ; see comments above
 (test8 foo state)
 :expected :hard) ; I'm surprised I need :expected :hard for a guard violation.

; The test just above doesn't invoke stobj-print-symbol.  The following,
; however, does.

(defstub my-stub (* foo foo-cong state) => *)

(defun test9 (foo state)
  (declare (xargs :stobjs (state foo) :verify-guards nil))
  (with-local-stobj
    foo-cong
    (mv-let (a foo-cong)
      (mv (my-stub 3 foo foo-cong state) foo-cong)
      (mv a state foo))))

(must-fail ; see comments above
 (test9 foo state)
 :expected :hard) ; I'm a bit surprised I need :expected :hard here.

; Below are some more test1s, contributed by Rob Sumners.

(defstobj foo2 foo2-fld)
(defstobj bar2 bar2-fld)

(defun test1-wls1 (x)
  (with-local-stobj
    foo2
    (mv-let (result foo2)
      (let ((foo2 (update-foo2-fld 2 foo2)))
        (mv (with-local-stobj
              bar2
              (mv-let (result bar2)
                (let ((bar2 (update-bar2-fld 3 bar2)))
                  (mv x bar2))
                result))
            foo2))
      result)))

(assert-event (equal (test1-wls1 129) 129))

(comp t)

(assert-event (equal (test1-wls1 '(adjka 202)) '(adjka 202)))

(thm (equal (test1-wls1 x) x))

(defun test1-wls2 (x)
  (with-local-stobj
    foo2
    (mv-let (result foo2)
      (let ((foo2 (update-foo2-fld 2 foo2)))
        (mv (with-local-stobj
              foo2
              (mv-let (result foo2)
                (let ((foo2 (update-foo2-fld 3 foo2)))
                  (mv x foo2))
                result))
            foo2))
      result)))

(assert-event (equal (test1-wls2 129) 129))

(comp t)

(assert-event (equal (test1-wls2 '(adjka 202)) '(adjka 202)))

(thm (equal (test1-wls2 x) x))

(defun test-wls3 (x)
  (if (atom x) x
    (with-local-stobj
      foo2
      (mv-let (result foo2)
        (mv (cons (car x)
                  (test-wls3 (cdr x)))
            foo2)
        (let ((x result))
          (if (atom x) x (cons (car x) (cdr x))))))))

(assert-event (equal (test-wls3 129) 129))

(comp t)

(assert-event (equal (test-wls3 '(adjka 202)) '(adjka 202)))

(thm (equal (test-wls3 x) x))

;;; Here are the two examples from :doc trans-eval-and-locally-bound-stobjs,
;;; slightly modified by using the following macro so that they can go into a
;;; book.

(defmacro my-eval (form)
; This little utility lets us evaluate arbitrary forms in a book.
  `(make-event
    (er-progn
     (trans-eval ',form 'top state nil)
     (value '(value-triple t)))))

;;; First, the with-local-stobj example....

(defstobj st fld)

(defun f (x state)
  (declare (xargs :stobjs state :mode :program))
  (with-local-stobj
    st
    (mv-let (state local-fld st)
      (mv-let (erp val state)
        (trans-eval `(update-fld ',x st) 'f state nil)
        (declare (ignore erp val))
        (mv state (fld st) st))
      (mv state local-fld))))

; The following returns (<state> NIL).  Thus, the return value of local-fld
; indicated above, which is the value of the fld of the locally-bound st, is
; nil: trans-eval did not update the locally-bound stobj!
(make-event
 (mv-let (state local-fld)
   (f 3 state)
   (value `(assert-event (equal ',local-fld nil)))))

; On the other hand the global stobj, st, was indeed updated by the call of f
; just above.
(assert-event (equal (fld st) 3))

;;; Here is another such example, this time using nested-stobjs instead of tsee
;;; with-local-stobj.

(defstobj sub1 sub1-fld1)
(defstobj top1 (top1-fld :type sub1))

(defun g (x top1 state)
  (declare (xargs :stobjs (top1 state) :mode :program))
  (stobj-let
   ((sub1 (top1-fld top1))) ; bindings
   (sub1 state)             ; producer variables
   (mv-let (erp val state)  ; producer

; NOTE: The reference to sub1 inside the following trans-eval call is actually
; a reference to the global sub1 from the user-stobj-alist, not to the sub1
; bound by stobj-let above.  Thus, this trans-eval call updates the global
; stobj, sub1, not the locally bound sub1 that is a field of top1.

           (trans-eval `(update-sub1-fld1 ',x sub1) 'g state t)
           (declare (ignore erp val))
           (mv sub1 state))
   (mv top1 state)          ; consumer
  ))

(my-eval (g 7 top1 state))
; The global stobj, sub1, has been updated by the call of g just above.
(assert-event (equal (sub1-fld1 sub1) 7))

(my-eval (g 8 top1 state))
; The global stobj, sub1, has been updated by the call of g just above.
(assert-event (equal (sub1-fld1 sub1) 8))

; Obtain the sub1 field of top1.
(defun get-sub1-of-top1 (top1)
  (declare (xargs :stobjs top1 :mode :program))
  (stobj-let
   ((sub1 (top1-fld top1)))  ; bindings
   (val)                     ; producer variable
   (sub1-fld1 sub1)          ; producer
   val                       ; consumer
  ))

; The calls of g above did not update the locally bound sub1.
; That is, they did not update the sub1 field of top1.
(assert-event (equal (get-sub1-of-top1 top1) nil))
