; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

(defstobj st1 fld1)
(defstobj st2 fld2 :congruent-to st1)
(defstobj st3 fld3 :congruent-to st1)
(defun foo (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (swap-stobjs st1 st2))

(defmacro my-eval (form)
; This little utility lets us evaluate arbitrary forms in a book.
  `(make-event
    (er-progn
     (trans-eval ',form 'top state nil)
     (value '(value-triple t)))))

; Here are a bunch of tests of foo, above, hence of swap-stobjs.

(my-eval (update-fld1 3 st1))
(assert-event (equal (fld1 st1) 3))
(my-eval (update-fld2 4 st2))
(assert-event (equal (fld2 st2) 4))
(assert-event (equal (fld1 st1) 3))
(my-eval (foo st1 st2))
(assert-event (equal (fld2 st2) 3))
(assert-event (equal (fld1 st1) 4))
(my-eval (foo st2 st1))
(assert-event (equal (fld2 st2) 4))
(assert-event (equal (fld1 st1) 3))

(must-fail
; Error: Need to return the modified stobjs.
(defun bar (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (mv-let (st1 st2)
    (swap-stobjs st1 st2)
    (mv (fld1 st2) (fld2 st1))))
)

(defun bar (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (mv-let (st1 st2)
    (swap-stobjs st1 st2)
    (mv (fld1 st2) (fld2 st1) st1 st2)))

(my-eval (bar st1 st2)) ; should return (mv 3 4 ...).
(my-eval (bar st1 st2)) ; should return (mv 4 3 ...).
(my-eval (bar st1 st2)) ; should return (mv 3 4 ...).
(assert-event (equal (fld2 st2) 3))
(assert-event (equal (fld1 st1) 4))

; Let's test swapping twice within a function.

(defun swap-twice (x1 x2 st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (let* ((st1 (update-fld1 x1 st1))
         (st2 (update-fld2 x2 st2)))
    (assert$ (and (equal (fld1 st1) x1)
                  (equal (fld2 st2) x2))
             (mv-let (st1 st2)
               (swap-stobjs st1 st2)
               (assert$ (and (equal (fld1 st1) x2)
                             (equal (fld2 st2) x1))
                        (mv-let (st1 st2)
                          (swap-stobjs st1 st2)
                          (assert$ (and (equal (fld1 st1) x1)
                                        (equal (fld2 st2) x2))
                                   (mv st1 st2))))))))

(my-eval (swap-twice 7 8 st1 st2))
(assert-event (equal (fld1 st1) 7))
(assert-event (equal (fld2 st2) 8))

; Let's test swapping three times within a function.

(defun swap-thrice (x1 x2 st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (let* ((st1 (update-fld1 x1 st1))
         (st2 (update-fld2 x2 st2)))
    (assert$ (and (equal (fld1 st1) x1)
                  (equal (fld2 st2) x2))
             (mv-let (st1 st2)
               (swap-stobjs st1 st2)
               (assert$ (and (equal (fld1 st1) x2)
                             (equal (fld2 st2) x1))
                        (mv-let (st1 st2)
                          (swap-stobjs st1 st2)
                          (assert$ (and (equal (fld1 st1) x1)
                                        (equal (fld2 st2) x2))
                                   (mv-let (st1 st2)
                                     (swap-stobjs st1 st2)
                                     (assert$ (and (equal (fld1 st1) x2)
                                                   (equal (fld2 st2) x1))
                                              (mv st1 st2))))))))))

(my-eval (swap-thrice 10 20 st1 st2))
(assert-event (equal (fld1 st1) 20))
(assert-event (equal (fld2 st2) 10))

; Here is a silly little test of swapping a local and a global stobj.  In this
; function we swap the local and global stobj, then compute on the global stobj
; (which was created locally), and then swap back.  Here we swap local st1 and
; global st2, and store a result in st3 to look at below.

(defun swap-local-global (x st2 st3)
  (declare (xargs :stobjs (st2 st3) :mode :program))
  (with-local-stobj
    st1
    (mv-let (val st2 st1)
; -- COMPUTATION PART of the with-local-stobj form:
      (mv-let (st2 st1)
        (swap-stobjs st2 st1)
        (let ((st2
               ;; compute on what used to be local and is now the global stobj
               (update-fld2 (* 2 x) st2)))
          (mv-let (st2 st1)
            (swap-stobjs st2 st1)
            (mv (fld1 st1) st2 st1))))
; -- RESULT PART of the with-local-stobj form:
      (let ((st3 (update-fld3 val st3))) ; store the computed value
        (mv st2 st3)))))

(my-eval (swap-local-global 3 st2 st3))
; Then st1 and st2 aren't changed, and st3 has the expected computed value.
(assert-event (equal (fld1 st1) 20))
(assert-event (equal (fld2 st2) 10))
(assert-event (equal (fld3 st3)  6))

; We can also swap two local stobjs without anything going wrong.  Unlike the
; example above we swap only once, not twice -- so if the swapping "leaked"
; into the global stobjs for st1 and st2, we'd see that.

(defun swap-local-local (x st3)
  (declare (xargs :stobjs (st3) :mode :program))
  (with-local-stobj
    st2
; -- COMPUTATION PART for st2:
    (mv-let (st2 st3)
      (with-local-stobj
        st1
        (mv-let (val st2 st1)
; -- COMPUTATION PART for st1:
          (mv-let (st2 st1)
            (swap-stobjs st2 st1)
            (let ((st2
                   ;; compute on what used to be local and is now the global stobj
                   (update-fld2 (* 2 x) st2)))
              (mv (fld2 st2) st2 st1)))
; -- RESULT PART for st1:
          (let ((st3 (update-fld3 val st3))) ; store the computed value
            (mv st2 st3))))
; -- RESULT PART for st2:
      st3)))

(my-eval (swap-local-global 15 st2 st3))

; Then st1 and st2 aren't changed, and st3 has the expected computed value.
(assert-event (equal (fld1 st1) 20))
(assert-event (equal (fld2 st2) 10))
(assert-event (equal (fld3 st3) 30))

; It can be problematic to call trans-eval under swap-stobjs, as this may
; produce surprising results.  Let's reinitialize our stobjs to values that are
; easy to remember and then look at how trans-eval might not behave as expected.

(my-eval (update-fld1 1 st1))
(my-eval (update-fld2 2 st2))
(my-eval (update-fld3 3 st3))

(defun swap-local-global-trans-eval (state st2 st3)
  (declare (xargs :stobjs (state st2 st3) :mode :program))
  (with-local-stobj
    st1

; So st1 is bound above to the value of (create-st1); hence (fld1 st1) = nil at
; this point.

    (mv-let (stobjs-out/val state st2 st1)

; -- COMPUTATION PART of the with-local-stobj form:

      (mv-let (st2 st1)
        (swap-stobjs st2 st1)

; At this point, the value of lexical variable st1 is the original (global)
; st2, and the value of lexical variable st2 is the local stobj, st1.  So at
; this point, (fld2 st2) = nil.  We do not change st2 below, so this equation
; will hold of the final st2.  Note however that the global st2 -- which is in
; the user-stobj-alist of the state -- won't be updated until exiting from this
; function, because the user-stobj-alist of the state is only updated when
; exiting from an evaluator call on a stobj-producing term.  Thus the value of
; st2 in the user-stobj-alist will be updated only upon exit from
; swap-local-global-trans-eval.

        (mv-let (erp stobjs-out/val state)

; Next we obtain (fld2 st2) through trans-eval.  Since we have swapped st2 and
; st1, maybe we'd expect the value to be from the fld2 taken from the local
; stobj st1 from before we swapped, hence nil.  But in fact, at this point the
; computed value is fld2 from the global st2, which is 2.  Why?  Because
; swap-stobjs doesn't update the state; only evaluator calls update the state.

          (trans-eval '(fld2 st2) 'top state nil)
          (declare (ignore erp))

; As discussed above, the value component of stobjs-out/val is 2.

          (mv stobjs-out/val state st2 st1)))

; -- RESULT PART of the with-local-stobj form:

      (let ((st3

; Store the computed value of 2 in st3, to look up later.

             (update-fld3 (cdr stobjs-out/val) st3)))
        (mv stobjs-out/val state st2 st3)))))

(my-eval (swap-local-global-trans-eval state st2 st3))
; The global value of st1 hasn't changed:
(assert-event (equal (fld1 st1) 1))
; But because of the swap of local and global described above:
(assert-event (equal (fld2 st2) nil))
; The value produced by trans-eval is the fld2 of the original global st2,
; which is 2:
(assert-event (equal (fld3 st3) 2))

; We conclude with some tests involving swap-stobjs and stobj-let.  To make
; things a bit interesting, we'll delay termination and guard verification for
; the function init-parent below and make sure that it works in each case.

(defstobj parent
  (st1-field :type st1)
  (st2-field :type st2)
  (st3-field :type st3))

(defun fldi-parent (i parent)
  (declare (xargs :stobjs (parent)))
  (stobj-let
; bindings
   ((st1 (st1-field parent))
    (st2 (st2-field parent))
    (st3 (st3-field parent)))
; producer-variables
   (val)
; producer
   (case i
     (1 (fld1 st1))
     (2 (fld2 st2))
     (3 (fld3 st3))
     (otherwise (er hard? 'fldi-parent
                    "Bad index, ~x0"
                    i)))
; consumer
   val))

(defun init-parent (x1 x2 x3 parent)
  (declare (xargs :stobjs (parent) :mode :program))
  (stobj-let
; bindings
   ((st1 (st1-field parent))
    (st2 (st2-field parent))
    (st3 (st3-field parent)))
; producer-variables
   (st1 st2 st3)
; producer
   (let* ((st1 (update-fld1 x1 st1))
          (st2 (update-fld2 x2 st2))
          (st3 (update-fld3 x3 st3)))
     (mv st1 st2 st3))
; consumer
   parent))

(my-eval (init-parent 'a 'b 'c parent))
(assert-event (equal (fldi-parent 1 parent) 'a))
(assert-event (equal (fldi-parent 2 parent) 'b))
(assert-event (equal (fldi-parent 3 parent) 'c))

(verify-termination init-parent
  (declare (xargs :verify-guards nil)))

(my-eval (init-parent 'd 'e 'f parent))
(assert-event (equal (fldi-parent 1 parent) 'd))
(assert-event (equal (fldi-parent 2 parent) 'e))
(assert-event (equal (fldi-parent 3 parent) 'f))

(verify-guards init-parent)

(my-eval (init-parent 1 2 3 parent))
(assert-event (equal (fldi-parent 1 parent) 1))
(assert-event (equal (fldi-parent 2 parent) 2))
(assert-event (equal (fldi-parent 3 parent) 3))

(defun swap-st1-st2-in-parent (parent)
  (declare (xargs :stobjs (parent)))
  (stobj-let
; bindings
   ((st1 (st1-field parent))
    (st2 (st2-field parent)))
; producer-variables
   (st1 st2)
; producer
   (foo st1 st2)
; consumer
   parent))

(my-eval (swap-st1-st2-in-parent parent))
; Check that the swap actually worked.
(assert-event (equal (fldi-parent 1 parent) 2))
(assert-event (equal (fldi-parent 2 parent) 1))
(assert-event (equal (fldi-parent 3 parent) 3))

(defun swap-st1-in-parent-with-global-st2 (parent st2)
  (declare (xargs :stobjs (parent st2)))
  (stobj-let
; bindings
   ((st1 (st1-field parent)))
; producer-variables
   (st1 st2)
; producer
   (foo st1 st2)
; consumer
   (mv parent st2)))

; Before swapping child st1 with global st2:
(my-eval (init-parent 'a 'b 'c parent))
(assert-event (equal (fldi-parent 1 parent) 'a))
(assert-event (equal (fldi-parent 2 parent) 'b))
(my-eval (update-fld1 1 st1))
(my-eval (update-fld1 2 st2))
(assert-event (equal (fld1 st1) 1))
(assert-event (equal (fld2 st2) 2))
; Now swap child st1 with global st2:
(my-eval (swap-st1-in-parent-with-global-st2 parent st2))
; Check that results are as expected.
(assert-event (equal (fldi-parent 1 parent) 2))
(assert-event (equal (fldi-parent 2 parent) 'b))
(assert-event (equal (fld1 st1) 1))
(assert-event (equal (fld2 st2) 'a))

; Here are some errors.  They won't show up in the log because of must-fail,
; but they were useful without the must-fail wrappers when developing
; swap-stobjs.

(must-fail
(defun bad (st1 st2)
  (declare (xargs :stobjs (st1))) ; forgot to declare st2 as a stobj
  (swap-stobjs st1 st2))
)

(must-fail
(defun bad (st1 st2)
; forgot to declare either stobj
  (swap-stobjs st1 st2))
)

(must-fail
(defun bad (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
; duplicate arguments
  (swap-stobjs st1 st1))
)

(must-fail
(defun bad (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
; non-symbol argument, which thus isn't a stobj name
  (swap-stobjs st1 (let ((st2 st2)) st2)))
)

(defstobj st4 fld4)

(must-fail
(defun bad (st1 st4)
  (declare (xargs :stobjs (st1 st4)))
; not congruent stobjs
  (swap-stobjs st1 st4))
)
