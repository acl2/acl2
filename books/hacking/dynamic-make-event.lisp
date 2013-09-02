(in-package "ACL2")

#|

dynamic-make-event.lisp
-----------------------

By Peter Dillinger, ca. 2006-2009

If you modify the code for an event (such as defun) to call
DYNAMIC-MAKE-EVENT-FN, then that event can have a make-event expansion,
just as a MAKE-EVENT would, meaning that at include-book time, the
expansion is the only part that is seen.

This functionality used to require a hack, but in latest ACL2 versions,
it does not.

The code here is trivial, but we want this functionality to remain in
ACL2, so it should be in the regression suite.  See
dynamic-make-event-test.lisp

|#

(program)
(set-state-ok t)



; body is the new form to replace this one
; event-form is the original (if available?)
(defun dynamic-make-event-fn (body event-form state)
  (make-event-fn `',body
                 nil
                 nil
                 nil
                 event-form
                 state))


#| used to be needed for events other than MAKE-EVENT to have expansion:
(progn+touchable
 :all
 (redefun+rewrite
  make-event-fn
  (:pat (mv-let (wrappers base)
                %1%
                (cond ((member-eq (car base) %2%)  %stuff%)
                      . %3%))
   :repl (mv-let (wrappers base)
                 %1%
                 (declare (ignorable base))
                 %stuff%)
   :vars (%1% %2% %3% %stuff%)
   :mult 1)))
|#
