; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc all-logic-fns
  :parents (system-utilities-non-built-in)
  :short "All @(':')@(tsee logic)-mode functions in a given world."
  :long "
 @({Typical Form:

 (all-logic-fns (w state))

 })

 <p>The form @('(all-logic-fns wrld)') returns a duplicate-free list of all
 @(':')@(tsee logic)-mode functions in the given ACL2 logical @(see world),
 @('wrld').  Although any logical world is a legal input, performance is
 generally fastest if the input is the current ACL2 world or a small extension
 of it.  For example, immediately after starting ACL2 we have measured the time
 to execute @('(length (all-logic-fns (w state)))') as 0.01 seconds, and then
 execution of @('(length (all-logic-fns (cdr (w state))))') has taken over 3
 seconds.</p>")

(defxdoc all-program-fns
  :parents (system-utilities-non-built-in)
  :short "All @(':')@(tsee program)-mode functions in a given world."
  :long "
 @({Typical Form:

 (all-program-fns (w state))

 })

 <p>The form @('(all-program-fns wrld)') returns a duplicate-free list of all
 @(':')@(tsee program)-mode functions in the given ACL2 logical @(see world),
 @('wrld').  Although any logical world is a legal input, performance is
 generally fastest if the input is the current ACL2 world or a small extension
 of it.  For example, immediately after starting ACL2 we have measured the time
 to execute @('(length (all-program-fns (w state)))') as 0.01 seconds, and then
 execution of @('(length (all-program-fns (cdr (w state))))') has taken over 3
 seconds.</p>")

(defun all-mode-fns-1 (wrld-tail wrld logicp acc)

; Wrld-tail is a tail of wrld, which for decent performance (of the getpropc
; call below) should be an installed world or a modest extension thereof.

  (declare (xargs :guard (and (plist-worldp wrld-tail)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (cond
   ((endp wrld-tail) (remove-duplicates-eq acc))
   (t (all-mode-fns-1
       (cdr wrld-tail)
       wrld
       logicp
       (let ((trip (car wrld-tail)))
         (cond
          ((and (eq (cadr trip) 'formals)
; The following should ensure that the function's definition wasn't erased.
                (iff logicp
                     (member-eq (getpropc (car trip) 'symbol-class nil wrld)
                                '(:ideal :common-lisp-compliant))))
           (cons (car trip) acc))
          (t acc)))))))

(defun all-logic-fns (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (all-mode-fns-1 wrld wrld t nil))

(defun all-program-fns (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (all-mode-fns-1 wrld wrld nil nil))
