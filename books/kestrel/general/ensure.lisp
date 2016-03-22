; Ensuring that Conditions Hold
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides macros to ensure that conditions hold,
; stopping execution with an error message if the conditions do not hold.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ensure

  :parents (kestrel-general-utilities programming)

  :short
  "A macro to ensure that a condition holds,
  stopping with an error message if the condition does not hold."

  :long
  "<p>
  The macro takes as input
  the condition to check,
  a format string for the error message,
  and zero or more arguments for the format string.
  If the condition holds, @('t') is returned.
  Otherwise, execution stops with an error with the given message,
  using the enclosing @('__function__') as context
  (thus, this macro is best used inside @(tsee define)).
  </p>
  <p>
  This macro may be useful, for instance,
  to validate user inputs as follows inside @(tsee b*):
  </p>
  @({
  (- (ensure (condition1 input1) ...))
  (- (ensure (condition2 input2) ...))
  (- (ensure (condition3 input3) ...))
  ...
  })
  @(def ensure)"

  (defmacro ensure (condition error-message &rest error-message-args)
    (declare (xargs :guard (stringp error-message)))
    `(if ,condition
         t
       (er hard? __function__ ,error-message ,@error-message-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ensure$

  :parents (kestrel-general-utilities programming)

  :short "A variant of @(tsee ensure) with @(see state)."

  :long
  "<p>
  This macro takes as input an @(tsee error-triple) condition.
  If the error component of the triple is non-@('nil'),
  the triple is returned.
  Otherwise, if the value component of the triple is non-@('nil'),
  the error triple @('(value t)') is returned.
  Otherwise, execution stops with an error with the given message,
  using the enclosing @('__function__') as context
  (thus, this macro is best used inside @(tsee define)).
  </p>
  <p>
  Inside @(tsee b*), this macro could be used as follows:
  @({
  ...
  ((er &) (ensure$ condition ...))
  ...
  })
  </p>
  @(def ensure$)"

  (defmacro ensure$ (condition-triple error-message &rest error-message-args)
    (declare (xargs :guard (stringp error-message)))
    `(er-let*
      ((condition ,condition-triple))
      (if condition
          (value t)
        (value (er hard? __function__ ,error-message ,@error-message-args))))))
