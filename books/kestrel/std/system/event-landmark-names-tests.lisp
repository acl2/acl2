; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "event-landmark-names")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) '(f)))

(must-succeed*
 (defun f (x) x)
 (verify-guards f)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) nil))

(must-succeed*
 (mutual-recursion
  (defun f (term)
    (if (variablep term)
        0
      (if (fquotep term)
          0
        (1+ (f-lst (fargs term))))))
  (defun f-lst (terms)
    (if (endp terms)
        0
      (+ (f (car terms))
         (f-lst (cdr terms))))))
 (assert-equal (event-landmark-names (cddr (nth 0 (w state))))
               '(f f-lst)))
