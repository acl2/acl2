; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-nary-lambda-call")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-unary-lambda-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (formal symbolp :hyp :guard)
               (body pseudo-termp :hyp :guard)
               (arg pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of a unary lambda expression."
  :long
  (xdoc::topstring-p
   "This is a specialization of @(tsee check-nary-lambda-call)
    that returns a single formal and a single argument
    instead of two singleton lists.")
  (b* (((mv yes/no formals body args) (check-nary-lambda-call term 1))
       ((unless yes/no) (mv nil nil nil nil)))
    (mv t (car formals) body (car args)))
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))
   (local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))))
