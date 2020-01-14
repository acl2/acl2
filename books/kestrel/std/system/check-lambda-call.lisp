; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-lambda-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (formals symbol-listp :hyp :guard)
               (body pseudo-termp :hyp :guard)
               (args pseudo-term-listp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of a lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, the first result is @('t') and the other results are
     the formal parameters of the lambda expression,
     the body of the lambda expression, and
     the arguments on which the lambda expression is called.
     Otherwise, all the results are @('nil').")
   (xdoc::p
    "See also @(tsee check-nary-lambda-call)."))
  (b* (((when (variablep term)) (mv nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil))
       (fn (ffn-symb term))
       ((when (symbolp fn)) (mv nil nil nil nil)))
    (mv t (lambda-formals fn) (lambda-body fn) (fargs term)))
  ///

  (defret len-of-check-lambda-calls.formals-is-args
    (equal (len formals)
           (len args))
    :hyp :guard)

  (defret len-of-check-lambda-calls.args-is-formals
    (equal (len args)
           (len formals))
    :hyp :guard)

  (defret true-listp-of-check-lambda-call.formals
    (true-listp formals)
    :hyp :guard
    :rule-classes :type-prescription)

  (defret true-listp-of-check-lambda-call.args
    (true-listp args)
    :hyp :guard
    :rule-classes :type-prescription)

  (in-theory (disable len-of-check-lambda-calls.formals-is-args
                      len-of-check-lambda-calls.args-is-formals))

  (theory-invariant (incompatible
                     (:rewrite len-of-check-lambda-calls.formals-is-args)
                     (:rewrite len-of-check-lambda-calls.args-is-formals)))

  (defret acl2-count-of-check-lambda-call.body
    (implies yes/no
             (< (acl2-count body)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-lambda-call.args
    (implies yes/no
             (< (acl2-count args)
                (acl2-count term)))
    :rule-classes :linear))
