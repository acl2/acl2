; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-lambda-call")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-nary-lambda-call ((term pseudo-termp) (n natp))
  :returns (mv (yes/no booleanp)
               (formals symbol-listp :hyp :guard)
               (body pseudo-termp :hyp :guard)
               (args pseudo-term-listp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of
          an @('n')-ary lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee check-lambda-call)
     but it additionally requires the lambda expression
     to have a specified arity.
     It is accompanied by theorems saying that
     the lengths of the formal and argument lists equal the specified arity.")
   (xdoc::p
    "See also @(tsee check-unary-lambda-call)."))
  (b* (((mv yes/no formals body args) (check-lambda-call term))
       ((unless yes/no) (mv nil nil nil nil))
       ((unless (equal (len formals) n)) (mv nil nil nil nil)))
    (mv t formals body args))
  ///

  (defret true-listp-of-check-nary-lambda-call.formals
    (true-listp formals)
    :hyp :guard
    :rule-classes :type-prescription)

  (defret true-listp-of-check-nary-lambda-call.args
    (true-listp args)
    :hyp :guard
    :rule-classes :type-prescription)

  (defret len-of-check-nary-lambda-call.formals
    (implies yes/no
             (equal (len formals) n))
    :hyp :guard)

  (defret len-of-check-nary-lambda-call.args
    (implies yes/no
             (equal (len args) n))
    :hyp :guard
    :hints (("Goal"
             :in-theory (enable len-of-check-lambda-calls.args-is-formals))))

  (defret acl2-count-of-check-nary-lambda-call.body
    (implies yes/no
             (< (acl2-count body)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-nary-lambda-call.args
    (implies yes/no
             (< (acl2-count args)
                (acl2-count term)))
    :rule-classes :linear))
