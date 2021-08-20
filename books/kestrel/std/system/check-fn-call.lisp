; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fn-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (fn symbolp :hyp :guard)
               (args pseudo-term-listp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of a named function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, the first result is @('t') and the other results are
     the function symbol and the arguments on which the function is called.
     Otherwise, all the results are @('nil')."))
  (b* (((when (variablep term)) (mv nil nil nil))
       ((when (fquotep term)) (mv nil nil nil))
       (fn (ffn-symb term))
       ((when (flambdap fn)) (mv nil nil nil)))
    (mv t fn (fargs term)))
  ///

  (more-returns
   (args true-listp
         :hyp :guard
         :rule-classes :type-prescription))

  (defret check-fn-call-not-quote
    (not (equal fn 'quote)))

  (defret acl2-count-of-check-fn-call
    (implies yes/no
             (< (acl2-count args)
                (acl2-count term)))
    :rule-classes :linear))
