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

(define check-if-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (test pseudo-termp :hyp :guard)
               (then pseudo-termp :hyp :guard)
               (else pseudo-termp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a call of @(tsee if)."
  :long
  (xdoc::topstring
   "If it is, return its test and branches.
    If it is not, all results are @('nil').")
  (b* (((when (variablep term)) (mv nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil))
       (fn (ffn-symb term))
       ((unless (eq fn 'if)) (mv nil nil nil nil))
       ((unless (= (len (fargs term)) 3))
        (prog2$ (raise "Internal error: ~
                        the IF call ~x0 has arguments ~x1."
                       term (fargs term))
                (mv nil nil nil nil))))
    (mv t (fargn term 1) (fargn term 2) (fargn term 3)))
  ///

  (defret acl2-count-of-check-if-call.test
    (implies yes/no
             (< (acl2-count test) (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-if-call.then
    (implies yes/no
             (< (acl2-count then) (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-check-if-call.else
    (implies yes/no
             (< (acl2-count else) (acl2-count term)))
    :rule-classes :linear))
