; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-limit-rules
  :short "Rules about limits not being 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "These two rules serve to relieve the recurring hypothesis
     that the limit is never 0 during the symbolic execution.
     Initially the limit is a variable, and the first rule applies;
     the hypothesis of this rule is easily discharged by
     the inequality assumption over the initial limit
     in the symbolic execution theorem,
     via ACL2's linear arithmetic.
     The @(tsee syntaxp) hypothesis restricts the application of the rule
     to the case in which the limit is a variable (which is true initially).
     As the symbolic execution proceeds,
     1 gets repeatedly subtracted from the initial limit variable,
     and it appears that ACL2 automatically combines multiple 1s
     into constants larger than 1,
     giving the pattern @('(binary-+ \'<negative-integer> <limit-variable>)').
     This is the pattern in the second rule @('not-zp-of-limit-...'),
     whose hypothesis about the limit variable
     is easily discharged via linear arithmetic."))

  (defruled not-zp-of-limit-variable
    (implies (and (syntaxp (symbolp limit))
                  (integerp limit)
                  (> limit 0))
             (not (zp limit))))

  (defruled not-zp-of-limit-minus-const
    (implies (and (syntaxp (quotep -c))
                  (integerp -c)
                  (< -c 0)
                  (integerp limit)
                  (> limit (- -c)))
             (not (zp (binary-+ -c limit)))))

  (defval *atc-limit-rules*
    '(not-zp-of-limit-variable
      not-zp-of-limit-minus-const)))
