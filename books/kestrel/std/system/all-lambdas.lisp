; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-lambda-listp")

(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines all-lambdas
  :parents (std/system/term-queries)
  :short "Lambda expressions in a term."

  (define all-lambdas ((term pseudo-termp) (ans pseudo-lambda-listp))
    :returns (final-ans pseudo-lambda-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn (ffn-symb term))
         (ans (if (flambdap fn)
                  (all-lambdas (lambda-body fn) (add-to-set-equal fn ans))
                ans)))
      (all-lambdas-lst (fargs term) ans)))

  (define all-lambdas-lst ((terms pseudo-term-listp) (ans pseudo-lambda-listp))
    :returns (final-ans pseudo-lambda-listp :hyp :guard)
    (if (endp terms)
        ans
      (all-lambdas-lst (cdr terms)
                       (all-lambdas (car terms) ans))))

  :verify-guards nil ; done below
  ///
  (verify-guards all-lambdas))
