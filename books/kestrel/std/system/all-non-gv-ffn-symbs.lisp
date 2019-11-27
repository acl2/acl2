; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-p")

(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines all-non-gv-ffn-symbs
  :parents (std/system/term-queries)
  :short "Non-guard-verified functions called by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this function is consistent with
     the name of @('all-ffn-symbs') in the ACL2 source code.")
   (xdoc::p
    "Note that if any function
     inside the @(':logic') component of an @(tsee mbe)
     or called via @(tsee ec-call)
     is not guard-verified,
     we return it.
     See @(tsee all-non-gv-exec-ffn-symbs) for a similar utility
     that does not return such functions.")
   (xdoc::@def "all-non-gv-ffn-symbs")
   (xdoc::@def "all-non-gv-ffn-symbs-lst"))

  (define all-non-gv-ffn-symbs ((term pseudo-termp)
                                (ans symbol-listp)
                                (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn/lambda (ffn-symb term))
         (ans (if (flambdap fn/lambda)
                  (all-non-gv-ffn-symbs (lambda-body fn/lambda) ans wrld)
                (if (guard-verified-p fn/lambda wrld)
                    ans
                  (add-to-set-eq fn/lambda ans)))))
      (all-non-gv-ffn-symbs-lst (fargs term) ans wrld)))

  (define all-non-gv-ffn-symbs-lst ((terms pseudo-term-listp)
                                    (ans symbol-listp)
                                    (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (endp terms)) ans)
         (ans (all-non-gv-ffn-symbs (car terms) ans wrld)))
      (all-non-gv-ffn-symbs-lst (cdr terms) ans wrld)))

  :verify-guards nil ; done below
  ///
  (verify-guards all-non-gv-ffn-symbs))
