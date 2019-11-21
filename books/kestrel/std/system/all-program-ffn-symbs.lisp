; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines all-program-ffn-symbs
  :parents (std/system/term-queries)
  :short "Program-mode functions called by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this function is consistent with
     the name of @('all-ffn-symbs') in the ACL2 source code.")
   (xdoc::@def "all-program-ffn-symbs")
   (xdoc::@def "all-program-ffn-symbs-lst"))

  (define all-program-ffn-symbs ((term pseudo-termp)
                                 (ans symbol-listp)
                                 (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (variablep term)) ans)
         ((when (fquotep term)) ans)
         (fn/lambda (ffn-symb term))
         (ans (if (flambdap fn/lambda)
                  (all-program-ffn-symbs (lambda-body fn/lambda) ans wrld)
                (if (logicp fn/lambda wrld)
                    ans
                  (add-to-set-eq fn/lambda ans)))))
      (all-program-ffn-symbs-lst (fargs term) ans wrld)))

  (define all-program-ffn-symbs-lst ((terms pseudo-term-listp)
                                     (ans symbol-listp)
                                     (wrld plist-worldp))
    :returns (final-ans symbol-listp :hyp :guard)
    (b* (((when (endp terms)) ans)
         (ans (all-program-ffn-symbs (car terms) ans wrld)))
      (all-program-ffn-symbs-lst (cdr terms) ans wrld)))

  :verify-guards nil ; done below
  ///
  (verify-guards all-program-ffn-symbs))
