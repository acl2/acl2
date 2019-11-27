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

(defines guard-verified-fnsp
  :parents (std/system/term-queries)
  :short "Check if a term calls only guard-verified functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that if any function
     inside the @(':logic') component of an @(tsee mbe)
     or called via @(tsee ec-call)
     is not guard-verified,
     we return @('nil'),
     even when @('term') could otherwise be fully guard-verified.
     See @(tsee guard-verified-exec-fnsp) for a similar utility
     that ignores the guard verification status of functions
     in the @(':logic') components of @(tsee mbe)s
     or called via @(tsee ec-call).")
   (xdoc::p
    "The name of this function is consistent with
     the name of @('logic-fnsp') in the ACL2 source code.")
   (xdoc::@def "guard-verified-fnsp")
   (xdoc::@def "guard-verified-fnsp-lst"))

  (define guard-verified-fnsp ((term pseudo-termp)
                               (wrld plist-worldp))
    :returns (yes/no booleanp)
    (or (variablep term)
        (fquotep term)
        (and (guard-verified-fnsp-lst (fargs term) wrld)
             (let ((fn (ffn-symb term)))
               (if (symbolp fn)
                   (guard-verified-p fn wrld)
                 (guard-verified-fnsp (lambda-body fn) wrld))))))

  (define guard-verified-fnsp-lst ((terms pseudo-term-listp)
                                   (wrld plist-worldp))
    :returns (yes/no booleanp)
    (or (endp terms)
        (and (guard-verified-fnsp (car terms) wrld)
             (guard-verified-fnsp-lst (cdr terms) wrld)))))
