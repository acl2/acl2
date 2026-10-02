; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dialects")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signed-formats
  :parents (implementation-environments)
  :short "Formats of signed integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize the possible ways in which
     negative integers are encoded with respect to non-negative integers,
     i.e. two's complement, or ones' complement, or sign and magnitude.
     Although [C23] only supports two's complement,
     the other two are still relevant to support older versions of C."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum signed-format
  :short "Fixtype of signed formats."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.2.6.2/2] lists three possible ways in which a sign bit equal to 1
     modifies the value of the integer value whose sign bit is 0.
     We call these `signed formats', even though [C17] does not use this term.")
   (xdoc::p
    "This fixtype includes all three choices to support C17.
     The choices allowed by a particular standard
     are checked by @(tsee signed-format-wfp),
     which restricts C23 to two's complement."))
  (:sign-magnitude ())
  (:ones-complement ())
  (:twos-complement ())
  :pred signed-formatp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-format-wfp ((format signed-formatp)
                           (std standardp))
  :returns (yes/no booleanp)
  :short "Check if a signed format is well-formed for a C standard."
  :long
  (xdoc::topstring
   (xdoc::p
    "C17 allows all three signed formats [C17:6.2.6.2/2],
     while C23 only allows two's complement [C23:6.2.6.2]."))
  (standard-case std
                 :c17 t
                 :c23 (signed-format-case format :twos-complement))

  ///

  (defrule signed-format-wfp-of-standard-c17
    (signed-format-wfp format (standard-c17)))

  (defrule signed-format-wfp-of-signed-format-twos-complement
    (signed-format-wfp (signed-format-twos-complement) std)))
