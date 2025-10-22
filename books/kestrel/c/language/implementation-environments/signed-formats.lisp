; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)

(include-book "../../portcullis")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
     We call these `signed formats', even though [C17] does not use this term."))
  (:sign-magnitude ())
  (:ones-complement ())
  (:twos-complement ())
  :pred signed-formatp)
