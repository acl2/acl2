; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../let-designations")
(include-book "../conditional-expressions")

(include-book "std/util/defval" :dir :system)

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-wrapper-rules
  :short "Rules about wrappers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We expand wrappers that are identity functions
     and are just used to inform ATC of
     the exact representation of C constructs."))

  (defval *atc-wrapper-rules*
    '(condexpr
      declar
      assign
      star)))
