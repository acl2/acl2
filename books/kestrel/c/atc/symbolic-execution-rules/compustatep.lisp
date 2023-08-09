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

(include-book "../../language/computation-states")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-compustatep-rules
  :short "Rules about @(tsee compustatep)."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are other rules that involve @(tsee compustatep) elsewhere,
     but we also need the rule here,
     which does not readily fit elsewhere.
     At some point we may improve the organization
     of the symbolic execution rules."))

  (defruled compustatep-of-if*-when-both-compustatep
    (implies (and (compustatep b)
                  (compustatep c))
             (compustatep (if* a b c)))
    :enable if*))
