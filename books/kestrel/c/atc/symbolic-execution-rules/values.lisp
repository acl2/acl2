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

(include-book "../../language/values")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-listp-rules
  :short "Rules for discharging @(tsee value-listp) hypotheses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some symbolic execution rules have hypotheses saying that
     certain terms are lists of values, i.e. satisfy @(tsee value-listp).
     These are discharged by the rules here,
     in conjunction with the rules in @(see atc-valuep-rules)."))

  (defval *atc-value-listp-rules*
    '((:e value-listp)
      value-listp-of-cons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-optionp-rules
  :short "Rules for discharging @(tsee value-optionp) hypotheses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some symbolic execution rules have hypotheses saying that
     certain terms are optional values, i.e. satisfy @(tsee value-optionp).
     These are discharged by the rules here.
     The executable counterpart of @(tsee value-optionp)
     takes care of the @('nil') case.
     The non-@('nil') case is taken care by backchaining to
     the rules in @(see atc-valuep-rules)."))

  (defval *atc-value-optionp-rules*
    '((:e value-optionp)
      value-optionp-when-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-fix-rules
  :short "Rules for simplifying away @(tsee value-fix)."

  (defval *atc-value-fix-rules*
    '(value-fix-when-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-value-result-fix-rules
  :short "Rules for simplifying away @(tsee value-result-fix)."

  (defruled value-result-fix-when-valuep
    (implies (valuep x)
             (equal (value-result-fix x)
                    x)))

  (defval *atc-value-result-fix-rules*
    '(value-result-fix-when-valuep)))
