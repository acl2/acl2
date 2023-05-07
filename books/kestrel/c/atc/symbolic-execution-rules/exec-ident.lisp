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

(include-book "../../language/dynamic-semantics")
(include-book "../read-write-variables")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-ident-rules
  :short "Rules for executing identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a binding hypothesis to read the variable's value,
     and we rewrite @(tsee exec-ident) differently
     based on whether the value is an array or not.")
   (xdoc::p
    "We also introduce a rule that is used in the modular proofs,
     and that follows the definition of @(tsee exec-ident) more closely.
     This will eventually replace the other rule below."))

  (defruled exec-ident-open
    (implies (and (equal val (read-var id compst))
                  (valuep val))
             (equal (exec-ident id compst)
                    (make-expr-value
                     :value val
                     :object (objdesign-of-var id compst))))
    :enable (objdesign-of-var-when-valuep-of-read-var
             exec-ident
             read-object-of-objdesign-of-var-to-read-var))

  (defruled exec-ident-open-via-object
    (implies (and (equal objdes (objdesign-of-var id compst))
                  objdes)
             (equal (exec-ident id compst)
                    (make-expr-value :value (read-object objdes compst)
                                     :object objdes)))
    :enable exec-ident)

  (defval *atc-exec-ident-rules*
    '(exec-ident-open)))
