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
     based on whether the value is an array or not."))

  (defruled exec-ident-open
    (implies (and (equal val (read-var id compst))
                  (valuep val))
             (equal (exec-ident id compst)
                    (if (value-case val :array)
                        (make-expr-value
                         :value (make-value-pointer
                                 :core (pointer-valid (objdesign-static id))
                                 :reftype (value-array->elemtype val))
                         :object nil)
                      (make-expr-value
                       :value val
                       :object (objdesign-of-var id compst)))))
    :enable exec-ident)

  (defval *atc-exec-ident-rules*
    '(exec-ident-open)))
