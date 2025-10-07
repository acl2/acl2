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

(include-book "../../language/dynamic-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-call-rules
  :short "Rules for executing function call expressions."

  (defruled exec-expr-when-call-open
    (implies (and (not (zp limit))
                  (equal (expr-kind expr) :call)
                  (equal vals
                         (exec-expr-pure-list (expr-call->args expr) compst))
                  (value-listp vals))
             (equal (exec-expr expr compst fenv limit)
                    (exec-fun (expr-call->fun expr)
                              vals
                              compst
                              fenv
                              (1- limit))))
    :enable exec-expr)

  (defval *atc-exec-expr-when-call-rules*
    '(exec-expr-when-call-open
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))
