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

  (defruled exec-expr-when-call-value-open
    (implies (and (not (zp limit))
                  (equal (expr-kind expr) :call)
                  (equal vals
                         (exec-expr-pure-list (expr-call->args expr) compst))
                  (value-listp vals)
                  (equal val+compst1
                         (exec-fun (expr-call->fun expr)
                                   vals
                                   compst
                                   fenv
                                   (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-expr expr compst fenv limit)
                    (mv (expr-value val nil) compst1)))
    :enable (exec-expr
             expr-purep))

  (defruled exec-expr-when-call-novalue-open
    (implies (and (not (zp limit))
                  (equal (expr-kind expr) :call)
                  (equal vals
                         (exec-expr-pure-list (expr-call->args expr) compst))
                  (value-listp vals)
                  (equal val+compst1
                         (exec-fun (expr-call->fun expr)
                                   vals
                                   compst
                                   fenv
                                   (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (not val))
             (equal (exec-expr expr compst fenv limit)
                    (mv nil compst1)))
    :enable (exec-expr
             expr-purep))

  (defval *atc-exec-expr-when-call-rules*
    '(exec-expr-when-call-value-open
      exec-expr-when-call-novalue-open
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))
