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
(include-book "../../language/pure-expression-execution")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-call-rules
  :short "Rules for executing function call expressions."

  (defruled exec-expr-when-call-value-open
    (implies (and (integerp limit)
                  (>= limit (1+ (expr-list-pure-limit (expr-call->args expr))))
                  (equal (expr-kind expr) :call)
                  (expr-list-purep (expr-call->args expr))
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
    :expand (exec-expr expr compst fenv limit)
    :enable (exec-expr-list-to-exec-expr-pure-list-when-expr-pure-list-limit
             nfix))

  (defruled exec-expr-when-call-novalue-open
    (implies (and (integerp limit)
                  (>= limit (1+ (expr-list-pure-limit (expr-call->args expr))))
                  (equal (expr-kind expr) :call)
                  (expr-list-purep (expr-call->args expr))
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
    :expand (exec-expr expr compst fenv limit)
    :enable (exec-expr-list-to-exec-expr-pure-list-when-expr-pure-list-limit
             nfix))

  (defval *atc-exec-expr-when-call-rules*
    '(exec-expr-when-call-value-open
      exec-expr-when-call-novalue-open
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args)
      (:e expr-list-purep)
      (:e expr-list-pure-limit))))
