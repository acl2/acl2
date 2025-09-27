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

(defsection atc-exec-expr-call-or-asg-rules
  :short "Rules for @(tsee exec-expr-call-or-asg)."

  (defruled exec-expr-call-or-asg-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit)))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    (exec-expr-call (expr-call->fun e)
                                    (expr-call->args e)
                                    compst
                                    fenv
                                    (1- limit))))
    :enable exec-expr-call-or-asg)

  (defruled exec-expr-call-or-asg-when-asg
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal (binop-kind (expr-binary->op e)) :asg)
                  (not (zp limit)))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    (exec-expr-asg (expr-binary->arg1 e)
                                   (expr-binary->arg2 e)
                                   compst
                                   fenv
                                   (1- limit))))
    :enable exec-expr-call-or-asg)

  (defval *atc-exec-expr-call-or-asg-rules*
    '(exec-expr-call-or-asg-when-call
      exec-expr-call-or-asg-when-asg
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2))))
