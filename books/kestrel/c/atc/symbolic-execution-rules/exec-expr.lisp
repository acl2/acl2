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
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-rules
  :short "Rules for @(tsee exec-expr)."

  (defruled exec-expr-when-pure
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (and (equal (expr-kind e) :binary)
                            (equal (binop-kind (expr-binary->op e)) :asg)))
                  (not (zp limit))
                  (compustatep compst)
                  (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr e compst fenv limit)
                    (mv (expr-value->value eval1)
                        compst)))
    :enable exec-expr)

  (defval *atc-exec-expr-rules*
    '(exec-expr-when-pure
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e binop-kind))))
