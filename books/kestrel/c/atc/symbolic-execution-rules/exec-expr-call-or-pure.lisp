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

(defsection atc-exec-expr-call-or-pure-rules
  :short "Rules for @(tsee exec-expr-call-or-pure)."

  (defruled exec-expr-call-or-pure-when-pure
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (zp limit))
                  (compustatep compst)
                  (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (mv (expr-value->value eval1)
                        compst)))
    :enable exec-expr-call-or-pure)

  (defruled exec-expr-call-or-pure-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit)))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (exec-expr-call (expr-call->fun e)
                                    (expr-call->args e)
                                    compst
                                    fenv
                                    (1- limit))))
    :enable exec-expr-call-or-pure)

  (defval *atc-exec-expr-call-or-pure-rules*
    '(exec-expr-call-or-pure-when-pure
      exec-expr-call-or-pure-when-call
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))
