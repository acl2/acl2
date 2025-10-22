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

(defsection atc-exec-expr-when-pure-rules
  :short "Rules for executing pure expressions with @(tsee exec-expr)."

  (defruled exec-expr-when-pure
    (implies (and (syntaxp (quotep e))
                  (expr-purep e)
                  (not (zp limit))
                  (compustatep compst)
                  (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval))
             (equal (exec-expr e compst fenv limit)
                    (mv eval compst)))
    :expand (exec-expr e compst fenv limit)
    :enable (expr-purep
             exec-expr-pure
             binop-purep))

  (defval *atc-exec-expr-when-pure-rules*
    '(exec-expr-when-pure
      (:e expr-purep))))
