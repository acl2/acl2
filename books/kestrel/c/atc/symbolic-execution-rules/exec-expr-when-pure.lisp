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
(include-book "../pure-expression-limits")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-pure-rules
  :short "Rules for executing pure expressions with @(tsee exec-expr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We need a (locally defined) induction schema
     that takes into account the recursive structure of @(tsee exec-expr)
     with respect to the expression and the limit.")
   (xdoc::p
    "Attempting to prove the theorem directly by induction fails,
     apparently because of the binding hypothesis for @('eval').
     So we prove by induction a lemma without the binding hypothesis."))

  (local
   (defun induction (expr limit)
     (declare (xargs :measure (expr-count expr)
                     :hints (("Goal" :in-theory (enable o< o-finp)))))
     (declare (irrelevant limit))
     (expr-case expr
                :ident nil
                :const nil
                :call nil
                :unary (induction expr.arg (1- limit))
                :otherwise nil)))

  (defrulel lemma
    (b* ((eval (exec-expr-pure e compst)))
      (implies (and (expr-purep e)
                    (integerp limit)
                    (>= limit (expr-pure-limit e))
                    (compustatep compst)
                    (expr-valuep eval))
               (equal (exec-expr e compst fenv limit)
                      (mv eval compst))))
    :induct (induction e limit)
    :expand ((exec-expr e compst fenv limit)
             (exec-expr-pure e compst))
    :enable (expr-purep
             binop-purep
             expr-pure-limit))

  (defruled exec-expr-when-pure
    (implies (and (syntaxp (quotep e))
                  (expr-purep e)
                  (integerp limit)
                  (>= limit (expr-pure-limit e))
                  (compustatep compst)
                  (equal eval (exec-expr-pure e compst))
                  (expr-valuep eval))
             (equal (exec-expr e compst fenv limit)
                    (mv eval compst))))

  (defval *atc-exec-expr-when-pure-rules*
    '(exec-expr-when-pure
      (:e expr-purep)
      (:e expr-pure-limit))))
