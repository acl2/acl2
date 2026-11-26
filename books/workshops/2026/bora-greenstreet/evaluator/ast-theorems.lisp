; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-ast")

; AST Theorems -----------------------------------------------------------------

; Sub-nodes of a cons expression are also expressions.
(defrule expr-cons-ensures
  (implies (and (expr-p x) (equal (node-kind x) :cons))
           (and (expr-p (node-cons->hd x))
                (expr-p (node-cons->tl x))))
  :enable expr-p)

; Sub-nodes of a cons pattern are also patterns.
(defrule pattern-cons-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :cons))
           (and (pattern-p (node-cons->hd x))
                (pattern-p (node-cons->tl x))))
  :enable (arithm-expr-p pattern-p))

; Sub-nodes of a cons guard are also guards.
(defrule guard-cons-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :cons))
           (and (guard-expr-p (node-cons->hd x))
                (guard-expr-p (node-cons->tl x))))
  :enable guard-expr-p)

; Sub-nodes of a tuple expression are also expressions.
(defrule expr-tuple-ensures
  (implies (and (expr-p x) (equal (node-kind x) :tuple))
           (and (expr-p (node-tuple->lst x))
                (or (equal (node-kind (node-tuple->lst x)) :cons)
                    (equal (node-kind (node-tuple->lst x)) :nil))))
  :enable expr-p)

; Sub-nodes of a tuple pattern are also patterns.
(defrule pattern-tuple-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :tuple))
           (and (pattern-p (node-tuple->lst x))
                (or (equal (node-kind (node-tuple->lst x)) :cons)
                    (equal (node-kind (node-tuple->lst x)) :nil))))
  :enable (arithm-expr-p pattern-p))

; Sub-nodes of a tuple guard are also guards.
(defrule guard-tuple-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :tuple))
           (and (guard-expr-p (node-tuple->lst x))
                (or (equal (node-kind (node-tuple->lst x)) :cons)
                    (equal (node-kind (node-tuple->lst x)) :nil))))
  :enable guard-expr-p)
  
; Sub-nodes of a binop expression are also expressions.
(defrule expr-binop-ensures
  (implies (and (expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (expr-p (node-binop->left x))
                (expr-p (node-binop->right x))))
  :enable expr-p)

; Sub-node of an unop expression is also an expression.
(defrule expr-unop-ensures
  (implies (and (expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (expr-p (node-unop->expr x))))
  :enable expr-p)

; Sub-nodes of a numeric binop expression are also expressions.
(defrule arirhm-expr-binop-ensures
  (implies (and (arithm-expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (arithm-expr-p (node-binop->left x))
                (arithm-expr-p (node-binop->right x))))
  :enable arithm-expr-p)

; Sub-node of a numeric unop expression is also an expression.
(defrule arithm-expr-unop-ensures
  (implies (and (arithm-expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (arithm-expr-p (node-unop->expr x))))
  :enable arithm-expr-p)

; Sub-nodes of a binop guard are also guards.
(defrule guard-binop-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (guard-expr-p (node-binop->left x))
                (guard-expr-p (node-binop->right x))))
  :enable guard-expr-p)

; Sub-node of an unop guard is also a guard.
(defrule guard-unop-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (guard-expr-p (node-unop->expr x))))
  :enable guard-expr-p)

; Sub-nodes of a match expression are expressions, and lhs is a pattern.
(defrule expr-match-ensures
  (implies (and (expr-p x) (equal (node-kind x) :match))
           (and (expr-p (node-match->rhs x))
                (expr-p (node-match->lhs x))
                (pattern-p (node-match->lhs x))))
  :enable expr-p)

; Sub-nodes of a match pattern are patterns.
(defrule pattern-match-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :match))
           (and (pattern-p (node-match->rhs x))
                (pattern-p (node-match->lhs x))))
  :enable (arithm-expr-p pattern-p))

; Clauses of an if expression are erl-clauses
(defrule expr-if-ensures
  (implies (and (expr-p x) (equal (node-kind x) :if))
           (erl-clause-list-p (node-if->clauses x)))
  :enable expr-p)

; Clauses of a case-of expression are erl-clauses, and its expr is an Expression
(defrule expr-case-of-ensures
  (implies (and (expr-p x) (equal (node-kind x) :case-of))
           (and (expr-p (node-case-of->expr x))
                (erl-clause-list-p (node-case-of->clauses x))))
  :enable expr-p)

; The args of a remote function call are an expression
(defrule expr-remote-call-ensures
  (implies (and (expr-p x) (equal (node-kind x) :remote-call))
           (and (symbolp (node-remote-call->module x))
                (symbolp (node-remote-call->fn x))  
                (expr-p (node-remote-call->args x))
                (or (equal (node-kind (node-remote-call->args x)) :cons)
                    (equal (node-kind (node-remote-call->args x)) :nil))))
  :enable expr-p)

; The args of a function call expression are an expression
(defrule expr-call-ensures
  (implies (and (expr-p x) (equal (node-kind x) :call))
           (and (symbolp (node-call->fn x))  
                (expr-p (node-call->args x))
                (or (equal (node-kind (node-call->args x)) :cons)
                    (equal (node-kind (node-call->args x)) :nil))))
  :enable expr-p)

; The args of a bif call guard are a guard expression
(defrule guard-expr-call-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :call))
           (and (symbolp (node-call->fn x))  
                (guard-expr-p (node-call->args x))
                (or (equal (node-kind (node-call->args x)) :cons)
                    (equal (node-kind (node-call->args x)) :nil))))
  :enable guard-expr-p)

; Clauses consist of pattern, guards, and a list of expressions.
(defrule clause-ensures
  (implies (erl-clause-p x)
           (and (pattern-list-p (node-clause->cases x))
                (guard-expr-lists-p (node-clause->guards x))
                (expr-list-p (node-clause->body x))))
  :enable erl-clause-p)

; If an Expression list is not null, then it must be consp.
(defrule consp-of-expr-list-p
  (implies
    (and x (expr-list-p x))
    (consp x)))

; Clauses of a fun expression are erl-clauses
(defrule expr-fun-ensures
  (implies (and (expr-p x) (equal (node-kind x) :fun))
           (erl-clause-list-p (node-fun->cls x)))
  :enable expr-p)

; Args and call fields of a fun expression are expressions.
(defrule expr-fun-call-ensures
  (implies (and (expr-p x) (equal (node-kind x) :fun-call))
           (and (expr-p (node-fun-call->fun x))
                (expr-p (node-fun-call->args x))
                (or (equal (node-kind (node-fun-call->args x)) :cons)
                    (equal (node-kind (node-fun-call->args x)) :nil))))
  :enable expr-p)

; Clauses of a receive expression are erl-clauses,
(defrule expr-receive-ensures
  (implies (and (expr-p x) (equal (node-kind x) :receive))
           (erl-clause-list-p (node-receive->cls x)))
  :enable expr-p)

; Clauses of a try expression are erl-clauses,
(defrule expr-try-ensures
  (implies
    (and (expr-p x) (equal (node-kind x) :try))
    (and 
      (expr-list-p (node-try->exprs x))
      (erl-clause-list-p (node-try->err-clauses x))))
  :enable expr-p)