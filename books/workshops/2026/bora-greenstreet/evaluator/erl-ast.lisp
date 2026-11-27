; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "std/util/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defsubtype" :dir :system)

; Erlang AST Definitions -------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Term comparison operations
; Remark: =:= is represented as =.= for now.
(fty::defsubtype comp-binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(== /= =< < >= > =.= =/=)))))
  :fix-value '==)

; Arithmetic binary operations
(fty::defsubtype arithm-binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(+ - * / div rem band bor bxor bsl bsr)))))
  :fix-value '+)

; Arithmetic unary operations
(fty::defsubtype arithm-unop
  :supertype symbolp
  :restriction 
    (lambda (x)
      (not (null (member x '(+ -)))))
  :fix-value '+)

; Binary boolean operations
(fty::defsubtype bool-binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(and or xor)))))
  :fix-value 'and)

; Unary boolean operations
(fty::defsubtype bool-unop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(not)))))
  :fix-value 'not)

; Short-circuit operations
(fty::defsubtype short-circ-op
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(orelse andalso)))))
  :fix-value 'andalso)

; List operations
(fty::defsubtype list-op
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(++ --)))))
  :fix-value '++)

; Erlang binary operators
(fty::defsubtype erl-binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (or (comp-binop-p x)
          (arithm-binop-p x)
          (bool-binop-p x)
          (short-circ-op-p x)
          (list-op-p x)
          (equal x '!)))
  :fix-value '+)

; Erlang unary operators
(fty::defsubtype erl-unop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (or (arithm-unop-p x)
          (bool-unop-p x)))
  :fix-value '+)

; Node represents an Erlang AST without the restrictions of patterns and guards.
(fty::deftypes node
  (fty::deftagsum node
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:fun ((cls node-clause-list-p)))
    (:cons ((hd node-p)
            (tl node-p)))
    (:tuple ((lst node-p)))
    ; TODO: symbols are not a good representations of Erlang variables.
    (:var ((id symbolp)))
    (:unop ((op erl-unop-p) (expr node-p)))
    (:binop ((op erl-binop-p)
		         (left node-p)
             (right node-p)))
    (:match ((lhs node-p) (rhs node-p)))
    (:if ((clauses node-clause-list)))
    (:case-of ((expr node-p) (clauses node-clause-list)))
    (:try ((exprs node-list-p) (err-clauses node-clause-list)))
    (:remote-call ((module symbolp) (fn symbolp) (args node-p)))
    (:fun-call ((fun node-p) (args node-p)))
    (:call ((fn symbolp) (args node-p)))
    (:receive ((cls node-clause-list-p)))
    :measure (list (acl2-count x) 3))

  (fty::deflist node-list
    :elt-type node-p
    :true-listp t
    :measure (list (acl2-count x) 1))
  
  (fty::deflist node-lists
    :elt-type node-list
    :true-listp t
    :measure (list (acl2-count x) 0))
  
  (fty::defprod node-clause
    ((cases node-list-p :default nil)
     (guards node-lists-p :default nil)
     (body node-list-p :default nil))
    :measure (list (acl2-count x) 2))

  (fty::deflist node-clause-list
    :elt-type node-clause-p
    :true-listp t
    :measure (list (acl2-count x) 0)))

; Arithmetic Expression --------------------------------------------------------

; Arithmetic expressions are expressions allowed in patterns.
;  1) They contain only numeric and bitwise operations.
;  2) They can be evaluated to a constant during compilation. For the ACL2 evaluator,
;     this means that they can be evaluated in isolation, i.e. without bindings,
;     and will not have any side effects, i.e. no new bindings, messages, etc.. 
(define arithm-expr-p ((x acl2::any-p))
  :returns (ok booleanp)
  :measure (node-count x)
  (and (node-p x)
       (case (node-kind x)
         (:integer t)
         (:atom nil)
         (:string nil)
         (:nil nil)
         (:fun nil)
         (:cons nil)
         (:tuple nil)
         (:var nil)
         (:unop (and (arithm-unop-p (node-unop->op x))
                     (arithm-expr-p (node-unop->expr x))))
         (:binop (and (arithm-binop-p (node-binop->op x))
                      (arithm-expr-p (node-binop->left x))
                      (arithm-expr-p (node-binop->right x))))
         (:match nil)
         (:if nil)
         (:case-of nil)
         (:try nil)
         (:remote-call nil)
         (:call nil)
         (:fun-call nil)
         (:receive nil))))

; Erlang Pattern ---------------------------------------------------------------

; A pattern has the same structure as a term but can contain unbound variables.
; - The match operator is allowed if both operands are valid patterns.
; - Arithmetic expressions are allowed.
; - List concatenation is allowed, but not list substraction. However, this is
;   currently not supported.
(defines pattern
  :flag-local nil
  (define pattern-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag pattern
    (and 
      (node-p x)
      (or (arithm-expr-p x)
          (case (node-kind x)
                (:integer t)
                (:atom t)
                (:string t)
                (:nil t)
                (:fun nil)
                (:cons
                  (and (pattern-p (node-cons->hd x))
                       (pattern-p (node-cons->tl x))))
                (:tuple
                  (and (pattern-p (node-tuple->lst x))
                       (or (equal (node-kind (node-tuple->lst x)) :cons)
                           (equal (node-kind (node-tuple->lst x)) :nil))))
                (:var t)
                (:unop nil)
                (:binop nil)
                (:match (and (pattern-p (node-match->lhs x))
                             (pattern-p (node-match->rhs x))))
                (:if nil)
                (:case-of nil)
                (:try nil)
                (:remote-call nil)
                (:call nil)
                (:fun-call nil)
                (:receive nil)))))
  (define pattern-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    :flag pattern-list
    (if (consp x)
        (and (pattern-p (car x)) (pattern-list-p (cdr x)))
        (null x)))
    
    ///
    (std::deflist pattern-list-p (x)
        (pattern-p x)
        :already-definedp t
        :true-listp t))

; Erlang Guard Expression ------------------------------------------------------

; The Erlang Docs state: The set of valid guard expressions is a subset of the 
; set of valid Erlang expressions. The reason for restricting the set of valid 
; expressions is that evaluation of a guard expression must be guaranteed to be
; free of side effects.
(defines guard-expr
  :flag-local nil
  (define guard-expr-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag guard-expr
    (and (node-p x)
        (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:nil t)
          (:fun nil)
          (:cons
            (and (guard-expr-p (node-cons->hd x))
                 (guard-expr-p (node-cons->tl x))))
          (:tuple (and (guard-expr-p (node-tuple->lst x))
                       (or (equal (node-kind (node-tuple->lst x)) :cons)
                           (equal (node-kind (node-tuple->lst x)) :nil))))
          (:var t)
          (:unop (guard-expr-p (node-unop->expr x)))
          (:binop (and (guard-expr-p (node-binop->left x))
                       (guard-expr-p (node-binop->right x))))
          (:match nil)
          (:if nil)
          (:case-of nil)
          (:try nil)
          (:remote-call nil)
          (:call (and (guard-expr-p (node-call->args x))
                      (or (equal (node-kind (node-call->args x)) :cons)
                          (equal (node-kind (node-call->args x)) :nil))))
          (:fun-call nil)
          (:receive nil))))

  ; List of Erlang Expressions
  (define guard-expr-list-p ((x acl2::any-p))
      :returns (ok booleanp)
      :measure (node-list-count x)
      :flag guard-expr-list
      (if (consp x)
          (and (guard-expr-p (car x)) (guard-expr-list-p (cdr x)))
          (null x)))
  
  ; List of Lists of Erlang Guards
  (define guard-expr-lists-p ((x acl2::any-p))
      :returns (ok booleanp)
      :measure (node-lists-count x)
      :flag guard-expr-lists
      (if (consp x)
          (and (guard-expr-list-p (car x)) (guard-expr-lists-p (cdr x)))
          (null x)))
    
    ///
    (std::deflist guard-expr-list-p (x)
        (guard-expr-p x)
        :already-definedp t
        :true-listp t)
    (std::deflist guard-expr-lists-p (x)
        (guard-expr-list-p x)
        :already-definedp t
        :true-listp t))

; Erlang Expression ------------------------------------------------------------

; All Erlang expression types supported by the evaluator.
(defines expr
  :flag-local nil
  (define expr-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag expr
    (and (node-p x)
        (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:nil t)
          (:fun (erl-clause-list-p (node-fun->cls x)))
          (:cons 
            (and (expr-p (node-cons->hd x))
                 (expr-p (node-cons->tl x))))
          (:tuple (and (expr-p (node-tuple->lst x))
                       (or (equal (node-kind (node-tuple->lst x)) :cons)
                           (equal (node-kind (node-tuple->lst x)) :nil))))
          (:var t)
          (:unop (expr-p (node-unop->expr x)))
          (:binop (and (expr-p (node-binop->left x))
                       (expr-p (node-binop->right x))))
          (:match (and (pattern-p (node-match->lhs x))
                       (expr-p (node-match->rhs x))))
          (:if (erl-clause-list-p (node-if->clauses x)))
          (:case-of 
            (and (expr-p (node-case-of->expr x))
                 (erl-clause-list-p (node-case-of->clauses x))))
          (:try
            (and (expr-list-p (node-try->exprs x))
                 (erl-clause-list-p (node-try->err-clauses x))
                  ))
          (:remote-call
            (and (expr-p (node-remote-call->args x))
                 (or (equal (node-kind (node-remote-call->args x)) :cons)
                     (equal (node-kind (node-remote-call->args x)) :nil))))
          (:call
            (and (expr-p (node-call->args x))
                 (or (equal (node-kind (node-call->args x)) :cons)
                     (equal (node-kind (node-call->args x)) :nil))))
          (:fun-call
            (and (expr-p (node-fun-call->fun x))
                 (expr-p (node-fun-call->args x))
                 (or (equal (node-kind (node-fun-call->args x)) :cons)
                     (equal (node-kind (node-fun-call->args x)) :nil))))
          (:receive (erl-clause-list-p (node-receive->cls x))))))

  ; List of Erlang Expressions
  (define expr-list-p ((x acl2::any-p))
      :returns (ok booleanp)
      :measure (node-list-count x)
      :flag expr-list
      (if (consp x)
          (and (expr-p (car x)) (expr-list-p (cdr x)))
          (null x)))
  
  ; Erlang Clause
  (define erl-clause-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-clause-count x)
    :flag clause
    (and (node-clause-p x) 
         (pattern-list-p (node-clause->cases x))
         (guard-expr-lists-p (node-clause->guards x))
         (expr-list-p (node-clause->body x))))

  ; List of Clauses
  (define erl-clause-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-clause-list-count x)
    :flag clause-list
    (if (consp x)
        (and (erl-clause-p (car x)) (erl-clause-list-p (cdr x)))
        (null x)))
    ///
    (std::deflist expr-list-p (x)
        (expr-p x)
        :already-definedp t
        :true-listp t)
    (std::deflist erl-clause-list-p (x)
        (erl-clause-p x)
        :already-definedp t
        :true-listp t))

; Theorems ---------------------------------------------------------------------

(defthm-expr-flag
  ; Expression list is a subtype of Node list
  (defthm expr-list-is-subtype-of-node-list
    (implies (expr-list-p x) (node-list-p x))
    :flag expr-list)
  ; Expression is a subtype of Node
  (defthm expr-is-subtype-of-node
    (implies (expr-p x) (node-p x))
    :flag expr)
  ; Erl-Clause is a subtype of Node-Clause
  (defthm erl-clause-is-subtype-of-node-clause
    (implies (erl-clause-p x) (node-clause-p x))
    :flag clause)
  ; Erl-Clause-List is a subtype of Node-Clause-List
  (defthm erl-clause-list-is-subtype-of-node-clause-list
    (implies (erl-clause-list-p x) (node-clause-list-p x))
    :flag clause-list)
  :hints (("Goal" :in-theory (enable expr-p erl-clause-p))))

; Arithmetic Expression is a subtype of Expression
(defrule arithm-expr-is-subtype-of-expr
  (implies (arithm-expr-p x) (expr-p x))
  :enable (arithm-expr-p expr-p))

; Arithmetic Expression is a subtype of Pattern
(defrule arithm-expr-is-subtype-of-pattern
  (implies (arithm-expr-p x) (pattern-p x))
  :enable (arithm-expr-p pattern-p))

(defthm-pattern-flag
  ; Pattern list is a subtype of Expression list
  (defthm pattern-list-is-subtype-of-expr-list
    (implies (pattern-list-p x) (expr-list-p x))
    :flag pattern-list)
  ; Pattern is a subtype of Expression
  (defthm pattern-is-subtype-of-expr
    (implies (pattern-p x) (expr-p x))
    :flag pattern)
  :hints (("Goal" :in-theory (enable pattern-p expr-p))))

(defthm-guard-expr-flag
  ; Guard list is a subtype of Expression list
  (defthm guard-expr-list-is-subtype-of-expr-list
    (implies (guard-expr-list-p x) (expr-list-p x))
    :flag guard-expr-list)
  ; List of Guard list is a subtype of Node
  (defthm guard-expr-lists-is-subtype-of-node-lists
    (implies (guard-expr-lists-p x) (node-lists-p x))
    :flag guard-expr-lists)
  ; Guard Expression is a subtype of Expression
  (defthm guard-expr-is-subtype-of-expr
    (implies (guard-expr-p x) (expr-p x))
    :flag guard-expr)
  :hints (("Goal" :in-theory (enable guard-expr-p expr-p))))

(set-well-founded-relation o<)

; Fixing Functions -------------------------------------------------------------

(define arithm-expr-fix ((x arithm-expr-p))
  :inline t
  (mbe :logic (if (arithm-expr-p x) x (make-node-integer :val 0))
       :exec x))

(defrule arithm-expr-fix-produces-arithm-expr
  (arithm-expr-p (arithm-expr-fix x))
  :expand (arithm-expr-fix x))

(defrule arithm-expr-fix-is-the-identity-on-arithm-expr
  (implies (arithm-expr-p x)
           (equal (arithm-expr-fix x) x))
  :expand (arithm-expr-fix x))

(define pattern-fix ((x pattern-p))
  :inline t
  (mbe :logic (if (pattern-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule pattern-fix-produces-pattern
  (pattern-p (pattern-fix x))
  :expand (pattern-fix x))

(defrule pattern-fix-is-the-identity-on-pattern
  (implies (pattern-p x)
           (equal (pattern-fix x) x))
  :expand (pattern-fix x))

(define guard-expr-fix ((x guard-expr-p))
  :inline t
  (mbe :logic (if (guard-expr-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule guard-expr-fix-produces-guard-expr
  (guard-expr-p (guard-expr-fix x))
  :expand (guard-expr-fix x))

(defrule guard-expr-fix-is-the-identity-on-guard-expr
  (implies (guard-expr-p x)
           (equal (guard-expr-fix x) x))
  :expand (guard-expr-fix x))

(define expr-fix ((x expr-p))
  :inline t
  (mbe :logic (if (expr-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule expr-fix-produces-expr
  (expr-p (expr-fix x))
  :expand (expr-fix x))

(defrule expr-fix-is-the-identity-on-expr
  (implies (expr-p x)
           (equal (expr-fix x) x))
  :expand (expr-fix x))

(define erl-clause-fix ((x erl-clause-p))
  :inline t
  (mbe :logic (if (erl-clause-p x) x (make-node-clause))
       :exec x))

(defrule erl-clause-fix-produces-erl-clause
  (erl-clause-p (erl-clause-fix x))
  :expand (erl-clause-fix x))

(defrule erl-clause-fix-is-the-identity-on-erl-clause
  (implies (erl-clause-p x)
           (equal (erl-clause-fix x) x))
  :expand (erl-clause-fix x))

; FTY Types --------------------------------------------------------------------

; Arithmetic Erlang Expression
(fty::deffixtype arithm-expr
  :pred   arithm-expr-p
  :fix    arithm-expr-fix
  :equiv  arithm-expr-equiv
  :define t
  :forward t)

; Erlang Pattern
(fty::deffixtype pattern
  :pred   pattern-p
  :fix    pattern-fix
  :equiv  pattern-equiv
  :define t
  :forward t)

(fty::deflist pattern-list
  :elt-type pattern-p
  :true-listp t
  :pred pattern-list-p)

; Erlang Guard Expression
(fty::deffixtype guard-expr
  :pred   guard-expr-p
  :fix    guard-expr-fix
  :equiv  guard-expr-equiv
  :define t
  :forward t)

(fty::deflist guard-expr-list
  :elt-type guard-expr-p
  :true-listp t
  :pred guard-expr-list-p)

(fty::deflist guard-expr-lists
  :elt-type guard-expr-list-p
  :true-listp t
  :pred guard-expr-lists-p)

; Erlang Expression
(fty::deffixtype expr
  :pred   expr-p
  :fix    expr-fix
  :equiv  expr-equiv
  :define t
  :forward t)

(fty::deflist expr-list
  :elt-type expr-p
  :true-listp t
  :pred expr-list-p)

(fty::deffixtype erl-clause
  :pred   erl-clause-p
  :fix    erl-clause-fix
  :equiv  erl-clause-equiv
  :define t
  :forward t)

(fty::deflist erl-clause-list
  :elt-type erl-clause-p
  :true-listp t
  :pred erl-clause-list-p)