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
(include-book "ast-theorems")
(include-book "eval-bif")
(include-book "erl-state")

; Erl Guard Count Decreases ----------------------------------------------------

(local (defrule node-count-of-guard-cons->tl
  (implies (equal (node-kind (guard-expr-fix x)) :cons)
           (< (node-count (node-cons->tl (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-cons->hd
  (implies (equal (node-kind (guard-expr-fix x)) :cons)
           (< (node-count (node-cons->hd (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-tuple->lst
  (implies (equal (node-kind (guard-expr-fix x)) :tuple)
           (< (node-count (node-tuple->lst (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-binop->left
  (implies (equal (node-kind (guard-expr-fix x)) :binop)
           (< (node-count (node-binop->left (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-binop->right
  (implies (equal (node-kind (guard-expr-fix x)) :binop)
           (< (node-count (node-binop->right (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-unop
  (implies (equal (node-kind (guard-expr-fix x)) :unop)
           (< (node-count (node-unop->expr (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-call
  (implies (equal (node-kind (guard-expr-fix x)) :call)
           (< (node-count (node-call->args (guard-expr-fix x)))
              (node-count x)))
  :enable guard-expr-fix))

; Guard Expression Evaluation --------------------------------------------------

; Erlang reference manual explains: The set of valid guard expressions is a 
; subset of the set of valid Erlang expressions. The reason for restricting the 
; set of valid expressions is that evaluation of a guard expression must be 
; guaranteed to be free of side effects.
;
; Supported guard expressions:
; - (Bound) Variables
; - Connstants (atoms, integers, lists, tuples)
; - Expressions that construct atoms, integer, lists and tuples
; - Calls to certain BIFs (defined in world.lisp)
; - Term Comparison
; - Arithmetic expressions
; - Boolean expressions
; - Short-circuit operations
;
; Remarks:
; - Currently, all operations included in erl-binop and erl-unop are
;   allowed in guard-expressions, except for send, '!'.
; - Unlike in patterns, arithmetic expressions in guards can cause
;   runtime exceptions.
;
; Guards allowed by Erlang that are not supported currently:
; - Floats, records, maps and binaries
; - Expressions that construct floats, records, maps and binaries
; - Expressions that update a map
; - The record expressions Expr#Name.Field and #Name.Field

; Evaluate the given guard expression.
(define eval-guard-expr ((x guard-expr-p) (s erl-state-p))
  :returns (v erl-val-p)
  :measure (node-count x)
  :verify-guards nil
  (b* ((x (guard-expr-fix x))
       ((erl-state s) (erl-state-fix s)))
    (node-case x
      (:integer (make-erl-val-integer :val x.val))
      (:atom (make-erl-val-atom :val x.val))
      (:string (string=>erl-cons x.val))
      (:nil (make-erl-val-cons :lst nil))
      (:fun (make-erl-val-reject :err "Guard expressions cannot have fun."))
      (:cons (b* (; Evaluate the car and cdr of the list.
                  (hd (eval-guard-expr x.hd s))
                  (tl (eval-guard-expr x.tl s))

                  ; Propagate rejections.
                  ((if (equal (erl-val-kind hd) :reject)) hd)
                  ((if (equal (erl-val-kind tl) :reject)) tl)

                  ; Propagate exceptions
                  ((if (equal (erl-val-kind hd) :excpt)) hd)
                  ((if (equal (erl-val-kind tl) :excpt)) tl)

                  ; Pairs are not supported.
                  ((unless (equal (erl-val-kind tl) :cons))
                    (make-erl-val-reject :err "Eval-Guard: tl of cons must be a list.")))
                (make-erl-val-cons :lst (cons hd (erl-val-cons->lst tl)))))
      (:tuple (b* (; Evaluate the list.
                   (lst (eval-guard-expr x.lst s))

                   ; Propagate rejections.
                   ((if (equal (erl-val-kind lst) :reject)) lst)

                   ; Propagate exceptions.
                   ((if (equal (erl-val-kind lst) :excpt)) lst)

                   ; Tuple must be well-formed.
                   ((if (not (equal (erl-val-kind lst) :cons)))
                    (make-erl-val-reject :err "Eval-Guard: ill-formed tuple.")))
                  (make-erl-val-tuple :lst (erl-val-cons->lst lst))))
      (:var
        ; If the variable is bound, return its value, otherwise reject the AST.
        (if (omap::assoc x.id s.bind)
            (omap::lookup x.id s.bind)
            (make-erl-val-reject :err "unbound variable")))
      (:unop 
        ; Evaluate the operand and apply the unop.
        (apply-erl-unop x.op (eval-guard-expr x.expr s)))
      (:binop
        ; Evaluate the operands and apply the binop.
        (b* ((left (eval-guard-expr x.left s))
             (right (eval-guard-expr x.right s)))
            (apply-erl-binop x.op left right)))
      (:match (make-erl-val-reject :err "Guard expressions cannot have match."))
      (:if (make-erl-val-reject :err "Guard expressions cannot have if clauses."))
      (:case-of (make-erl-val-reject :err "Guard expressions cannot have case clauses."))
      (:try (make-erl-val-reject :err "Guard expressions cannot have try."))
      (:remote-call (make-erl-val-reject :err "Guard expressions can only have calls to BIFs."))
      (:call
        (b* (; Evaluate the argument guard expresions.
             (args-res (eval-guard-expr x.args s))
             ((unless (equal (erl-val-kind args-res) :cons))
              (make-erl-val-reject :err "eval-guard-expr: Ill-formed function arguments."))

             ; construct the function call
             (fn (make-fn :name x.fn :arity (len (erl-val-cons->lst args-res))))
              
             ; if the function call is not a BIF, it is not allowed in a guard.
             ((unless (erl-bif-p fn)) 
              (make-erl-val-reject :err "Guard expressions can only have calls to BIFs.")))
            (eval-bif fn (erl-val-cons->lst args-res) s)))
      (:fun-call (make-erl-val-reject :err "Guard expressions can only have calls to BIFs."))
      (:receive (make-erl-val-reject :err "Guard expressions cannot have receive expressions."))))
  ///
    (verify-guards eval-guard-expr)
    (defcong guard-expr-equiv equal (eval-guard-expr x s) 1)
    (defcong erl-state-equiv equal (eval-guard-expr x s) 2))

; Guard Sequence Evaluation ----------------------------------------------------

; Erlang reference manual explains:
; - A guard sequence is true if at least one of the guards is true. 
;   (The remaining guards, if any, are not evaluated.)
; - A guard is a sequence of guard expressions. The guard is true if all guard 
;   expressions evaluate to true.
;
; Remark: Exceptions raised by guards are equivalent to the guard evaluating to
; false, and will not alter the control flow.

; Return '(:atom true) if every guard expression in the sequence evaluates 
; to '(:atom true). If there are rejections, return the first rejection 
; encounetered. If any guard expressions evaluates to a different value,
; return that value.
(define eval-guard ((x guard-expr-list-p) (s erl-state-p))
  :returns (result erl-val-p)
  :measure (len (guard-expr-list-fix x))
  (b* ((x (guard-expr-list-fix x))
       (s (erl-state-fix s))

       ; If there are no guard expressions left, the guard succeeds. 
       ((if (null x)) (make-erl-val-atom :val 'true))

       ; Evaluate the car and cdr of the guard expressions.
       (hd (eval-guard-expr (car x) s))
       (tl (eval-guard (cdr x) s))

       ; Propagate rejections.
       ((if (equal (erl-val-kind hd) :reject)) hd)
       ((if (equal (erl-val-kind tl) :reject)) tl)
       
       ; If any guard expression is not true, the entire guard fails.
       ((unless (and (equal (erl-val-kind hd) :atom) 
                     (equal (erl-val-atom->val hd) 'true)))
        hd))
      tl)
  ///
    (defcong guard-expr-list-equiv equal (eval-guard x s) 1)
    (defcong erl-state-equiv equal (eval-guard x s) 2))

; Return '(:atom true) if there exists a guard in the sequence 
; that evaluates to '(:atom true). If any guard evaluates to a 
; rejection return that rejection. Otherwise, return '(:atom false).
(define eval-guard-seq-when-consp ((x guard-expr-lists-p) (s erl-state-p))
  :returns (result erl-val-p)
  :measure (len (guard-expr-lists-fix x))
  (b* ((x (guard-expr-lists-fix x))
       (s (erl-state-fix s))
       
       ; If no guard evaluated to true, the guard sequence fails.
       ((if (null x)) (make-erl-val-atom :val 'false))

       ; Evaluate the car and cdr of the guard sequence.
       (hd (eval-guard (car x) s))
       (tl (eval-guard-seq-when-consp (cdr x) s))

       ; Propagate rejections.
       ((if (equal (erl-val-kind hd) :reject)) hd)
       ((if (equal (erl-val-kind tl) :reject)) tl)
       
       ; If any guard succeeds, the guard sequence succeeds.
       ((if (and (equal (erl-val-kind hd) :atom) 
                 (equal (erl-val-atom->val hd) 'true)))
        hd))
      tl)
  ///
    (defcong guard-expr-lists-equiv equal (eval-guard-seq-when-consp x s) 1)
    (defcong erl-state-equiv equal (eval-guard-seq-when-consp x s) 2))

; If x is nil, return '(:atom true), otherwise evaluate the guard sequence.
(define eval-guard-seq ((x guard-expr-lists-p) (s erl-state-p))
  :returns (result erl-val-p)
  (b* ((x (guard-expr-lists-fix x))
       (s (erl-state-fix s))
       ((if (null x)) (make-erl-val-atom :val 'true)))
      (eval-guard-seq-when-consp x s))
  ///
    (defcong guard-expr-lists-equiv equal (eval-guard-seq x s) 1)
    (defcong erl-state-equiv equal (eval-guard-seq x s) 2))