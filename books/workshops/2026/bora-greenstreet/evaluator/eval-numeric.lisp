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
(include-book "erl-value")
(include-book "erl-op")

(set-induction-depth-limit 1)

; Evaluate Numeric Erlang Expressions ------------------------------------------

(define eval-numeric ((x arithm-expr-p))
  :returns (v erl-val-p)
  :measure (node-count x)
  :verify-guards nil
  :prepwork 
    ((defrule node-binop->left-decreases-count
       (implies (equal (node-kind (arithm-expr-fix x)) :binop)
                (< (node-count (node-binop->left (arithm-expr-fix x)))
                   (node-count x)))
       :enable arithm-expr-fix)
     (defrule node-binop->right-decreases-count
       (implies (equal (node-kind (arithm-expr-fix x)) :binop)
                (< (node-count (node-binop->right (arithm-expr-fix x)))
                   (node-count x)))
       :enable arithm-expr-fix)
     (defrule node-unop->expr-decreases-count
       (implies (equal (node-kind (arithm-expr-fix x)) :unop)
                (< (node-count (node-unop->expr (arithm-expr-fix x)))
                   (node-count x)))
       :enable arithm-expr-fix))

  (b* ((x (arithm-expr-fix x)))
    (node-case x
      (:integer (make-erl-val-integer :val x.val))
      (:string (make-erl-val-reject :err "Numeric expressions cannot have strings."))
      (:atom (make-erl-val-reject :err "Numeric expressions cannot have atoms."))
      (:nil (make-erl-val-reject :err "Numeric expressions cannot have lists."))
      (:fun (make-erl-val-reject :err "Numeric expressions cannot have funs."))
      (:cons (make-erl-val-reject :err "Numeric expressions cannot have lists."))
      (:tuple (make-erl-val-reject :err "Numeric expressions cannot have tuples."))
      (:var (make-erl-val-reject :err "Numeric expressions cannot have variables."))
      (:unop
        (b* ((val (apply-erl-unop (node-unop->op x) (eval-numeric (node-unop->expr x))))
             ((unless (or (equal (erl-val-kind val) :integer) 
                          (equal (erl-val-kind val) :reject))) 
               (make-erl-val-reject :err "Illegal numeric expression.")))
            val))
      (:binop
        (b* ((left (eval-numeric x.left))
              ((unless (or (equal (erl-val-kind left) :integer) 
                           (equal (erl-val-kind left) :reject)))
               (make-erl-val-reject :err "Illegal numeric expression."))
              (right (eval-numeric x.right))
              ((unless (or (equal (erl-val-kind right) :integer) 
                           (equal (erl-val-kind right) :reject))) 
               (make-erl-val-reject :err "Illegal numeric expression."))
              (val (apply-erl-binop x.op left right))
              ((unless (or (equal (erl-val-kind val) :integer) 
                           (equal (erl-val-kind val) :reject))) 
               (make-erl-val-reject :err "Illegal numeric expression.")))
            val))
      (:match (make-erl-val-reject :err "Numeric expressions cannot have match."))
      (:if (make-erl-val-reject :err "Numeric expressions cannot have if clauses."))
      (:case-of (make-erl-val-reject :err "Numeric expressions cannot have case clauses."))
      (:try (make-erl-val-reject :err "Numeric expressions cannot have try-catch."))
      (:remote-call (make-erl-val-reject :err "Numeric expressions cannot have remote calls."))
      (:call (make-erl-val-reject :err "Numeric expressions cannot have local calls."))
      (:fun-call (make-erl-val-reject :err "Numeric expressions cannot have fun calls."))
      (:receive (make-erl-val-reject :err "Numeric expressions cannot have receive expressions."))))

  ///
    (verify-guards eval-numeric)
    
    (defcong arithm-expr-equiv equal (eval-numeric x) 1)

    (more-returns
      (v (or (equal (erl-val-kind v) :integer)   
             (equal (erl-val-kind v) :reject))
        :name val-kind-of-eval-numeric)))