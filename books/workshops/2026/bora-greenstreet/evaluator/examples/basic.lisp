; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "util")

; This file contains some basic tests for the evaluator and the Erlang AST.
; Including,
; - Erlang Terms
; - Unop/Binops
; - Variables
; - Match Statements

; Terms ------------------------------------------------------------------------

; term constructors
(assert-equal (make-node-integer :val 1) '(:integer 1))
(assert-equal (make-node-string :val "abc") '(:string "abc"))
(assert-equal (make-node-atom :val 'atom) '(:atom atom))
(assert-equal (make-node-nil) '(:nil))

; list constructor
(assert-equal 
  (make-node-cons :hd (make-node-integer :val 1) 
                  :tl (make-node-cons :hd (make-node-integer :val 2)
                                      :tl (make-node-cons :hd (make-node-integer :val 3)
                                                          :tl (make-node-nil))))
  '(:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))

(assert-equal 
  (make-node-cons :hd (make-node-integer :val 1) 
                  :tl (make-node-integer :val 2))
  '(:cons (:integer 1) (:integer 2)))

; tuple constructor
(assert-equal
  (make-node-tuple :lst '(:cons (:integer 1) (:cons (:atom a) (:cons (:cons (:integer 1) (:cons (:integer 2) (:nil))) (:nil)))))
  '(:tuple (:cons (:integer 1) (:cons (:atom a) (:cons (:cons (:integer 1) (:cons (:integer 2) (:nil))) (:nil))))))

; integer
(assert-equal (eval-expr-val '(:integer 1)) '(:integer 1))

; string
(assert-equal
  (eval-expr-val '(:string "abc"))
  '(:cons ((:integer 97) (:integer 98) (:integer 99))))

; atom
(assert-equal (eval-expr-val '(:atom abc)) '(:atom abc))

; empty list
(assert-equal (eval-expr-val '(:nil)) '(:cons nil))

; list
(assert-equal
  (eval-expr-val
    '(:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))
  '(:cons ((:integer 1) (:integer 2) (:integer 3))))

; tuple
(assert-equal
  (eval-expr-val
    '(:tuple (:cons (:atom a) (:cons (:atom b) (:nil)))))
  '(:tuple ((:atom a) (:atom b))))

; Unop -------------------------------------------------------------------------

; constructor
(assert-equal
  (make-node-unop :op '- :expr '(:integer 1))
  '(:unop - (:integer 1)))

; unop '-' on integer 
(assert-equal (eval-expr-val '(:unop - (:integer 1))) '(:integer -1))

; unop '-' on non-integer
(assert-equal
  (eval-expr-val '(:unop - (:atom a)))
  '(:excpt (:atom error) (:atom badarith) nil))

; Binop ------------------------------------------------------------------------

; constructor
(assert-equal
  (make-node-binop :op '+ :left '(:integer 2) :right '(:integer 3))
  '(:binop + (:integer 2) (:integer 3)))

; binop '+ on integers
(assert-equal
  (eval-expr-val '(:binop + (:integer 2) (:integer 3)))
  '(:integer 5))

; binop '+ with bad arguments
(assert-equal
  (eval-expr-val '(:binop + (:integer 2) (:atom a)))
  '(:excpt (:atom error) (:atom badarith) nil))

; Variables --------------------------------------------------------------------

; constructor
(assert-equal (make-node-var :id 'X) '(:var X))

; unbound variable (compile error)
(assert-equal (eval-expr-bind-val '(:var X) nil) '(:reject "unbound variable"))

; bound variable
(assert-equal
  (eval-expr-bind-val
    '(:var X) (omap::from-lists (list 'X) (list '(:integer 3))))
  '(:integer 3))

(assert-equal
  (eval-expr-bind-val
    '(:binop + (:var X) (:var Y))
    (omap::from-lists (list 'X 'Y) (list '(:integer 4) '(:integer 5))))
  '(:integer 9))

; Match ------------------------------------------------------------------------

; constructor
(assert-equal
  (make-node-match :lhs '(:var X) :rhs '(:integer 1))
  '(:match (:var X) (:integer 1)))                

; contructor for [X, Y, Z] = [int,int,int].
(assert-equal 
  (make-node-match 
    :lhs '(:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))) 
    :rhs '(:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))
  '(:match (:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))) 
           (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))) 

; Match unbound variable, X = 1.
(assert-equal
  (eval-expr '(:match (:var X) (:integer 1)))
  (make-erl-state :in '(:integer 1) :bind '((X :integer 1))))

; Match list of unbound variables, [X, Y, Z] = [1, 2, 3].
(assert-equal
  (eval-expr
    '(:match
      (:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil))))
      (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil))))))
  (make-erl-state
    :in '(:cons ((:integer 1) (:integer 2) (:integer 3))) 
    :bind '((X :integer 1) (Y :integer 2) (Z :integer 3))))

; Match tuple of unbound variables, {X, Y, Z} = {1, 2, 3}.
(assert-equal
  (eval-expr
    '(:match
      (:tuple (:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))))
      (:tuple (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))))
  (make-erl-state
    :in '(:tuple ((:integer 1) (:integer 2) (:integer 3))) 
    :bind '((X :integer 1) (Y :integer 2) (Z :integer 3))))


; Match with arithemtic expressions, {1 + 2, X} = {3, abc}.
(assert-equal
  (eval-expr
    '(:match
      (:tuple (:cons (:binop + (:integer 1) (:integer 2)) (:cons (:var X) (:nil))))
      (:tuple (:cons (:integer 3) (:cons (:atom abc) (:nil))))))
  (make-erl-state
    :in '(:tuple ((:integer 3) (:atom abc)))
    :bind '((X :atom abc))))

; Complex match, {[1, 2, X], Y = 4} = {Z, 4} = {[1, 2, 3], 4}.
(assert-equal
  (eval-expr
    '(:match 
      (:match
        (:tuple
          (:cons
            (:cons (:integer 1) (:cons (:integer 2) (:cons (:var X) (:nil))))
            (:cons (:match (:var Y) (:integer 4)) (:nil))))
        (:tuple (:cons (:var Z) (:cons (:integer 4) (:nil)))))
      (:tuple
        (:cons
          (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))) 
          (:cons (:integer 4) (:nil))))))
  (make-erl-state
    :in '(:tuple ((:cons ((:integer 1) (:integer 2) (:integer 3))) (:integer 4))) 
    :bind '((X :integer 3) (Y :integer 4) 
            (Z :cons ((:integer 1) (:integer 2) (:integer 3))))))

; Sequence of matches, X = 3, Y = X + 2, Y * X.
(assert-equal
  (eval-exprs
    '((:match (:var X) (:integer 3))
      (:match (:var Y) (:binop + (:var X) (:integer 2)))
      (:binop * (:var Y) (:var X))))
  (make-erl-state
    :in '(:integer 15)
    :bind '((X :integer 3) (Y :integer 5))))

; Math pair, [Hd | Tl] = [1, 2, 3].
(assert-equal
  (eval-expr
    '(:match
      (:cons (:var Hd) (:var Tl))
      (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil))))))
  (make-erl-state
    :in '(:cons ((:integer 1) (:integer 2) (:integer 3)))
    :bind '((Hd :integer 1) (Tl :cons ((:integer 2) (:integer 3))))))
