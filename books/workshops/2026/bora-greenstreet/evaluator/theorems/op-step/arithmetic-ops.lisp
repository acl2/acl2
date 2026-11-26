; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../core/eval-theorems")

; Arithemtic Operation Theorems ------------------------------------------------

(defrule erl-binop-p-of-arithm-binop-p
  (implies (arithm-binop-p op) (erl-binop-p op)))

(defrule appy-erl-binop-of-arithm-binop
  (implies
    (and (arithm-binop-p op)
         (equal (erl-val-kind left) :integer)
         (equal (erl-val-kind right) :integer))
    (equal (apply-erl-binop op left right)
           (apply-erl-arithm-binop op left right)))
  :enable (apply-erl-binop apply-erl-arithm-binop))

; erl-add
(defrule apply-erl-arithm-binop-of-+
  (implies
    (and
      (equal op '+)
      (equal (erl-val-kind left) :integer)
      (equal (erl-val-kind right) :integer))
    (equal
      (apply-erl-arithm-binop op left right)
      (make-erl-val-integer 
        :val (+ (erl-val-integer->val left)
                (erl-val-integer->val right)))))
  :enable (apply-erl-arithm-binop erl-add))

; erl-sub
(defrule apply-erl-arithm-binop-of--
  (implies
    (and
      (equal op '-)
      (equal (erl-val-kind left) :integer)
      (equal (erl-val-kind right) :integer))
    (equal
      (apply-erl-arithm-binop op left right)
      (make-erl-val-integer 
        :val (- (erl-val-integer->val left)
                (erl-val-integer->val right)))))
  :enable (apply-erl-arithm-binop erl-sub))