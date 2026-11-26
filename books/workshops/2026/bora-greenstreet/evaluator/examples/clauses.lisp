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

; This file contains some tests for evaluating if and case clauses

; Erlang If --------------------------------------------------------------------

; if
;   X, Y -> 1;
;   X > 0 -> 2; 
;   false; Y; false -> 3;
;   1 div 0; X == -1 -> 4;
;   true -> 5

; X = true, Y = true
(assert-equal
  (eval-expr-bind-val
    '(:if
      (((cases)
        (guards ((:var X) (:var Y)))
        (body (:integer 1)))
       ((cases)
        (guards ((:binop > (:var X) (:integer 0))))
        (body (:integer 2)))
       ((cases)
        (guards ((:atom false)) ((:var Y)) ((:atom false)))
        (body (:integer 3)))
       ((cases)
        (guards ((:binop div (:integer 1) (:integer 0)))
                ((:binop == (:var X) (:integer -1))))
        (body (:integer 4)))
      ((cases)
       (guards ((:atom true)))
       (body (:integer 5)))))
    '((X :atom true) (Y :atom true)))
  '(:integer 1))

; X = 1, Y = true
(assert-equal
  (eval-expr-bind-val
    '(:if
      (((cases)
        (guards ((:var X) (:var Y)))
        (body (:integer 1)))
       ((cases)
        (guards ((:binop > (:var X) (:integer 0))))
        (body (:integer 2)))
       ((cases)
        (guards ((:atom false)) ((:var Y)) ((:atom false)))
        (body (:integer 3)))
       ((cases)
        (guards ((:binop div (:integer 1) (:integer 0)))
                ((:binop == (:var X) (:integer -1))))
        (body (:integer 4)))
      ((cases)
       (guards ((:atom true)))
       (body (:integer 5)))))
    '((X :integer 1) (Y :atom true)))
  '(:integer 2))

; X = -1, Y = true
(assert-equal
  (eval-expr-bind-val
    '(:if
      (((cases)
        (guards ((:var X) (:var Y)))
        (body (:integer 1)))
       ((cases)
        (guards ((:binop > (:var X) (:integer 0))))
        (body (:integer 2)))
       ((cases)
        (guards ((:atom false)) ((:var Y)) ((:atom false)))
        (body (:integer 3)))
       ((cases)
        (guards ((:binop div (:integer 1) (:integer 0)))
                ((:binop == (:var X) (:integer -1))))
        (body (:integer 4)))
      ((cases)
       (guards ((:atom true)))
       (body (:integer 5)))))
    '((X :integer -1) (Y :atom true)))
  '(:integer 3))

; X = -1, Y = false
(assert-equal
  (eval-expr-bind-val
    '(:if
      (((cases)
        (guards ((:var X) (:var Y)))
        (body (:integer 1)))
       ((cases)
        (guards ((:binop > (:var X) (:integer 0))))
        (body (:integer 2)))
       ((cases)
        (guards ((:atom false)) ((:var Y)) ((:atom false)))
        (body (:integer 3)))
       ((cases)
        (guards ((:binop div (:integer 1) (:integer 0)))
                ((:binop == (:var X) (:integer -1))))
        (body (:integer 4)))
      ((cases)
       (guards ((:atom true)))
       (body (:integer 5)))))
    '((X :integer -1) (Y :atom false)))
  '(:integer 4))

; X = -2, Y = false 
(assert-equal
  (eval-expr-bind-val
    '(:if
      (((cases)
        (guards ((:var X) (:var Y)))
        (body (:integer 1)))
       ((cases)
        (guards ((:binop > (:var X) (:integer 0))))
        (body (:integer 2)))
       ((cases)
        (guards ((:atom false)) ((:var Y)) ((:atom false)))
        (body (:integer 3)))
       ((cases)
        (guards ((:binop div (:integer 1) (:integer 0)))
                ((:binop == (:var X) (:integer -1))))
        (body (:integer 4)))
      ((cases)
       (guards ((:atom true)))
       (body (:integer 5)))))
    '((X :integer -2) (Y :atom false)))
  '(:integer 5))

; Erlang Case ------------------------------------------------------------------

; case X of
;   {0, B} -> err;
;   {A, B} when is_integer(A), A >= 0 -> B div A;
;   {A, B} when is_integer(A) -> B div (-1 * A);
;   {_, B} -> A = 1, B
; end.  

(assert-equal
  (eval-expr-bind-val
    '(:case-of (:var X)
      (((cases (:tuple (:cons (:integer 0) (:cons (:var B) (:nil)))))
        (guards)
        (body (:atom err)))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))
                 (:binop >= (:var A) (:integer 0))))
        (body (:binop div (:var B) (:var A))))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))))
        (body (:binop div (:var B) (:binop * (:integer -1) (:var A)))))
       ((cases (:tuple (:cons (:var _) (:cons (:var B) (:nil)))))
        (guards)
        (body (:match (:var A) (:integer 1)) (:var B)))))
    '((X :tuple ((:integer 0) (:integer 100)))))
  '(:atom err))

(assert-equal
  (eval-expr-bind-val
    '(:case-of (:var X)
      (((cases (:tuple (:cons (:integer 0) (:cons (:var B) (:nil)))))
        (guards)
        (body (:atom err)))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))
                 (:binop >= (:var A) (:integer 0))))
        (body (:binop div (:var B) (:var A))))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))))
        (body (:binop div (:var B) (:binop * (:integer -1) (:var A)))))
       ((cases (:tuple (:cons (:var _) (:cons (:var B) (:nil)))))
        (guards)
        (body (:match (:var A) (:integer 1)) (:var B)))))
    '((X :tuple ((:integer 2) (:integer 100)))))
  '(:integer 50))

(assert-equal
  (eval-expr-bind-val
    '(:case-of (:var X)
      (((cases (:tuple (:cons (:integer 0) (:cons (:var B) (:nil)))))
        (guards)
        (body (:atom err)))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))
                 (:binop >= (:var A) (:integer 0))))
        (body (:binop div (:var B) (:var A))))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))))
        (body (:binop div (:var B) (:binop * (:integer -1) (:var A)))))
       ((cases (:tuple (:cons (:var _) (:cons (:var B) (:nil)))))
        (guards)
        (body (:match (:var A) (:integer 1)) (:var B)))))
    '((X :tuple ((:integer -2) (:integer 100)))))
  '(:integer 50))

(assert-equal
  (eval-expr-bind
    '(:case-of (:var X)
      (((cases (:tuple (:cons (:integer 0) (:cons (:var B) (:nil)))))
        (guards)
        (body (:atom err)))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))
                 (:binop >= (:var A) (:integer 0))))
        (body (:binop div (:var B) (:var A))))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))))
        (body (:binop div (:var B) (:binop * (:integer -1) (:var A)))))
       ((cases (:tuple (:cons (:var _) (:cons (:var B) (:nil)))))
        (guards)
        (body (:match (:var A) (:integer 1)) (:var B)))))
    '((X :tuple ((:atom cow) (:integer 100)))))
  (make-erl-state
    :in '(:integer 100)
    :bind '((A :integer 1) (B :integer 100)
            (X :tuple ((:atom cow) (:integer 100))))))

(assert-equal
  (eval-expr-bind-val
    '(:case-of (:var X)
      (((cases (:tuple (:cons (:integer 0) (:cons (:var B) (:nil)))))
        (guards)
        (body (:atom err)))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))
                 (:binop >= (:var A) (:integer 0))))
        (body (:binop div (:var B) (:var A))))
       ((cases (:tuple (:cons (:var A) (:cons (:var B) (:nil)))))
        (guards ((:call is_integer (:cons (:var A) (:nil)))))
        (body (:binop div (:var B) (:binop * (:integer -1) (:var A)))))
       ((cases (:tuple (:cons (:var _) (:cons (:var B) (:nil)))))
        (guards)
        (body (:match (:var A) (:integer 1)) (:var B)))))
    '((X :atom cow)))
  '(:excpt (:atom error) (:tuple ((:atom case_clause) (:atom cow))) nil))