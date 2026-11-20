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

; This file contains some tests for evaluating local and remote function calls

; BIFs -------------------------------------------------------------------------

(assert-equal
  (eval-expr-val '(:call is_integer (:cons (:integer 1) (:nil))))
  '(:atom true))

(assert-equal
  (eval-expr-val
    '(:call element
      (:cons
        (:integer 2)
        (:cons
          (:tuple
            (:cons
              (:atom one) (:cons (:atom two) (:cons (:atom three) (:nil)))))
          (:nil)))))
  '(:atom two))

; Example World ---------------------------------------------------------------

; An Erlang world with the following modules:
; 
; -module(arithm1).
; -exports([add/2, sum/1]).
; add(X, Y) -> X + Y.
; '((name . adder) (arity . 2))
;
; sum(0) -> 0;
; sum(X) when is_integer(X), X > 0 -> X + sum(X - 1).
; '((name . sum) (arity . 1))
;
;
; -module(arithm2).
; -imports(arithm1, [add/2]).
; add*([]) -> 0;
; add*([Hd | Tl]) when is_integer(Hd) ->
;   Rest = add*(Tl),
; ;   add(Hd, Rest).
; '((name . add) (arity . 1))
;
(local (define test-world ()
  :returns (w world-p)
  '((arithm1
      (attrs (module . arithm1)
              (export ((name . add) (arity . 2))
                      ((name . sum) (arity . 1)))
              (import))
      (fn-defns
        (((name . add) (arity . 2))
          ((cases (:var X) (:var Y))
          (guards)
          (body (:binop + (:var X) (:var Y)))))
        (((name . sum) (arity . 1))
          ((cases (:integer 0))
          (guards)
          (body (:integer 0)))
          ((cases (:var X))
          (guards ((:call is_integer (:cons (:var X) (:nil))) 
                    (:binop > (:var X) (:integer 0))))
          (body (:binop + 
                  (:var X)
                  (:call sum (:cons (:binop - (:var X) (:integer 1)) (:nil)))))))))
    (arithm2
      (attrs (module . arithm2)
              (export)
              (import (((name . add) (arity . 2)) . arithm1)))
      (fn-defns
        (((name . add*) (arity . 1))
          ((cases (:nil))
          (guards)
          (body (:integer 0)))
          ((cases (:cons (:var Hd) (:var Tl)))
          (guards ((:call is_integer (:cons (:var Hd) (:nil)))))
          (body (:match (:var Rest) (:call add* (:cons (:var Tl) (:nil))))
                (:call add (:cons (:var Hd)
                                  (:cons (:var Rest) (:nil)))))))))
    (local
      (attrs (module . local)
              (export)
              (import))
      (fn-defns)))))

; Simple Local Function --------------------------------------------------------

(assert-equal
  (eval-expr-world-val
    '(:call add (:cons (:integer 2) (:cons (:integer 2) (:nil))))
    'arithm1 (test-world))
  '(:integer 4))

; Simple Remote Function -------------------------------------------------------

(assert-equal
  (eval-expr-world-val
    '(:remote-call arithm1 add (:cons (:integer 2) (:cons (:integer 2) (:nil))))
    'local (test-world))
  '(:integer 4))

(assert-equal
  (eval-expr-world-val
    '(:call add*
      (:cons (:cons (:integer 3) (:cons (:integer 6) (:cons (:integer 9) (:nil)))) (:nil)))
      'arithm2 (test-world))
  '(:integer 18))

; Recursive Local Function -----------------------------------------------------

(assert-equal
  (eval-expr-world-val
    '(:call sum (:cons (:integer 5) (:nil))) 'arithm1 (test-world))
  '(:integer 15))

; Recursive Remote Function ----------------------------------------------------

(assert-equal
  (eval-expr-world-val
    '(:remote-call arithm1 sum (:cons (:integer 5) (:nil))) 'local (test-world))
  '(:integer 15))

; Exceptions -------------------------------------------------------------------

; function_clause (local)
(assert-equal
  (eval-expr-world-val
    '(:call sum (:cons (:integer -5) (:nil))) 'arithm1 (test-world))
  '(:excpt (:atom error) (:atom function_clause) nil))

; function_clause (remote)
(assert-equal
  (eval-expr-world-val
    '(:remote-call arithm1 sum (:cons (:integer -5) (:nil))) 'local (test-world))
  '(:excpt (:atom error) (:atom function_clause) nil))


; undef (remote call to undefined module)
(assert-equal
  (eval-expr-world-val
    '(:remote-call crock sum (:cons (:integer -5) (:nil))) 'arithm1 (test-world))
  '(:excpt (:atom error) (:atom undef) ((:atom crock) (:atom sum) (:integer 1))))


; undef (remote call to undefined function)
(assert-equal
  (eval-expr-world-val
    '(:remote-call arithm2 sum (:cons (:integer -5) (:nil))) 'arithm1 (test-world))
  '(:excpt (:atom error) (:atom undef) ((:atom arithm2) (:atom sum) (:integer 1))))