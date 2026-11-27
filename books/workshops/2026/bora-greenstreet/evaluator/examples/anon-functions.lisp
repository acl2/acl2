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

; Simple Anonymous Function ----------------------------------------------------

(assert-equal
  (eval-exprs-val
    '((:match (:var F) (:fun (((cases (:var X)) (guards) (body (:binop + (:var X) (:integer 1)))))))
      (:fun-call (:var F) (:cons (:integer 1) (:nil)))))
  '(:integer 2))

; Remote Anonymous Function ----------------------------------------------------

; A world with the following module:
;
; -module(funs).
; -exports([fn1/2, makeFun/0]).
;
; fn1(X, Y) -> X > Y.
; 
; makeFun() -> fun(X, Y) -> fn1(X, Y) end.
;
(local (define test-world ()
  :returns (w world-p)
  '((funs
      (attrs
        (module . funs)
        (export ((name . fn1) (arity . 2)) ((name . makeFun) (arity . 0)))
        (import))
      (fn-defns
        (((name . fn1) (arity . 2))
        ((cases (:var X) (:var Y)) (guards) (body (:binop > (:var X) (:var Y)))))
        (((name . makeFun) (arity . 0))
        ((cases) (guards)
         (body
          (:fun (((cases (:var X) (:var Y)) (guards) 
                  (body (:call fn1 (:cons (:var X) (:cons (:var Y) (:nil)))))))))))))
    (local (attrs (module . local) (export) (import)) (fn-defns)))))

(assert-equal
  (eval-exprs-world-val
    '((:match (:var F) (:remote-call funs makeFun (:nil)))
      (:fun-call (:var F) (:cons (:integer 3) (:cons (:integer 1) (:nil)))))
    'local (test-world))
  '(:atom true))