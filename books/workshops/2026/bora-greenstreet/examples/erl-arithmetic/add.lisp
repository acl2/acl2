; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../../evaluator/top")

(set-induction-depth-limit 1)

; An Erlang World with the following function defined locally:
;
; add(X, Y) when is_integer(X), is_integer(Y) -> X + Y.
;
; We make no claim about the rest of the world, i.e. there could be other
; modules and functions.
(define add-world-p ((w world-p))
  :enabled t
  (b* (((unless (omap::assoc 'local w)) nil)
       (defns (module->fn-defns (omap::lookup 'local w)))
       (fn '((name . add) (arity . 2)))
       ((unless (omap::assoc fn defns)) nil))
      (equal
        (omap::lookup fn defns)
        '(((cases (:var X) (:var Y))
           (guards ((:call is_integer (:cons (:var X) (:nil))) 
                    (:call is_integer (:cons (:var Y) (:nil)))))
           (body (:binop + (:var X) (:var Y))))))))

; Show that calling [add X Y] returns [X + Y].
(defrule apply-k-of-add
  (b* (; The starting state is well-formed
       ((unless (wf-state-p s)) t)
       ((if (equal (erl-val-kind (erl-state->in s)) :excpt)) t)
       ((erl-state s) s)

       ; The state has the world defined above.
       ((unless (add-world-p s.world)) t)
       ((unless (equal s.module 'local)) t)
       
       ; The next continuation calls add(X, Y).
       ((erl-k k) k)
       ((unless (> (erl-k->fuel k) 5)) t)
       ((unless (equal (kont-kind k.kont) :local-call)) t)
       ((unless (equal (kont-local-call->call (erl-k->kont k)) 'add)) t)

       ; The arguments have evaluated to a list of two integers.
       ((unless (equal (erl-val-kind (erl-state->in s)) :cons)) t)
       (vals (erl-val-cons->lst (erl-state->in s)))
       ((unless
          (and (car vals)
               (cadr vals)
               (not (cddr vals))
               (equal (erl-val-kind (car vals)) :integer)
               (equal (erl-val-kind (cadr vals)) :integer))) t))

    (equal (erl-state->in (apply-k s (cons k nil)))
           (erl-val-integer (+ (erl-val-integer->val (car vals))
                               (erl-val-integer->val (cadr vals))))))
 :use (:instance apply-k-of-local-call-when-match)
 :enable (omap::lookup-of-update eval-local-call eval-clauses
          eval-clauses-when-consp match-args eval-match eval-guard-seq
          eval-guard-seq-when-consp eval-guard eval-guard-expr eval-bif
          apply-k-of-binop-expr1))