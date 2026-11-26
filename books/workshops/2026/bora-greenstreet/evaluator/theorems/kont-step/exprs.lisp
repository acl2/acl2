; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")

; Kont-Step for Consequitve Expressions ----------------------------------------

; eval-k -----------------------------------------------------------------------

(defrule eval-k-exprs->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal (erl-s-klst->s (eval-k k s)) (erl-state-fix s)))
  :enable eval-k)

(defrule eval-k-exprs->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (if (kont-exprs->exprs (erl-k->kont k))
          (list (make-erl-k 
                  :fuel (1- (erl-k->fuel k))
                  :kont
                    (make-kont-expr 
                      :expr (car (kont-exprs->exprs (erl-k->kont k)))))
                (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont
                    (make-kont-exprs
                      :exprs (cdr (kont-exprs->exprs (erl-k->kont k))))))
          nil)))
  :enable eval-k)

; apply-k ----------------------------------------------------------------------

(defrule apply-k-of-exprs
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :exprs)
         (not (equal (erl-val-kind (erl-state->in s)) :receive))
         (consp (kont-exprs->exprs (erl-k->kont k))))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              s
              (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont
                        (make-kont-expr 
                          :expr (car (kont-exprs->exprs (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont
                      (make-kont-exprs
                        :exprs (cdr (kont-exprs->exprs (erl-k->kont k)))))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s)))

(defrule apply-k-of-exprs-nil
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :exprs)
         (not (equal (erl-val-kind (erl-state->in s)) :receive))
         (endp (kont-exprs->exprs (erl-k->kont k))))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable apply-k-of-step
  :cases ((wf-state-p s)))

(defrule apply-k-of-exprs-excpt
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (erl-val-kind (erl-state->in s)) :excpt)
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))