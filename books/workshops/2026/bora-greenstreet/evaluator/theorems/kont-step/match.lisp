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

; Match Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a match
; expression is equivalent to evaluating the rhs, and then pattern matching it
; to the lhs.

; expr-match
(defrule eval-k-of-expr-match->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-expr
                      :expr (node-match->rhs
                              (kont-expr->expr (erl-k->kont k)))))
           (make-erl-k
             :fuel (1- (erl-k->fuel k))
             :kont (make-kont-match
                     :lhs (node-match->lhs
                           (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-match->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; kont-match
(defrule eval-k-of-match->klst
  (implies 
    (equal (kont-kind (erl-k->kont k)) :match)
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-match->s
  (implies 
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :match))
    (equal 
      (erl-s-klst->s (eval-k k s)) 
      (cond
        ((and (equal (erl-val-kind
                       (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
              (equal (erl-val-kind
                       (erl-val-excpt->err-reason
                         (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) :atom)
              (equal (erl-val-atom->val
                       (erl-val-excpt->err-reason
                         (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) 'badmatch))
         (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst
                            (list (make-erl-val-atom :val 'badmatch) (erl-state->in s))))))
        (t (eval-match (kont-match->lhs (erl-k->kont k)) s)))))
  :enable eval-k)

; apply-k  ---------------------------------------------------------------------

(defrule apply-k-of-expr-match
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-match->rhs
                                      (kont-expr->expr (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-match
                            :lhs (node-match->lhs
                                   (kont-expr->expr (erl-k->kont k)))))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-expr 
              :expr
                (node-match->rhs (kont-expr->expr (erl-k->kont k))))))))

(defrule apply-k-of-match-succeed
  (implies
    (and
      (wf-state-p s) (> (erl-k->fuel k) 0)
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))
      (equal (kont-kind (erl-k->kont k)) :match)
      (not 
        (and (equal (erl-val-kind
                       (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
              (equal (erl-val-kind
                       (erl-val-excpt->err-reason
                         (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) :atom)
              (equal (erl-val-atom->val
                       (erl-val-excpt->err-reason
                         (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) 'badmatch))))
    (equal (apply-k s (cons k nil))
           (eval-match (kont-match->lhs (erl-k->kont k)) s)))
  :enable apply-k-of-step)

(defrule apply-k-of-match-fail
  (implies
    (and
      (wf-state-p s) (> (erl-k->fuel k) 0)
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))
      (equal (kont-kind (erl-k->kont k)) :match)
      (equal (erl-val-kind
                (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
      (equal (erl-val-kind
                (erl-val-excpt->err-reason
                  (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) :atom)
      (equal (erl-val-atom->val
                (erl-val-excpt->err-reason
                  (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s)))) 'badmatch))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst
                            (list (make-erl-val-atom :val 'badmatch) (erl-state->in s)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-match-excpt
  (implies
    (and
      (> (erl-k->fuel k) 0) (equal (erl-val-kind (erl-state->in s)) :excpt)
      (equal (kont-kind (erl-k->kont k)) :match))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))
