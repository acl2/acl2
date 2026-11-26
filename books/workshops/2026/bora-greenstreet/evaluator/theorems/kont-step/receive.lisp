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

; Receive Kont-Step ------------------------------------------------------------

; The following theorems show that evaluating a continuation for a receive
; returns a value collecting the continuations along the klst.

; expr receive
(defrule eval-k-of-expr-receive->klst
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :receive))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-receive->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :receive))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s
            (make-erl-val-receive
              :klst
                (list
                  (make-erl-k
                    :fuel (erl-k->fuel k)
                    :kont
                      (make-kont-receive
                        :clauses
                          (node-receive->cls
                            (kont-expr->expr (erl-k->kont k))))))))))
  :enable eval-k)

; kont receive
(defrule eval-k-of-receive->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :receive))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond
        ((null
          (mv-nth 1
            (eval-receive s (kont-receive->clauses (erl-k->kont k)))))
          nil)
        (t
          (list
            (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont
                (make-kont-expr
                  :expr
                    (car
                      (mv-nth 1
                        (eval-receive s
                          (kont-receive->clauses (erl-k->kont k)))))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont
                (make-kont-exprs
                  :exprs
                    (cdr
                      (mv-nth 1
                        (eval-receive s
                          (kont-receive->clauses (erl-k->kont k))))))))))))
  :enable eval-k)

(defrule eval-k-of-receive->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :receive))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((null
          (mv-nth 1
            (eval-receive s (kont-receive->clauses (erl-k->kont k)))))
          (mv-nth 0
            (eval-receive s (kont-receive->clauses (erl-k->kont k)))))
        (t
         (update-erl-state->in
          (mv-nth 0
            (eval-receive s (kont-receive->clauses (erl-k->kont k))))
          (make-erl-val-none))))))
  :enable eval-k)


; apply-k ----------------------------------------------------------------------

(defrule apply-k-of-expr-receive
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :receive))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in (erl-state-fix s)
             (make-erl-val-receive
               :klst (list (make-erl-k
                             :fuel (erl-k->fuel k)
                             :kont (make-kont-receive
                                     :clauses (node-receive->cls
                                                (kont-expr->expr (erl-k->kont k))))))))))
  :enable apply-k-of-step)

(defrule apply-k-of-receive-no-match
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :receive)
         (not (mv-nth 1 (eval-receive s (kont-receive->clauses (erl-k->kont k))))))
    (equal (apply-k s (cons k nil))
           (mv-nth 0 (eval-receive s (kont-receive->clauses (erl-k->kont k))))))
  :enable apply-k-of-step)

(defrule apply-k-of-receive-when-match
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :receive)
         (mv-nth 1 (eval-receive s (kont-receive->clauses (erl-k->kont k)))))
    (equal
      (apply-k s (cons k nil))
      (apply-k
        (update-erl-state->in
          (mv-nth 0 (eval-receive s (kont-receive->clauses (erl-k->kont k))))
          (make-erl-val-none))
        (list (make-erl-k
                :fuel (1- (erl-k->fuel k))
                :kont
                  (make-kont-expr
                    :expr
                      (car
                        (mv-nth 1
                          (eval-receive s
                            (kont-receive->clauses (erl-k->kont k)))))))
              (make-erl-k
                :fuel (1- (erl-k->fuel k))
                :kont
                  (make-kont-exprs
                    :exprs
                      (cdr
                        (mv-nth 1
                          (eval-receive s
                            (kont-receive->clauses (erl-k->kont k)))))))))))
  :enable apply-k-of-step)

(defrule apply-k-of-receive-excpt
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :excpt)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :receive))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))

; TODO: I think this was already covered elsewhere
(defrule apply-k-of-receive-val
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :receive)
         (erl-klst-p klst)
         (consp klst))
    (equal (apply-k s klst)
           (update-erl-state->in (erl-state-fix s)
             (make-erl-val-receive
               :klst (append (erl-val-receive->klst (erl-state->in s)) klst)))))
  :expand ((apply-k s klst)))