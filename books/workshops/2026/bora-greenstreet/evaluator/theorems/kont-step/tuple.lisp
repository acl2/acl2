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

; Tuple Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a tuple
; expression is equivalent to evaluating every element of the tuple from
; left to right, and then merging the results.

(defrule apply-k-of-expr-tuple
  (implies
    (and (wf-state-p s) (> (erl-k->fuel k) 0)
         (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple))
    (equal (apply-k s (cons k nil))
           (apply-k
             (apply-k s
               (list (make-erl-k
                       :fuel (1- (erl-k->fuel k))
                       :kont (make-kont-expr
                               :expr (node-tuple->lst
                                       (kont-expr->expr (erl-k->kont k)))))))
             (list (make-erl-k :fuel (1- (erl-k->fuel k))
                               :kont (make-kont-tuple))))))
  :enable (apply-k-of-step eval-k)
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k
           :fuel (1- (erl-k->fuel k))
           :kont (make-kont-expr
                   :expr (node-tuple->lst (kont-expr->expr (erl-k->kont k))))))))

(defrule apply-k-of-tuple
  (implies
    (and (wf-state-p s) (> (erl-k->fuel k) 0)
         (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :tuple)
         (equal (erl-val-kind (erl-state->in s)) :cons))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in (erl-state-fix s)
             (make-erl-val-tuple :lst (erl-val-cons->lst (erl-state->in s))))))
  :enable (apply-k-of-step eval-k))

(defrule apply-k-of-tuple-excpt
  (implies
    (and (> (erl-k->fuel k) 0) (equal (erl-val-kind (erl-state->in s)) :excpt)
         (equal (kont-kind (erl-k->kont k)) :tuple))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))