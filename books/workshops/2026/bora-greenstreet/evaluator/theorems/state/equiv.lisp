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
(include-book "update")
(local (include-book "std/lists/nthcdr" :dir :system))

(set-induction-depth-limit 1)

; State Equivalence ------------------------------------------------------------

(defruled update-erl-state->in-when-only-diff-val
  (implies
    (and (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (erl-state->self s1) (erl-state->self s2))
         (equal (erl-state->outbox s1) (erl-state->outbox s2)))
    (equal (update-erl-state->in s1 v) (update-erl-state->in s2 v)))
  :enable update-erl-state->in)

(defruled apply-k-of-expr-when-diff-val
  (implies
    (and (wf-state-p s1) (not (equal (erl-val-kind (erl-state->in s1)) :excpt))
         (wf-state-p s2) (not (equal (erl-val-kind (erl-state->in s2)) :excpt))
         (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (erl-state->self s1) (erl-state->self s2))
         (equal (erl-state->outbox s1) (erl-state->outbox s2))
         (equal (kont-kind (erl-k->kont k)) :expr))
    (equal (apply-k s1 (cons k nil))
           (apply-k s2 (cons k nil))))
  :expand
    ((apply-k s1 (list k))
     (apply-k s2 (list k))
     (eval-k k s1)
     (eval-k k s2))
  :enable update-erl-state->in)

(defruled erl-state-send-when-nil-outbox
  (implies
    (and (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (erl-state->self s1) (erl-state->self s2))
         (equal (erl-state->outbox s2) nil))
    (equal (erl-state->outbox s1)
           (erl-state->outbox (update-erl-state->outbox s2 (erl-state->outbox s1)))))
  :enable erl-state-send)

(defruled apply-k-of-expr-when-diff-val-and-outbox
  (implies
    (and (wf-state-p s1) (not (equal (erl-val-kind (erl-state->in s1)) :excpt))
         (wf-state-p s2) (not (equal (erl-val-kind (erl-state->in s2)) :excpt))
         (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (erl-state->self s1) (erl-state->self s2))
         (equal (erl-state->outbox s2) nil)
         (equal (kont-kind (erl-k->kont k)) :expr))
    (equal (apply-k s1 (cons k nil))
           (apply-k (update-erl-state->outbox s2 (erl-state->outbox s1)) (cons k nil))))
  :use ((:instance erl-state-send-when-nil-outbox)
        (:instance apply-k-of-expr-when-diff-val
          (s2 (update-erl-state->outbox s2 (erl-state->outbox s1))))))

; (defruled erl-state-send-when-prefix-outbox
;   (implies
;     (and (equal (erl-state->module s1) (erl-state->module s2))
;          (equal (erl-state->bind s1) (erl-state->bind s2))
;          (equal (erl-state->world s1) (erl-state->world s2))
;          (equal (erl-state->self s1) (erl-state->self s2))
;          (equal (erl-state->outbox s2) (take n (erl-state->outbox s1)))
;          (< n (length (erl-state->outbox s1)))
;          (natp n))
;     (equal (erl-state->outbox s1)
;            (erl-state->outbox (erl-state-send s2 (nthcdr n (erl-state->outbox s1))))))
;   :enable erl-state-send)

; (defruled apply-k-of-expr-when-diff-val-and-postfix-of-outbox
;   (implies
;     (and (wf-state-p s1)
;          (wf-state-p s2)
;          (equal (erl-state->module s1) (erl-state->module s2))
;          (equal (erl-state->bind s1) (erl-state->bind s2))
;          (equal (erl-state->world s1) (erl-state->world s2))
;          (equal (erl-state->self s1) (erl-state->self s2))
;          (equal (erl-state->outbox s2) (take n (erl-state->outbox s1)))
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (< n (length (erl-state->outbox s1)))
;          (natp n))
;     (equal (apply-k s1 (cons k nil))
;            (apply-k (erl-state-send s2 (nthcdr n (erl-state->outbox s1))) (cons k nil))))
;   :use ((:instance erl-state-send-when-prefix-outbox)
;         (:instance apply-k-of-expr-when-diff-val
;           (s2 (erl-state-send s2 (nthcdr n (erl-state->outbox s1)))))))

