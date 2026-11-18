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

; Function Return Kont-Step ----------------------------------------------------

; eval-k -----------------------------------------------------------------------

(defrule eval-k-of-function-return->klst
  (implies
    (equal (kont-kind (erl-k->kont k)) :function-return)
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-function-return->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->bind-mod
        s
        (kont-function-return->bind (erl-k->kont k))
        (kont-function-return->module (erl-k->kont k)))))
  :enable eval-k)

; apply-k ----------------------------------------------------------------------

(defrule apply-k-of-function-return
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (apply-k s (cons k nil))
           (update-erl-state->bind-mod
             s
             (kont-function-return->bind (erl-k->kont k))
             (kont-function-return->module (erl-k->kont k)))))
  :enable apply-k-of-step)