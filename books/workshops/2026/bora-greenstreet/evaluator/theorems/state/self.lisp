; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../core/eval-theorems")

(set-induction-depth-limit 1)

; Erl-State Self Theorems ------------------------------------------------------

; The theorems below reason about what happens the self field of an erl-state
; after various operations.

(local (defrule erl-state->self-of-eval-match
  (equal (erl-state->self (eval-match p s))
          (erl-state->self s))
  :enable eval-match))

(local (defrule erl-state->self-of-match-args
  (equal (erl-state->self (match-args cs args s))
         (erl-state->self s))
  :enable match-args))

(local (defrule erl-state->self-of-eval-clauses-when-consp
  (equal (erl-state->self (mv-nth 0 (eval-clauses-when-consp args cls s)))
          (erl-state->self s))
  :enable eval-clauses-when-consp))

(local (defrule erl-state->self-of-eval-clauses
  (equal (erl-state->self (mv-nth 0 (eval-clauses args cls s)))
          (erl-state->self s))
  :enable eval-clauses))

(defrule erl-state->self-of-eval-local-call
  (equal (erl-state->self (mv-nth 0 (eval-local-call s c args)))
          (erl-state->self s))
  :enable eval-local-call)

(defrule erl-state->self-of-eval-remote-call
  (equal (erl-state->self (mv-nth 0 (eval-remote-call s m c args)))
          (erl-state->self s))
  :enable eval-remote-call)

(defrule erl-state->self-of-eval-fun-call
  (equal (erl-state->self (mv-nth 0 (eval-fun-call s f args)))
          (erl-state->self s))
  :enable eval-fun-call)

(defrule erl-state->self-of-erl-receive
  (equal (erl-state->self (mv-nth 0 (eval-receive s clauses)))
          (erl-state->self s))
  :enable eval-receive)

; The self field of an erl-state never changes during evaluation.
(defrule apply-k-of-self
  (equal (erl-state->self (apply-k s klst))
         (erl-state->self s))
  :expand (eval-k (car klst) s)
  :enable (apply-k))

(defrule eval-k-of-self
    (equal (erl-state->self (erl-s-klst->s (eval-k k s)))
           (erl-state->self s))
  :enable eval-k)