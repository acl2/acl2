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

; Erl-State World Theorems -----------------------------------------------------

; The theorems below reason about what happens the world field of an erl-state
; after various operations.

(local (defrule erl-state->world-of-eval-match
  (equal (erl-state->world (eval-match p s))
         (erl-state->world s))
  :enable eval-match))

(local (defrule erl-state->world-of-match-args
  (equal (erl-state->world (match-args cs args s))
         (erl-state->world s))
  :enable match-args))

(local (defrule erl-state->world-of-eval-clauses-when-consp
  (equal (erl-state->world (mv-nth 0 (eval-clauses-when-consp args cls s)))
         (erl-state->world s))
  :enable eval-clauses-when-consp))

(local (defrule erl-state->world-of-eval-clauses
  (equal (erl-state->world (mv-nth 0 (eval-clauses args cls s)))
         (erl-state->world s))
  :enable eval-clauses))

(defrule erl-state->world-of-eval-local-call
  (equal (erl-state->world (mv-nth 0 (eval-local-call s c args)))
         (erl-state->world s))
  :enable eval-local-call)

(defrule erl-state->world-of-eval-remote-call
  (equal (erl-state->world (mv-nth 0 (eval-remote-call s m c args)))
         (erl-state->world s))
  :enable eval-remote-call)

(defrule erl-state->world-of-eval-fun-call
  (equal (erl-state->world (mv-nth 0 (eval-fun-call s f args)))
         (erl-state->world s))
  :enable eval-fun-call)

(defrule erl-state->world-of-erl-receive
  (equal (erl-state->world (mv-nth 0 (eval-receive s clauses)))
         (erl-state->world s))
  :enable eval-receive)

; The world field of an erl-state never changes during evaluation.
(defrule apply-k-of-world
  (equal (erl-state->world (apply-k s klst))
         (erl-state->world s))
  :expand (eval-k (car klst) s)
  :enable (apply-k))

(defrule eval-k-of-world
    (equal (erl-state->world (erl-s-klst->s (eval-k k s)))
           (erl-state->world s))
  :enable eval-k)