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

(set-induction-depth-limit 1)

; Properties of State Update ---------------------------------------------------

; There are also some rules on eval/erl-state.lisp

(defrule wf-state-of-update-erl-state->in
  (implies
    (not (or (equal (erl-val-kind v) :flimit)
             (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :excpt)
             (equal (erl-val-kind v) :receive)
             (equal (erl-val-kind v) :blocked)))
    (wf-state-p (update-erl-state->in s v)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->in-bind
  (implies
    (not (or (equal (erl-val-kind v) :flimit)
             (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :excpt)
             (equal (erl-val-kind v) :receive)
             (equal (erl-val-kind v) :blocked)))
    (wf-state-p (update-erl-state->in-bind s v b)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->bind
  (implies
    (wf-state-p s)
    (wf-state-p (update-erl-state->bind s b)))
  :enable wf-state-p)

(defrule non-wf-state-of-update-erl-state->bind
  (implies
    (not (wf-state-p s))
    (not (wf-state-p (update-erl-state->bind s b))))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->mod
  (implies
    (wf-state-p s)
    (wf-state-p (update-erl-state->mod s m)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->bind-mod
  (implies
    (wf-state-p s)
    (wf-state-p (update-erl-state->bind-mod s b m)))
  :enable wf-state-p)

(defrule wf-state-of-erl-state-send
  (implies
    (wf-state-p s)
    (wf-state-p (erl-state-send s dst val bind)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->outbox
  (implies
    (wf-state-p s)
    (wf-state-p (update-erl-state->outbox s ms)))
  :enable wf-state-p)

(defrule update-bind-mod-to-update-in
  (implies
    (and (equal (erl-state->world s1) (erl-state->world s2))
         (equal (erl-state->self s1) (erl-state->self s2))
         (equal (erl-state->outbox s1) (erl-state->outbox s2)))
    (equal (update-erl-state->bind-mod
             s2
             (erl-state->bind s1)
             (erl-state->module s1))
           (update-erl-state->in s1 (erl-state->in s2))))
  :enable (update-erl-state->in update-erl-state->bind
           update-erl-state->mod update-erl-state->bind-mod))