; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "eval-clauses")

; Erlang Receive ---------------------------------------------------------------

; Attempt to receive a message by trying to match it the clauses of
; the receive expression. If successful, return the body of that clause.
; If no clauses match, return '(:blocked) which will make the evaluator
; pass control back to the scheduler.
(define eval-receive ((s erl-state-p) (cls erl-clause-list-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
        (cls (erl-clause-list-fix cls))
        ((mv (erl-state rs) body)      
         (eval-clauses (list s.in) cls s))
        ((if (equal (erl-val-kind rs.in) :reject)) (mv rs nil))
        ((if (null body))
         (mv (update-erl-state->in s (make-erl-val-blocked)) nil)))
      (mv rs body))
  
  ///
    (defcong erl-state-equiv equal (eval-receive s cls) 1)
    (defcong erl-clause-list-equiv equal (eval-receive s cls) 2))