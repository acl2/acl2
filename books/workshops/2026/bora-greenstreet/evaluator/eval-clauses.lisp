; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "eval-match")
(include-book "eval-guards")

; Evaluate Erlang Clauses ------------------------------------------------------

; Returns the body of the first clause which has patterns that can match the 
; given args, and a has guard sequence that is satisfied. If no clauses match, 
; nil is returned, and the caller can throw the appropiate clause error.
;
; If a clause causes an exception during pattern maching or guard evaluation
; for any reason, it is treated as if the clause failed to match and it is skipped.
;
; Remark: some operations that would have caused an exceptions in
; expression context might instead cause a rejection in a different context.
; For example, '1 div 0' as an expression would throw a badarith exception, but
; as a pattern it would instead cause a compiler error, as arithemtic expressions
; in patterns are evaluated at compile time.
;
(define eval-clauses-when-consp ((args erl-vlst-p) (cls erl-clause-list-p) (s erl-state-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  :measure (len (erl-clause-list-fix cls))
  (b* ((args (erl-vlst-fix args))
       (cls (erl-clause-list-fix cls))
       (s (erl-state-fix s))
       
       ; No clauses matched -- the caller can throw the appropiate clause error.
       ((if (null cls)) (mv s nil))

       ; Pick the first clause, get its cases and guards.
       (cases (node-clause->cases (car cls)))
       (guards (node-clause->guards (car cls)))

       ; Obtain the result of evaluating rest of the clauses.
       ; - This can catch some of the rejections, though not all.
       ((mv (erl-state rs) body) (eval-clauses-when-consp args (cdr cls) s))
       
       ; Attempt to match cases to args.
       ((erl-state ms) (match-args cases args s))
       
       ; If a case fails to match, try the rest. 
       ((if (equal (erl-val-kind ms.in) :excpt)) (mv rs body))

       ; Propagate rejections.
       ((if (not (wf-state-p ms))) (mv ms nil))
       
       ; Evaluate the guard sequence.
       (guard-result (eval-guard-seq guards ms))

       ; Propagate rejections.
       ((if (equal (erl-val-kind guard-result) :reject)) 
        (mv (update-erl-state->in s guard-result) nil))
      
       ; If no guard in the sequence was satisfied, try rest of the clause.
       ((unless (equal guard-result (make-erl-val-atom :val 'true))) (mv rs body))
      
      ; Even if the chosen clause satisfies the cases and guards,
      ; ensure that there will be no rejection in the rest of the clauses.
      ((if (not (wf-state-p rs))) (mv rs nil)))

     ; The chosen clause satisfied the cases and guards, return its body.
     (mv ms (node-clause->body (car cls))))
  ///
    (defcong erl-vlst-equiv equal (eval-clauses-when-consp args cls s) 1)
    (defcong erl-clause-list-equiv equal (eval-clauses-when-consp args cls s) 2)
    (defcong erl-state-equiv equal (eval-clauses-when-consp args cls s) 3))

; This is a wrapper around eval-clauses-when-consp which does not consider the
; case where no clauses are passed to the evaluator initially. If the evaluator 
; runs out of clauses to try, it returns nil, and the caller can decide the
; appropiate exception to throw. However, if, initially, no clauses are given to
; the evaluator, that is a cause for rejection -- the Erlang compiler expects at
; least one clause in a clause-list.
(define eval-clauses ((args erl-vlst-p) (cls erl-clause-list-p) (s erl-state-p))
  :returns (mv (s erl-state-p) (body expr-list-p))
  (b* ((args (erl-vlst-fix args))
       (cls (erl-clause-list-fix cls))
       (s (erl-state-fix s))
       ((if (null cls)) 
        (mv 
          (update-erl-state->in 
            s 
            (make-erl-val-reject :err "eval-clauses: clause list cannot be empty."))
          nil)))
      (eval-clauses-when-consp args cls s))
  ///
    (defcong erl-vlst-equiv equal (eval-clauses-when-consp args cls s) 1)
    (defcong erl-clause-list-equiv equal (eval-clauses-when-consp args cls s) 2)
    (defcong erl-state-equiv equal (eval-clauses-when-consp args cls s) 3))