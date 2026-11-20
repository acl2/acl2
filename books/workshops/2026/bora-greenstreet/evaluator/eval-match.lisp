; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-state")
(include-book "eval-numeric")

(set-induction-depth-limit 1)

; Pattern Count Decreases ------------------------------------------------------

(local (defrule node-count-of-pattern-cons->tl
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :cons))
           (< (node-count (node-cons->tl (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-cons->hd
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :cons))
           (< (node-count (node-cons->hd (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-tuple->lst
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :tuple))
           (< (node-count (node-tuple->lst (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-match->lhs
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :match))
           (< (node-count (node-match->lhs (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-match->rhs
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :match))
           (< (node-count (node-match->rhs (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))


; Erlang Pattern Matching ------------------------------------------------------

; Erlang reference manual explains: In pattern matching, a left-hand side pattern 
; is matched against a right-hand side term. If the matching succeeds, any unbound 
; variables in the pattern become bound. If the matching fails, an exception 
; is raised.
;
; Supported patterns:
; - Any valid Erlang term,
; - Bound or unbound variables, including the wildcard '_'
; - Pattern1 = Pattern2
; - Arithmetic Expressions
;
; An arithmetic expressions can be used in patterns if:
; - It uses only numeric or bitwise operators.
; - Its value can be evaluated to a constant when complied.
;
; Patterns allowed by Erlang that are not supported currently:
; - String Prefix in Patterns, for example: "hello " ++ X = "hello world".
;
; Implementation:
; - If there is an arithmetic expression, evaluate it and then 
;   check if the result is equal to the right-hand side value. The arithmetic
;   expression should have been evaluated at compile time, so the AST will be
;   rejected if there is an exception raised.
; - If the pattern is a term or a bound variable, check if it is equal
;   to the right-hand side value. Lists and tuples are checked element by element.
; - If there is an unbound variable, bind the variable to the right-hand side 
;   value. Ignore this step if the variable is a wildcard, '_'. 
; - If sucessful, return the right-hand side value and the new bindings,
;   otherwise throw a badmatch exception.
;
(define eval-match ((p pattern-p) (s erl-state-p))
  :returns (rs erl-state-p)
  :measure (node-count p)
  :verify-guards nil
  (b* ((p (pattern-fix p))
       ((erl-state s) (erl-state-fix s))
       
       ; Exception to throw if there is a badmatch.
       (badmatch
         (update-erl-state->in s
          (make-erl-val-excpt
            :err-class (make-erl-val-atom :val 'error)
            :err-reason (make-erl-val-tuple :lst (list (make-erl-val-atom :val 'badmatch) s.in)))))
      
       ; Rejection to throw if there is an illegal pattern.
       (badpattern (update-erl-state->in s (make-erl-val-reject :err "Illegal pattern."))))

      (if (arithm-expr-p p)
          (b* ((n (eval-numeric p))
               ((unless (equal (erl-val-kind n) :integer)) badpattern)
               ((unless (equal n s.in)) badmatch))
              s)
          (node-case p
            (:integer
              (if (and (equal (erl-val-kind s.in) :integer) 
                       (equal p.val (erl-val-integer->val s.in)))
                  s
                  badmatch))
            (:string
              (if (and (equal (erl-val-kind s.in) :cons) 
                       (equal (string=>erl-cons p.val)
                              (erl-val-cons->lst s.in)))
                  s
                  badmatch))
            (:atom
              (if (and (equal (erl-val-kind s.in) :atom) 
                       (equal p.val (erl-val-atom->val s.in)))
                  s
                  badmatch))
            (:nil
              (if (and (equal (erl-val-kind s.in) :cons) 
                       (null (erl-val-cons->lst s.in)))
                  s
                  badmatch))
            (:fun badpattern)
            (:cons
              (b* (((unless (equal (erl-val-kind s.in) :cons)) badmatch)
                   
                   ; If the left-hand side is nil when the right-hand side is not, 
                   ; it is a badmatch.
                   ((if (null (erl-val-cons->lst s.in))) badmatch)
                    
                   ; Match the car of the list.
                   ((erl-state hd) 
                    (eval-match p.hd (update-erl-state->in s (car (erl-val-cons->lst s.in)))))
                    
                   ; Match the cdr of the list.
                   ((erl-state tl) 
                    (eval-match 
                      p.tl 
                      (update-erl-state->in 
                        s
                        (make-erl-val-cons :lst (cdr (erl-val-cons->lst s.in))))))
                    
                   ; Propagate rejections.
                   ((if (equal (erl-val-kind hd.in) :reject)) hd)
                   ((if (equal (erl-val-kind tl.in) :reject)) tl)

                   ; Propagate exceptions.
                   ((if (equal (erl-val-kind hd.in) :excpt)) hd)
                   ((if (equal (erl-val-kind tl.in) :excpt)) tl)

                   ; This is supposed to return the value that failed to match. 
                   ; However, there is no easy way to figure this out.
                   ; For now, it just returns the right-hand side value.
                   ((unless (omap::compatiblep hd.bind tl.bind)) badmatch))
                  (update-erl-state->bind s (omap::update* tl.bind hd.bind))))
            (:tuple
              (b* (((unless (equal (erl-val-kind s.in) :tuple)) badmatch)

                   ; Match the elements of the tuple as if they were an Erlang list.
                   ((erl-state lst)
                    (eval-match
                      p.lst
                      (update-erl-state->in
                        s
                        (make-erl-val-cons :lst (erl-val-tuple->lst s.in)))))

                   ; Propagate rejections.
                   ((if (equal (erl-val-kind lst.in) :reject)) lst)
                  
                   ; Propagate exceptions.
                   ((if (equal (erl-val-kind lst.in) :excpt)) lst))
                  (update-erl-state->in lst s.in)))
            (:var
              (b* (; Wildcard matches any value.
                   ((if (equal p.id '_)) s)
                   
                   ; If the variable is unbound, bind it to the right-hand side value.
                   ((unless (omap::assoc p.id s.bind))
                    (update-erl-state->bind s (omap::update p.id s.in s.bind)))

                   ; If the variable is bound, it must be equal to the right-hand side value.
                   ((unless (equal (omap::lookup p.id s.bind) s.in)) badmatch))
                  s))
            (:unop badpattern)
            (:binop 
              ; Some binops is patterns are allowed in Erlang, but currently none are supported.
              badpattern)
            (:match 
              (b* (; Match both sides to the right-hand side value. 
                   ((erl-state l) (eval-match p.lhs s))
                   ((erl-state r) (eval-match p.rhs s))

                   ; Propagate rejections.
                   ((if (equal (erl-val-kind l.in) :reject)) l)
                   ((if (equal (erl-val-kind r.in) :reject)) r)

                   ; Propagate exceptions.
                   ((if (equal (erl-val-kind l.in) :excpt)) l)
                   ((if (equal (erl-val-kind r.in) :excpt)) r)

                   ; This is supposed to return the value that failed to match. 
                   ; However, there is no easy way to figure this out.
                   ; For now, it just returns the right-hand side value.
                   ((unless (omap::compatiblep r.bind l.bind)) badmatch))
                  (update-erl-state->bind s (omap::update* r.bind l.bind))))
            (:if badpattern)
            (:case-of badpattern)
            (:try badpattern)
            (:remote-call badpattern)
            (:call badpattern)
            (:fun-call badpattern)
            (:receive badpattern))))
    ///
      (verify-guards eval-match)

      (defcong pattern-equiv equal (eval-match p s) 1
        :hints (("Goal" :in-theory (enable pattern-fix pattern-p))))
      (defcong erl-state-equiv equal (eval-match p s) 2)

      (more-returns
        (rs (or (equal (erl-val-kind (erl-state->in rs)) :reject)
                (equal (erl-val-kind (erl-state->in rs)) :excpt)
                (equal (erl-val-kind (erl-state->in rs)) 
                       (erl-val-kind (erl-state->in s))))
          :name erl-val-kind-of-eval-match)))

; Match each pattern to the corresponding argument, accumulate the bindings.
; - When called by 'if' or 'case-of' clauses, this is simply a wrapper 
;   around eval-match.
(define match-args ((ps pattern-list-p) (vs erl-vlst-p) (s erl-state-p))
  :returns (rs erl-state-p)
  :measure (len (pattern-list-fix ps))
  (b* ((ps (pattern-list-fix ps))
       (vs (erl-vlst-fix vs))
       (s (erl-state-fix s))
       
       ; Match succeeds if both sides are nil.
       ((if (and (null ps) (null vs))) s)

       ; Match fails if only one side is nil.
       ((if (or (null ps) (null vs)))
        (update-erl-state->in
          s 
          (make-erl-val-reject :err "Match-Args expects same number of patterns and args")))

       ; Match the head of the list.
       ((erl-state hd) (eval-match (car ps) (update-erl-state->in s (car vs))))
       
       ; Propagate exceptions and rejections.
       ((if (or (not (wf-state-p hd)) (equal (erl-val-kind (erl-state->in hd)) :excpt))) hd))

     ; Recursively match the rest of the list.
     (match-args (cdr ps) (cdr vs) hd))
  ///
    (defcong erl-state-equiv equal (match-args pl vl s) 3)
    (defcong erl-vlst-equiv equal (match-args pl vl s) 2
      :hints (("Goal" :expand (match-args pl vl-equiv s))))
    (defcong pattern-list-equiv equal (match-args pl vl s) 1
      :hints (("Goal" :expand (match-args pl-equiv vl s)))))