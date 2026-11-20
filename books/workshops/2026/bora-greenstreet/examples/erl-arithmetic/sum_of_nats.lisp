; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../../evaluator/top")

(set-induction-depth-limit 1)

; Erlang worlds with the following function defined locally:
;
; sum_of_nats(0) -> 0;
; sum_of_nats(X) when is_integer(X), X > 0 -> X + sum_of_nats(X - 1).
;
; We make no claim about the rest of the world, i.e. there could be other
; modules and functions.
(define sum-world-p ((w world-p))
  :enabled t
  (b* (((unless (omap::assoc 'local w)) nil)
       (defns (module->fn-defns (omap::lookup 'local w)))
       (fn '((name . sum_of_nats) (arity . 1)))
       ((unless (omap::assoc fn defns)) nil))
      (equal
        (omap::lookup fn defns)
        '(((cases (:integer 0)) (guards) (body (:integer 0)))
          ((cases (:var X))
           (guards ((:call is_integer (:cons (:var X) (:nil))) 
                    (:binop > (:var X) (:integer 0))))
           (body (:binop +
                    (:var X) 
                    (:call sum_of_nats
                      (:cons (:binop - (:var X) (:integer 1)) (:nil))))))))))

; We want to prove the closed form of summation:
;  1 + 2 + ... + n = n * (n + 1) / 2
; holds for the Erlang function [sum_of_nats] defined above.
;
; First, we will show that the Erlang [sum_of_nats] is equivalent to the
; the Lisp [sum-of-nats]. Then, we will be able to use the existing
; ACL2 theorems to complete the proof.

; ACL2 sum_of_nats
(local (define sum-of-nats ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum-of-nats (1- n))))))

; While it is not necessary to admit the theorem below, this lemma speeds up 
; the proof quite a bit. ACL2 has an easier time dealing with the cases of 
; eval-local-call and apply-k separately. I suspect some of this can be turned
; into more general lemmas about eval-local-call.
(local (defrule eval-local-call-of-sum-of-nats
  (implies
    (and 
      (wf-state-p s)
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      (erl-vlst-p args)
      (car args) (not (cdr args))
      (equal (erl-val-kind (car args)) :integer))
    (equal 
      (eval-local-call s 'sum_of_nats args)
      (if (> (erl-val-integer->val (car args)) 0)
          (mv (update-erl-state->bind
                (update-erl-state->in s (car args))
                (omap::update 'X (car args) nil))
              '((:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum_of_nats 
                    (:cons (:binop - (:var X) (:integer 1)) 
                            (:nil))))))
          (if (equal (erl-val-integer->val (car args)) 0)
              (mv (update-erl-state->bind
                    (update-erl-state->in s (car args))
                    nil)
                  '((:integer 0)))
              (mv (update-erl-state->in s 
                    (make-erl-val-excpt 
                      :err-class (make-erl-val-atom :val 'error)
                      :err-reason (make-erl-val-atom :val 'function_clause))) 
                  nil)))))
  :enable
    (omap::lookup-of-update eval-local-call eval-clauses
     eval-clauses-when-consp match-args eval-match eval-guard-seq
     eval-guard-seq-when-consp eval-guard eval-guard-expr eval-bif
     apply-erl-binop apply-erl-comp-binop erl-compare)
  :prep-lemmas
    ((defrule lemma-1
      (implies
        (and (erl-val-p x) (equal (erl-val-kind x) :integer))
        (integerp (cadr x)))
      :enable (erl-val-p erl-val-kind))
     (defrule lemma-2
      (implies
        (and (erl-val-p x) (equal (erl-val-kind x) :integer)
            (not (equal x '(:integer 0))))
        (not (equal (cadr x) 0)))
       :cases ((equal (cadr x) 0))
       :enable (erl-val-p erl-val-kind len)
       :expand ((len (cdr x)) (len (cddr x))))
     (defrule lemma-3
      (implies
        (and (erl-vlst-p args) (equal (erl-val-kind (car args)) :integer)
            (not (equal '(:integer 0) (car args))) (car args))
        (not (equal (erl-val-integer->val (car args)) 0)))
      :enable (erl-val-integer->val)
      :expand (erl-vlst-p args)))))

; Some trivial lemmas
(local (defrule wf-state-p-of-cons
  (implies (equal (erl-val-kind (erl-state->in s)) :cons)
           (wf-state-p s))
  :enable wf-state-p))

(local (defrule wf-state-p-of-integer
  (implies (equal (erl-val-kind (erl-state->in s)) :integer)
           (wf-state-p s))
  :enable wf-state-p))

; Induction schema for apply-k-of-sum-of-nats.
(local (define eval-sum-of-nats-induct (args k)
  (declare (irrelevant k))
  :measure (nfix (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))))
  :verify-guards nil
  :enabled t
  (if (< (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))) 0)
      nil
      (if (= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))) 0)
          t
          (eval-sum-of-nats-induct
            (update-erl-state->bind
              (update-erl-state->in args
                (erl-val-cons
                  (list
                    (erl-val-integer
                      (+ -1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))))))))
              (omap::update 'X (car (erl-val-cons->lst (erl-state->in args))) nil))
            (erl-k (+ -5 (erl-k->fuel k)) '(:local-call sum_of_nats)))))))

; Base Case
(local (defrule eval-sum-of-nats-base-case
  (implies
    (and
      ; there is enough fuel
      (> (erl-k->fuel k) 5)
      ; the world and module are correctly set
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      ; the expression is a local call to sum_of_nats
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      ; there is a single integer argument
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      ; the argument is equal to zero
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal (erl-state->in (apply-k s (list k))) (erl-val-integer 0)))
  :use (:instance apply-k-of-local-call-when-match)))

; Inductive Step.
(local (defrule eval-of-sum-of-nats-inductive-step
  (implies
    (and
      ; there is enough fuel
      (< 8 (erl-k->fuel k))
      ; the world and module are correctly set
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      ; the expression is a local call to sum_of_nats
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      ; there is a single integer argument
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      ; the argument is greater than zero.
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      ; the recursive call returns an integer (should be known from the inductive hypothesis)
      (equal
        (erl-val-kind
          (erl-state->in
            (apply-k
              (update-erl-state->bind
                (update-erl-state->in s
                  (erl-val-cons
                    (list
                      (erl-val-integer
                        (+ -1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))))))))
                (omap::update 'X (car (erl-val-cons->lst (erl-state->in s))) nil))
              (list (erl-k (+ -5 (erl-k->fuel k)) '(:local-call sum_of_nats))))))
        :integer))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (apply-erl-binop
        '+
        (car (erl-val-cons->lst (erl-state->in s)))
        (erl-state->in
          (apply-k
            (update-erl-state->bind
              (update-erl-state->in s
                (erl-val-cons
                  (list
                    (erl-val-integer
                      (+ -1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))))))))
              (omap::update 'X (car (erl-val-cons->lst (erl-state->in s))) nil))
            (list (erl-k (+ -5 (erl-k->fuel k)) '(:local-call sum_of_nats))))))))
  :use (:instance apply-k-of-local-call-when-match)
  :enable (omap::lookup-of-update apply-k-of-binop-expr1 apply-k-of-cons)))

; local call to sum_of_nats is equivalent to the acl2 sum-of-nats.
(local (defrule eval-sum-of-nats
  (implies
    (and
      ; there is enough fuel for each recursive call
      (< (* 8 (+ 1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))
         (erl-k->fuel k))
      ; the world and module are correctly set
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      ; the expression is a local call to sum_of_nats
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      ; there is a single integer argument
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      ; the argument is a natural number.
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val
        (sum-of-nats
          (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))))
  :induct (eval-sum-of-nats-induct s k)
  :enable sum-of-nats))

; Now we use the existing ACL2 arithemtic books.
(local (include-book "arithmetic/top" :dir :system))

; closed form of sum of nats
(local (defrule cfs 
  (implies (natp n) (equal (sum-of-nats n) (/ (* n (+ n 1)) 2)))
  :enable sum-of-nats))

; Closed of summation for the Erlang suum_of_nats.
(defrule eval-sum-of-nats-closed-form
  (implies
    (and
      ; there is enough fuel for each recursive call
      (< (* 8 (+ 1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))
         (erl-k->fuel k))
      ; the world and module are correctly set
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      ; the expression is a local call to sum_of_nats
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      ; there is a single integer argument
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      ; the argument is a natural number.
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val
        (/ (* (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))
              (+ (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 1)) 2)))))

; Same as above, restated to be more readable.
(defrule apply-k-of-sum-of-nats-closed-form-simpl
  (implies
    (and
      ; Let's say x is the argument.
      (equal x (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))))
      ; there is enough fuel for each recursive call
      (< (* 8 (+ 1 x)) (erl-k->fuel k))
      ; the world and module are correctly set
      (sum-world-p (erl-state->world s))
      (equal (erl-state->module s) 'local)
      ; the expression is a local call to sum_of_nats
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      ; there is a single integer argument
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      ; the argument is a natural number.
      (>= x 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val (/ (* x (+ x 1)) 2)))))