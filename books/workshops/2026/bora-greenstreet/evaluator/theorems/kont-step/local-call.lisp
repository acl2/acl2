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
(include-book "functions")
(include-book "exprs")

; Local Call Kont-Step ---------------------------------------------------------

; The following theorems show that evaluating a continuation for a local call
; expression is equivalent to evaluating the arguments in order, and then invoking
; the call evaluator which will then provide the body of the function to execute.


; eval-k -----------------------------------------------------------------------

; expr-local-call
(defrule eval-k-of-expr-local-call->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-call->args
                          (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-local-call 
                  :call (node-call->fn
                          (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-local-call->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

; kont-local-call
(defrule eval-k-of-local-call->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons)) nil)
        ((not (mv-nth
                1
                (eval-local-call
                  s
                  (kont-local-call->call (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
          nil)
        (t (list (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont (make-kont-exprs :exprs
                    (mv-nth
                      1
                      (eval-local-call
                        s
                        (kont-local-call->call (erl-k->kont k))
                        (erl-val-cons->lst (erl-state->in s))))))
                (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont (make-kont-function-return
                          :bind (erl-state->bind s)
                          :module (erl-state->module s))))))))
  :enable eval-k)

(defrule eval-k-of-local-call->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons))
         (update-erl-state->in 
           s
           (make-erl-val-reject :err "Local call: invalid arg list.")))
        (t (mv-nth 
             0
             (eval-local-call
               s
               (kont-local-call->call (erl-k->kont k))
               (erl-val-cons->lst (erl-state->in s))))))))
  :enable eval-k)


; apply-k ----------------------------------------------------------------------

(defrule apply-k-of-expr-local-call
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal (apply-k s (cons k nil))
           (apply-k
             (apply-k 
               s
               (list (make-erl-k
                       :fuel (1- (erl-k->fuel k))
                       :kont (make-kont-expr
                               :expr (node-call->args
                                       (kont-expr->expr (erl-k->kont k)))))))
             (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-local-call 
                            :call (node-call->fn
                                    (kont-expr->expr (erl-k->kont k)))))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k
            :fuel (1- (erl-k->fuel k))
            :kont (make-kont-expr
                    :expr (node-call->args
                            (kont-expr->expr (erl-k->kont k))))))))

(defruled apply-k-of-local-call-no-match
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 
                1 
                (eval-local-call
                  s
                  (kont-local-call->call (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (mv-nth 
              0 
              (eval-local-call
                s
                (kont-local-call->call (erl-k->kont k))
                (erl-val-cons->lst (erl-state->in s))))))
  :enable apply-k-of-step)

(defruled apply-k-of-local-call-when-match
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 
           1 
           (eval-local-call
             s
             (kont-local-call->call (erl-k->kont k))
             (erl-val-cons->lst (erl-state->in s))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (apply-k
             (mv-nth
               0 
               (eval-local-call
                 s
                 (kont-local-call->call (erl-k->kont k))
                 (erl-val-cons->lst (erl-state->in s))))
             (list (make-erl-k 
                     :fuel (1- (erl-k->fuel k))
                     :kont (make-kont-exprs :exprs
                              (mv-nth
                                1 
                                (eval-local-call
                                  s
                                  (kont-local-call->call (erl-k->kont k))
                                  (erl-val-cons->lst (erl-state->in s))))))
                    (make-erl-k
                      :fuel (1- (erl-k->fuel k)) 
                      :kont (make-kont-function-return 
                              :bind (erl-state->bind s) 
                              :module (erl-state->module s)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-local-call-excpt
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :excpt)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))


; more theorems ----------------------------------------------------------------

; A local call that returns a well-formed result, restores the bindings.
(defrule bindings-of-apply-k-of-local-call
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :local-call)
         (> (erl-k->fuel k) 1)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 1 (eval-local-call s
                     (kont-local-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))
         (wf-state-p (apply-k s (list k))))
    (equal (erl-state->bind (apply-k s (list k))) (erl-state->bind s)))
  :enable apply-k-of-local-call-when-match)