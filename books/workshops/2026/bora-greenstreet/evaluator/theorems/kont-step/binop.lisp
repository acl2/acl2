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

; Binop Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a binop 
; expression is equivalent to evaluating the left operand, the right operand
; and then applying the binop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

; eval-k -----------------------------------------------------------------------

; expr-binop
(defrule eval-k-of-expr-binop->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-binop->left
                          (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-binop-expr1
                  :op (node-binop->op
                        (kont-expr->expr (erl-k->kont k)))
                  :right (node-binop->right
                          (kont-expr->expr (erl-k->kont k)))
                  :bind-0 (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-expr-binop->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (erl-s-klst->s (eval-k k s)) (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; kont-binop-expr1
(defrule eval-k-of-binop-expr1->klst
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (kont-binop-expr1->right (erl-k->kont k))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-binop-expr2
                  :op (kont-binop-expr1->op (erl-k->kont k))
                  :val (erl-state->in s)
                  :left-bind (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-binop-expr1->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in-bind
        s
        (make-erl-val-none)
        (kont-binop-expr1->bind-0 (erl-k->kont k)))))
  :enable eval-k)

; kont-binop-expr2
(defrule eval-k-of-binop-expr2->klst
  (implies 
    (equal (kont-kind (erl-k->kont k)) :binop-expr2)
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-binop-expr2->s
  (implies
    (and (> (erl-k->fuel k) 0) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond 
        ((not (omap::compatiblep (erl-state->bind s) (kont-binop-expr2->left-bind (erl-k->kont k))))
          (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst
                            (list (make-erl-val-atom :val 'badmatch) (erl-state->in s))))))
        ((and (pid-p (kont-binop-expr2->val (erl-k->kont k)))
              (equal (kont-binop-expr2->op (erl-k->kont k)) '!))
         (erl-state-send s
          (kont-binop-expr2->val (erl-k->kont k)) (erl-state->in s)
          (omap::update* (erl-state->bind s) (kont-binop-expr2->left-bind (erl-k->kont k)))))
        ((equal (kont-binop-expr2->op (erl-k->kont k)) '!)
         (update-erl-state->in s
          (make-erl-val-excpt
            :err-class (make-erl-val-atom :val 'error)
            :err-reason (make-erl-val-atom :val 'badarg))))
        (t
          (update-erl-state->in-bind s
            (apply-erl-binop
              (kont-binop-expr2->op (erl-k->kont k))
              (kont-binop-expr2->val (erl-k->kont k))
              (erl-state->in s))
            (omap::update*
              (erl-state->bind s)
              (kont-binop-expr2->left-bind (erl-k->kont k))))))))
  :enable eval-k)


; apply-k  ---------------------------------------------------------------------

(defrule apply-k-of-expr-binop
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-binop->left
                                      (kont-expr->expr (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-binop-expr1
                            :op (node-binop->op
                                  (kont-expr->expr (erl-k->kont k)))
                            :right (node-binop->right
                                      (kont-expr->expr (erl-k->kont k)))
                            :bind-0 (erl-state->bind s)))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-expr 
              :expr
                (node-binop->left (kont-expr->expr (erl-k->kont k))))))))

(defruled apply-k-of-binop-expr1
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal (apply-k s (cons k nil))
           (apply-k
             (apply-k
               (update-erl-state->bind s (kont-binop-expr1->bind-0 (erl-k->kont k)))
               (list (make-erl-k
                       :fuel (1- (erl-k->fuel k))
                       :kont (make-kont-expr
                               :expr (kont-binop-expr1->right (erl-k->kont k))))))
             (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-binop-expr2
                              :op (kont-binop-expr1->op (erl-k->kont k))
                              :val (erl-state->in s)
                              :left-bind (erl-state->bind s)))))))
  :enable apply-k-of-step
  :use
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in-bind s (make-erl-val-none) (kont-binop-expr1->bind-0 (erl-k->kont k))))
      (s2 (update-erl-state->bind s (kont-binop-expr1->bind-0 (erl-k->kont k))))
      (k (make-erl-k
            :fuel (1- (erl-k->fuel k))
            :kont (make-kont-expr
                    :expr (kont-binop-expr1->right (erl-k->kont k)))))))

(defrule apply-k-of-binop-expr1-excpt
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :excpt)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal (apply-k s (cons k nil))
           (erl-state-fix s)))
  :enable (eval-k apply-k-of-step))

(defrule apply-k-of-binop-expr2-compatible
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (omap::compatiblep 
           (erl-state->bind s)
           (kont-binop-expr2->left-bind (erl-k->kont k)))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (not (equal (kont-binop-expr2->op (erl-k->kont k)) '!)))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
            s
            (apply-erl-binop
              (kont-binop-expr2->op (erl-k->kont k))
              (kont-binop-expr2->val (erl-k->kont k))
              (erl-state->in s))
            (omap::update*
              (erl-state->bind s)
              (kont-binop-expr2->left-bind (erl-k->kont k))))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr2-compatible-send
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (omap::compatiblep 
           (erl-state->bind s)
           (kont-binop-expr2->left-bind (erl-k->kont k)))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (equal (kont-binop-expr2->op (erl-k->kont k)) '!)
         (pid-p (kont-binop-expr2->val (erl-k->kont k))))
    (equal (apply-k s (cons k nil))
           (erl-state-send
             s
             (kont-binop-expr2->val (erl-k->kont k))
             (erl-state->in s)
             (omap::update*
              (erl-state->bind s)
              (kont-binop-expr2->left-bind (erl-k->kont k))))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr2-compatible-bad-send
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (omap::compatiblep 
           (erl-state->bind s)
           (kont-binop-expr2->left-bind (erl-k->kont k)))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (equal (kont-binop-expr2->op (erl-k->kont k)) '!)
         (not (pid-p (kont-binop-expr2->val (erl-k->kont k)))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-atom :val 'badarg)))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr2-incompatible
  (implies
    (and (wf-state-p s) (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (not (omap::compatiblep 
                (erl-state->bind s)
                (kont-binop-expr2->left-bind (erl-k->kont k))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in s
            (make-erl-val-excpt
              :err-class (make-erl-val-atom :val 'error)
              :err-reason (make-erl-val-tuple :lst
                            (list (make-erl-val-atom :val 'badmatch) (erl-state->in s)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr2-excpt
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :excpt)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (apply-k s (cons k nil)) (erl-state-fix s)))
  :enable (apply-k-of-step eval-k))

; apply-k when wf --------------------------------------------------------------

(local (defrule fuel-crock
  (implies
    (wf-state-p (apply-k s (cons k nil)))
    (> (erl-k->fuel k) 0))
  :enable apply-k))

(defrule apply-k-of-binop-has-enough-fuel-when-wf-1
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (> (erl-k->fuel k) 1))
  :disable apply-k-of-expr-binop
  :use ((:instance apply-k-of-expr-binop)
        (:instance fuel-crock
          (s s)
          (k (erl-k (+ -1 (erl-k->fuel k))
                    (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))))

(defrule binop-left-well-formed
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (wf-state-p
      (apply-k
        s
        (list (make-erl-k
                :fuel (1- (erl-k->fuel k))
                :kont (make-kont-expr
                        :expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))))
  :disable apply-k-of-expr-binop
  :use (:instance apply-k-of-expr-binop))

(defrule apply-k-of-binop-has-enough-fuel-when-wf-2
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (equal (erl-val-kind (erl-state->in s)) :excpt))
         (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :excpt))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (> (erl-k->fuel k) 2))
  :disable (apply-k-of-expr-binop apply-k-of-binop-expr1 apply-k-of-binop-has-enough-fuel-when-wf-1)
  :enable apply-k
  :use ((:instance apply-k-of-binop-has-enough-fuel-when-wf-1)
        (:instance apply-k-of-expr-binop)
        (:instance apply-k-of-binop-expr1
          (s (apply-k s
              (list (erl-k 1 (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
          (k (erl-k 1 (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                        (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                        (erl-state->bind s)))))))