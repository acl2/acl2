; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-state")

(set-induction-depth-limit 1)

; Termination Proof for apply-k ------------------------------------------------

(encapsulate
  ; Evaluation function and a recognizer for its return value
  (((eval-op * *) => *))

  ; Witness function
  (local (defun eval-op (k s)
      (make-erl-s-klst
        :s (erl-state-fix s)
        :klst (and (> (erl-k->fuel k) 0)
                   (list (change-erl-k k :fuel (1- (erl-k->fuel k)))
                         (change-erl-k k :fuel (1- (erl-k->fuel k))))))))

  ; Constraints
  (defrule erl-state-p-of-eval-op->s
    (erl-state-p (erl-s-klst->s (eval-op k s))))
  (defrule elr-klst-p-of-eval-op->klst
    (erl-klst-p (erl-s-klst->klst (eval-op k s))))

  (defrule len-of-eval-op->klst
    (let ((ks (erl-s-klst->klst (eval-op k s))))
         (implies ks
           (and (consp ks) (consp (cdr ks)) (not (cddr ks))))))
  (defrule eval-op-decreases-fuel
      (let ((ks (erl-s-klst->klst (eval-op k s))))
           (implies
             ks
             (and (equal (erl-k->fuel (car ks)) (- (erl-k->fuel k) 1))
                  (equal (erl-k->fuel (cadr ks)) (- (erl-k->fuel k) 1)))))))

; measure for erl-klst evaluation
(define klst-measure ((kl erl-klst-p))
  :returns m
  :measure (len kl)
  (let ((kl (erl-klst-fix kl)))
       (if (consp kl)
           (+ (expt 3 (erl-k->fuel (car kl)))
              (klst-measure (cdr kl)))
           0))
  ///
    (defcong erl-klst-equiv equal (klst-measure kl) 1)

    ; some lemmas for subsequent theorems about klst-measure
    (local (encapsulate nil
      (defrule integerp-of-expt3
	      (implies (natp i) (integerp (expt 3 i)))
	      :rule-classes ((:forward-chaining :trigger-terms ((expt 3 i)))))

      (defrule pos-of-expt3
	      (implies (natp i) (< 0 (expt 3 i)))
	      :rule-classes :linear)

      (defrule klst-measure-of-cons-lemma
        (equal (klst-measure (cons k kl))
               (+ (expt 3 (erl-k->fuel k)) (klst-measure kl)))
        :disable klst-measure
        :expand ((klst-measure (cons k kl))))))

    (defrule natp-of-klst-measure
      (natp (klst-measure kl)))

    (defrule klst-measure-of-nil
      (implies (not (consp kl))
	             (equal (klst-measure kl) 0)))

    (defrule klst-measure-of-cons
      (< (klst-measure kl)
	       (klst-measure (cons k kl)))
      :in-theory (disable klst-measure))

    (defrule klst-measure-of-append
      (equal (klst-measure (append kl1 kl2))
	           (+ (klst-measure kl1) (klst-measure kl2))))

    (defrule eval-op-decreases-klst-measure
      (< (klst-measure (append (erl-s-klst->klst (eval-op k s)) kl))
	       (klst-measure (cons k kl)))
      :disable len-of-eval-op->klst
      :use ((:instance len-of-eval-op->klst))))