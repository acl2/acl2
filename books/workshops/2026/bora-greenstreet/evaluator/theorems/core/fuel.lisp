; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "eval-theorems")

(set-induction-depth-limit 1)

; Fuel Theorems ----------------------------------------------------------------

; The following theorems show that if evaluating a value and klst terminates
; without fault, then increasing the fuel of the continuations will not change the result
; of evaluation. It is easier, and more elegant, for ACL2 to prove this for the more general
; case where each k in the klst is given more fuel, rather than, for example, only the first k.
; This is why increase-fuel and the corresponding theorems are defined.

; Increase the fuel of each continuation in klst by n.
(define increase-fuel ((klst erl-klst-p) (n natp))
  :measure (len klst)
  :returns (ks erl-klst-p)
  (b* ((klst (erl-klst-fix klst))
       (n (nfix n))
       ((if (endp klst)) nil))
      (cons (make-erl-k :kont (erl-k->kont (car klst))
                        :fuel (+ n (erl-k->fuel (car klst))))
            (increase-fuel (cdr klst) n)))
  ///
    (defcong erl-klst-equiv equal (increase-fuel klst n) 1)
    (defcong nat-equiv equal (increase-fuel klst n) 2)
    (defcong int-equiv equal (increase-fuel klst n) 2)
    
    (defrule increase-fuel-with-zero
      (implies (zp n) (equal (increase-fuel kl n) (erl-klst-fix kl)))
      :expand (increase-fuel (cdr kl) 0))
    
    (defrule increase-fuel-with-non-natp
      (implies (not (natp n)) (equal (increase-fuel kl n) (erl-klst-fix kl)))
      :do-not-induct t))


; increase-fuel is distributive over append
(defrule increase-fuel-is-distributive-over-append
  (implies
    (and (consp klst)
         (natp n)
         (wf-state-p (erl-s-klst->s (eval-k (car klst) s))))
    (equal (increase-fuel (append (erl-s-klst->klst (eval-k (car klst) s)) (cdr klst)) n)
           (append (erl-s-klst->klst (eval-k (erl-k (+ n (erl-k->fuel (car klst)))
                                                    (erl-k->kont (car klst)))
                                             s))
                   (increase-fuel (cdr klst) n))))
  :enable (eval-k increase-fuel))

; A continuation that did not cause an error in eval-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-eval
  (implies 
    (and (natp n)
         (wf-state-p (erl-s-klst->s (eval-k (car klst) s))))
    (equal (erl-s-klst->s (eval-k (erl-k (+ n (erl-k->fuel (car klst)))
                                         (erl-k->kont (car klst))) s))
           (erl-s-klst->s (eval-k (car klst) s))))
  :enable (eval-k wf-state-p))


(defcong erl-s-klst-equiv equal (erl-s-klst->klst ks) 1
  )

; A continuation that did not cause an error in apply-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-apply
  (implies
    (and (natp n)
         (wf-state-p s)
         (wf-state-p (apply-k s klst)))
    (equal (apply-k s (increase-fuel klst n))
           (apply-k s klst)))
  :enable (apply-k increase-fuel apply-k-of-append)
  :induct (apply-k s klst)
  :expand (apply-k s
                   (cons (erl-k (+ n (erl-k->fuel (car klst)))
                                (erl-k->kont (car klst)))
                        (increase-fuel (cdr klst) n)))
  :hints (("Subgoal *1/3"
            :use ((:instance increase-fuel-is-distributive-over-append)
                  (:instance more-fuel-is-good-for-eval)))))