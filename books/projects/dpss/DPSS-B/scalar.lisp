;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "coi/pattern-hint/pattern-hint" :dir :system)
(include-book "coi/types/types" :dir :system)
(include-book "math")

(encapsulate
    (
     ((LR-< * *) => *)
     ((RL-< * *) => *)
     )
  (local
   (defun LR-< (L R)
     (< (rfix L) (rfix R))))
  (local
   (defun RL-< (R L)
     (< (rfix R) (rfix L))))
  (defthm rule-1
    (implies
     (LR-< L R)
     (not (RL-< R L)))
    :rule-classes (:rewrite :forward-chaining))
  (defthm rule-2
    (implies
     (RL-< R L)
     (not (LR-< L R)))
    :rule-classes (:rewrite :forward-chaining))
  (defthm asymmetric-transitivity-1
    (implies
     (and
      (LR-< L1 R1)
      (LR-< L2 R2)
      (RL-< R1 L2))
     (LR-< L1 R2))
    :rule-classes (:rewrite :forward-chaining))
  (defthm asymmetric-transitivity-2
    (implies
     (and
      (RL-< R1 L1)
      (RL-< R2 L2)
      (LR-< L1 R2))
     (RL-< R1 L2))
    :rule-classes (:rewrite :forward-chaining))
  )
    
(defun-sk LL-< (L1 L2)
  (exists R (and (LR-< L1 R) (RL-< R L2))))

(defthm LL-inference
  (implies
   (and (LR-< L1 R)
        (RL-< R L2))
   (LL-< L1 L2))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use LL-<-suff)))

(in-theory (disable LL-<))

(defun-sk RR-< (R1 R2)
  (exists L (and (RL-< R1 L) (LR-< L R2))))

(defthm RR-inference
  (implies
   (and (RL-< R1 L)
        (LR-< L R2))
   (RR-< R1 R2))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :use RR-<-suff)))

(in-theory (disable RR-<))

;; L1 -> L0
;; R1 -> W
;; L2 -> L1
;; R2 -> R1
;; (defthm asymmetric-transitivity-1
;;     (implies
;;      (and
;;       (LR-< L0 W)
;;       (LR-< L1 R1)
;;       (RL-< W L1))
;;      (LR-< L0 R1))
;;     :rule-classes (:rewrite :forward-chaining))

(defthm LL-extend-LR-left
  (implies
   (and
    (LR-< L1 R1)
    (LL-< L0 L1))
   (LR-< L0 R1))
  :hints (("Goal" :in-theory (enable LL-<)))
  :rule-classes (:rewrite :forward-chaining)
  )

(defthm RR-extend-RL-left
  (implies
   (and
    (RL-< R1 L1)
    (RR-< R0 R1))
   (RL-< R0 L1))
  :hints (("Goal" :in-theory (enable RR-<)))
  :rule-classes (:rewrite :forward-chaining)
  )

(defthm RR-extend-LR-right
  (implies
   (and
    (LR-< L1 R1)
    (RR-< R1 R2))
   (LR-< L1 R2))
  :hints (("Goal" :in-theory (enable RR-<)))
  :rule-classes (:rewrite :forward-chaining)
  )

(defthm LL-extend-LR-right
  (implies
   (and
    (RL-< R1 L1)
    (LL-< L1 L2))
   (RL-< R1 L2))
  :hints (("Goal" :in-theory (enable LL-<)))
  :rule-classes (:rewrite :forward-chaining)
  )

(defthm oscillation-is-impossible
  (implies
   (and
    ;; (A X) (B Y) (C Z)
    (LR-< A X)
    (LR-< B Y)
    (LR-< C Z)
    ;; ..    (A Y) (B Z)
    (RL-< Y A)
    (RL-< Z B)
    ;; ..    (A Z) ..
    )
   (not (LR-< A Z))))

(include-book "math")

(defun corratio (n d)
  (/ (rfix n) (prat-fix (+ (rfix n) (rfix d)))))

(defun scalar-< (x y)
  (< (corratio x y) (corratio y x)))

(defun scalar-> (x y)
  (> (corratio x y) (corratio y x)))

(with-arithmetic
 (defthm scalar-<-is-<
   (equal (scalar-< x y)
          (< (rfix x) (rfix y)))
   :hints (("Goal" :in-theory (enable remove-reciporicals-<))))
 )

(with-arithmetic
 (defthm scalar->-is->
   (equal (scalar-> x y)
          (> (rfix x) (rfix y)))
   :hints (("Goal" :in-theory (enable remove-reciporicals-<))))
 )

(in-theory (disable scalar-< scalar->))

(defthm curious
  (implies
   (and
    (scalar-> 1.L 1.R)
    (scalar-> 2.L 2.R)
    (equal (+ (rfix 1.L) (rfix 1.R))
           (+ (rfix 2.L) (rfix 2.R))))
   (scalar-> 2.L 1.R)))

(defun inc (x)
  (1+ (rfix x)))

;;
;; This is the actual impossibility argument ..
;;
(defthm actual
  (implies
   (and
    ;; (0.L,0.R)  (1.L,2.R+1)(1.L+1,2.R) (3.L,3.R)
    (scalar-> 1.L (inc 2.R))
    (scalar-> (inc 1.L) 2.R)
    ;; (0.L,2.R+2)(0.L+1,2.R+1) (1.L+1,R.R+1)(1.L+2,R.R)
    (scalar-< 0.L (inc (inc 2.R)))
    (scalar-< (inc 0.L) (inc 2.R))
    (scalar-< (inc 1.L) (inc R.R))
    (scalar-< (inc (inc 1.L)) R.R))
   ;; (L.L,2.R+2) (0.L+1,R.R+2)(0.L+2,R.R+1) (1.L+2,R.R)
   (and (not (scalar-> (inc 0.L) (inc (inc R.R))))
        (not (scalar-> (inc (inc 0.L)) (inc R.R))))))


(defthm scalar-first-generalization-is-impossible-better
 (implies
  (and
   (scalar-> 2.L 1.R)
   (scalar-< 0.L 1.R)
   (scalar-< 2.L R.R))
  (not (scalar-> 0.L R.R))))

;;
;; This is a condensed argument ..
;;
(defthm scalar-first-generalization-is-impossible
 (implies
  (and
   ;;                        ;; 0 (1,2) 3
   (scalar-> 1.L 2.R)        ;; 1 and 2 split on the right side initially
   (scalar-< 0.L 2.R)        ;; 0 and 1 split on the left side after 1st exchange
   (scalar-< 1.L R.R))       ;; 1 amd 3 split on the left side after 1st exchange
  (not (scalar-> 0.L R.R)))) ;; 1 and 2 cannot split on the right side after 2nd exchange


