;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "CLOSER")

(include-book "coi/pattern-hint/pattern-hint" :dir :system)
(include-book "coi/types/types" :dir :system)
(include-book "math")

(defthm rfix-rfix
  (equal (rfix (rfix x))
         (rfix x)))

(in-theory (disable rfix))

(defun Dhyps (PL L R PR)
  (and
   (<= 0 (rfix L))
   (<= 0 (rfix R))
   (< (rfix PL) (rfix PR))))

(defun totalUAVS(L R)
  (declare (type t L R))
  (+ 1 (rfix L) (rfix R)))

(defun perimeterLength(PL PR)
  (declare (type t PL PR))
  (- (rfix PR) (rfix PL)))

(defun segmentLength(PL L R PR)
  (declare (type (satisfies natp) L R)
           (type t PL PR))
  (/ (perimeterLength PL PR) (totalUAVS L R)))

(defun density(PL L R PR)
  (/ (totalUAVS L R) (perimeterLength PL PR)))

(defun leftSegmentBoundary (PL L R PR)
  (declare (type (satisfies natp) L R)
           (type t PL PR))
  (+ (rfix PL) (* (rfix L) (segmentLength PL L R PR))))

(defun segmentMidpoint(PL L R PR)
  (declare (type (satisfies natp) L R)
           (type t PL PR))
  (+ (leftSegmentBoundary PL L R PR) (/ (segmentLength PL L R PR) 2)))

(defun perimeterMidpoint(PL PR)
  (+ (rfix PL) (/ (perimeterLength PL PR) 2)))

(defun xLR-< (PL L R PR)
  (< (segmentMidpoint PL L R PR) (perimeterMidpoint PL PR)))

(defun xRL-< (PR R L PL)
  (< (perimeterMidpoint PL PR) (segmentMidpoint PL L R PR)))

;; Can you prove that this depends only on R/L (?)

(include-book "arithmetic-5/top" :dir :system)

(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (defun diff (x y)
       (- (rfix y) (rfix x)))
     
     (defthm rationalp-diff
       (rationalp (diff x y)))
     
     (defthm step-1
       (equal (< (+ (* (RFIX L) (RFIX PR))
                    (* (RFIX PL) (RFIX R)))
                 (+ (* (RFIX L) (RFIX PL))
                    (* (RFIX PR) (RFIX R))))
              (< (* (RFIX L) (diff (RFIX PL) (RFIX PR)))
                 (* (RFIX R) (diff (RFIX PL) (RFIX PR))))))
          
     (in-theory (disable diff))
     
     (defthm really
       (implies
        (and
         (rationalp R)
         (rationalp L)
         (rationalp D)
         (< 0 D))
        (iff (< (* R D)
                (* L D))
             (< R L))))
     
     (defthm step-2
       (implies
        (< 0 (diff (RFIX PL) (RFIX PR)))
        (equal (< (+ (* (RFIX L) (RFIX PR))
                     (* (RFIX PL) (RFIX R)))
                  (+ (* (RFIX L) (RFIX PL))
                     (* (RFIX PR) (RFIX R))))
               (< (RFIX L) (RFIX R)))))
     
     ))
    
  (defthm reduce-<-1
    (implies
     (< (RFIX PL) (RFIX PR))
     (equal (< (+ (* (RFIX L) (RFIX PR))
                  (* (RFIX PL) (RFIX R)))
               (+ (* (RFIX L) (RFIX PL))
                  (* (RFIX PR) (RFIX R))))
            (< (RFIX L) (RFIX R))))
    :hints (("Goal" :in-theory '(diff rfix-rfix)
             :use step-2)))

  )
    
(defthm xLR-reduction
  (implies
   (dHyps PL L R PR)
   (iff (xLR-< PL L R PR)
        (< (rfix L) (rfix R))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (defun diff (x y)
       (- (rfix y) (rfix x)))
     
     (defthm rationalp-diff
       (rationalp (diff x y)))
     
     (defthm step-1
       (equal (< (+ (* (RFIX L) (RFIX PL))
                    (* (RFIX PR) (RFIX R)))
                 (+ (* (RFIX L) (RFIX PR))
                    (* (RFIX PL) (RFIX R))))
              (< (* (RFIX R) (diff (RFIX PL) (RFIX PR)))
                 (* (RFIX L) (diff (RFIX PL) (RFIX PR))))))
          
     (in-theory (disable diff))
     
     (defthm really
       (implies
        (and
         (rationalp R)
         (rationalp L)
         (rationalp D)
         (< 0 D))
        (iff (< (* R D)
                (* L D))
             (< R L))))
     
     (defthm step-2
       (implies
        (< 0 (diff (RFIX PL) (RFIX PR)))
        (equal (< (+ (* (RFIX L) (RFIX PL))
                    (* (RFIX PR) (RFIX R)))
                 (+ (* (RFIX L) (RFIX PR))
                    (* (RFIX PL) (RFIX R))))
               (< (RFIX R) (RFIX L)))))
     
     ))
    
  (defthm reduce-<-2
    (implies
     (< (RFIX PL) (RFIX PR))
     (equal (< (+ (* (RFIX L) (RFIX PL))
                  (* (RFIX PR) (RFIX R)))
               (+ (* (RFIX L) (RFIX PR))
                  (* (RFIX PL) (RFIX R))))
            (< (RFIX R) (RFIX L))))
    :hints (("Goal" :in-theory '(diff rfix-rfix)
             :use step-2)))
  
  )

(defthm xRL-<-reduction
  (implies
   (dHyps PL L R PR)
   (iff (xRL-< PR R L PL)
        (< (rfix R) (rfix L))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

;; So .. xRL-< and xLR-< reduce to predicates over L and R .. which
;; is consistent with our encapsulation above.
;;
;; So we can conclude that we cannot oscillate an arbirary number
;; of times between above and below the midpoint of the 
;; percieved perimeter.
;; 
;; Now I'm interested in a stronger linear-like properties which
;; we might get from notions of "density" and "equilibrium".
;;

(defthm positive-perimeter
  (implies
   (< (rfix PL0) (rfix PR0))
   (< 0 (PERIMETERLENGTH PL0 PR0)))
  :rule-classes :linear)

(set-non-linearp t)

(defthm density-is-segmentLength-inverse
  (equal (segmentLength PL L R PR)
         (/ (density PL L R PR))))

(defthm density-is-positive
  (implies
   (dHyps PL L R PR)
   (< 0 (density PL L R PR)))
  :rule-classes (:linear))

(defun dL (PL L m)
  (/ (+ (rfix L) 1/2) (- (rfix m) (rfix PL))))

(defun dLhyps (PL L m)
  (and
   (<= 0 (rfix L))
   (< (rfix PL) (rfix m))))

(defun dR (m R PR)
  (/ (+ (rfix R) 1/2) (- (rfix PR) (rfix m))))

(defun dRhyps (m R PR)
  (and
   (<= 0 (rfix R))
   (< (rfix m) (rfix PR))))

(defthm rationalp-segmentMidpoint
  (rationalp (segmentMidpoint PL L R PR))
  :rule-classes (:type-prescription
                 :rewrite
                 (:forward-chaining :trigger-terms ((segmentMidpoint PL L R PR)))))


(defthm segmentMidpoint-linear-bounds
  (implies
   (dHyps PL L R PR)
   (and
    (< (rfix PL) (segmentMidpoint PL L R PR))
    (< (segmentMidpoint PL L R PR) (rfix PR))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

(defthmd equality-double-containment
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (iff (equal x y)
        (and (not (< x y))
             (not (< y x))))))

(defthmd density-to-dL
  (implies
   (Dhyps PL L R PR)
   (equal (density PL L R PR)
          (dL PL L (segmentMidpoint PL L R PR))))
  :hints (("Goal" :in-theory (e/d (equality-double-containment
                                   remove-reciporicals-<)
                                  (segmentMidpoint)))
          (and stable-under-simplificationp
               '(:in-theory (enable remove-reciporicals-<)))
          ))

(defthmd density-to-dR
  (implies
   (Dhyps PL L R PR)
   (equal (density PL L R PR)
          (dR (segmentMidpoint PL L R PR) R PR)))
  :hints (("Goal" :in-theory (e/d (equality-double-containment
                                   remove-reciporicals-<)
                                  (segmentMidpoint)))
          (and stable-under-simplificationp
               '(:in-theory (enable remove-reciporicals-<)))
          ))


(encapsulate
    ()
  
  (local (in-theory (disable density dL dR segmentMidpoint)))
  
  (defthmd <-density-to-<-dL-dR
    (implies
     (and
      (Dhyps PL0 L0 R0 PR0)
      (Dhyps PL1 L1 R1 PR1))
     (iff (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
          (let ((m0 (segmentMidpoint PL0 L0 R0 PR0))
                (m1 (segmentMidpoint PL1 L1 R1 PR1)))
            (and (< (dL PL0 L0 m0)
                    (dL PL1 L1 m1))
                 (< (dR m0 R0 PR0)
                    (dR m1 R1 PR1))
                 (< (dL PL0 L0 m0)
                    (dR m1 R1 PR1))
                 (< (dR m0 R0 PR0)
                    (dL PL1 L1 m1))))))
    :hints ((pattern::hint
             (:and
              (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
              (not (< (dr m0 R0 PR0) (dl PL1 L1 m1))))
             :in-theory (enable density-to-dL density-to-dR)
             :restrict ((density-to-dR ((PL PL0) (L L0) (R R0) (PR PR0)))
                        (density-to-dL ((PL PL1) (L L1) (R R1) (PR PR1)))))
            (pattern::hint
             (:and
              (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
              (not (< (dl PL0 L0 m0) (dr m1 R1 PR1))))
             :in-theory (enable density-to-dL density-to-dR)
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))
            (pattern::hint
             (not (< (dl PL0 L0 m0) (dl PL1 L1 m1)))
             :in-theory (enable density-to-dL))
            (pattern::hint
             (not (< (dr m0 R0 PR0) (dr m1 R1 PR1)))
             :in-theory (enable density-to-dR))
            (pattern::hint
             (<= (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
             :in-theory (enable density-to-dR))
            ))

  (defthmd <=-density-to-<-dL-dR
    (implies
     (and
      (Dhyps PL0 L0 R0 PR0)
      (Dhyps PL1 L1 R1 PR1))
     (iff (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
          (let ((m0 (segmentMidpoint PL0 L0 R0 PR0))
                (m1 (segmentMidpoint PL1 L1 R1 PR1)))
            (or (< (dL PL0 L0 m0)
                   (dL PL1 L1 m1))
                (< (dR m0 R0 PR0)
                   (dR m1 R1 PR1))
                (< (dL PL0 L0 m0)
                   (dR m1 R1 PR1))
                (< (dR m0 R0 PR0)
                   (dL PL1 L1 m1))))))
    :hints ((pattern::hint
             (:and
              (<= (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0))
              (not (<= (dl PL1 L1 m1) (dr m0 R0 PR0))))
             :in-theory (enable density-to-dL density-to-dR)
             :restrict ((density-to-dR ((PL PL0) (L L0) (R R0) (PR PR0)))
                        (density-to-dL ((PL PL1) (L L1) (R R1) (PR PR1)))))
            (pattern::hint
             (:and
              (<= (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0))
              (not (<= (dr m1 R1 PR1) (dl PL0 L0 m0))))
             :in-theory (enable density-to-dL density-to-dR)
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))
            (pattern::hint
             (not (<= (dl PL1 L1 m1) (dl PL0 L0 m0)))
             :in-theory (enable density-to-dL))
            (pattern::hint
             (not (<= (dr m1 R1 PR1) (dr m0 R0 PR0)))
             :in-theory (enable density-to-dR))
            (pattern::hint
             (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
             :in-theory (enable density-to-dR))
            ))
  
  )
            
(defthmd dL-<-reduction
  (implies
   (and
    (dLhyps PL L m1)
    (dLhyps PL L m2))
   (iff (< (dL PL L m1) (dL PL L m2))
        (< (rfix m2) (rfix m1))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

;; (encapsulate
;;     (
;;      ((pair * *) => *)
;;      )
  
;;   (local (defun pair (x y)
;;            (declare (ignore x y))
;;            t))
  
;;   (defthm not-pair
;;     (implies (not (pair x y)) nil)
;;     :rule-classes ((:forward-chaining :trigger-terms ((pair x y)))))
  
;;   )

;; (defun meta-0 ()
;;   `(quote ,0))

;; (defun meta-1 ()
;;   `(quote ,1))

;; (defun meta-onep (x)
;;   (case-match x
;;     ((`quote v) (equal v 1))
;;     (& nil)))

;; (defun meta-zp (x)
;;   (case-match x
;;     ((`quote v) (equal v 0))
;;     (& nil)))

;; (defun meta-+ (x y)
;;   (if (meta-zp x) y
;;     (if (meta-zp y) x
;;       (if (and (quotep x) (quotep y))
;;           `(quote ,(+ (cadr x) (cadr y)))
;;         `(binary-+ ,x ,y)))))

;; (defun meta-- (x)
;;   (if (meta-zp x) x
;;     (if (quotep x) `(quote ,(- (cadr x)))
;;       `(unary-- ,x))))

;; (defun meta-* (x y)
;;   (if (meta-zp x) (meta-0)
;;     (if (meta-zp y) (meta-0)
;;       (if (meta-onep x) y
;;         (if (meta-onep y) x
;;           (if (and (quotep x) (quotep y))
;;               `(quote ,(* (cadr x) (cadr y)))
;;             `(binary-* ,x ,y)))))))

;; (defun linear-reduction (x y exp)
;;   (case-match exp
;;     (('binary-+ a b)
;;      (b* (((mv ac1 ac2 ac3) (linear-reduction x y a))
;;           ((mv bc1 bc2 bc3) (linear-reduction x y b)))
;;        (mv (meta-+ ac1 bc1)
;;            (meta-+ ac2 bc2)
;;            (meta-+ ac3 bc3))))
;;     (('unary-- a)
;;      (b* (((mv c1 c2 c3) (linear-reduction x y a)))
;;        (mv (meta-- c1) (meta-- c2) (meta-- c3))))
;;     (('binary-* a b)
;;      (b* (((mv ac1 ac2 ac3) (linear-reduction x y a))
;;           ((mv bc1 bc2 bc3) (linear-reduction x y b)))
;;        ;; 
;;        ;;          bc1 * x  +  bc2 * y  + bc3
;;        ;; ac1 * x      0           0     ac1*bc3
;;        ;; ac2 * y      0           0     ac2*bc3
;;        ;; ac3      ac3*bc1     ac3*bc2   ac3*bc3
;;        ;;
;;        (let ((c1 (meta-+ (meta-* ac3 bc1) (meta-* ac1 bc3)))
;;              (c2 (meta-+ (meta-* ac3 bc2) (meta-* ac2 bc3)))
;;              (c3 (meta-* ac3 bc3)))
;;          (mv c1 c2 c3))))
;;     (& (if (equal x exp) (mv (meta-1) (meta-0) (meta-0))
;;          (if (equal y exp) (mv (meta-0) (meta-1) (meta-0))
;;            (mv (meta-0) (meta-0) exp))))))
         
;; (defun linear-reduction-binder (x y exp)
;;   (b* (((mv c1 c2 c3) (linear-reduction x y exp)))
;;     (if (or (quotep c1) (quotep c2)) nil
;;       `((c1 . ,c1) (c2 . ,c2) (c3 . ,c3)))))

;; (defun contains-exp (x exp)
;;   (case-match exp
;;     (('binary-+ a b)
;;      (or (contains-exp x a)
;;          (contains-exp x b)))
;;     (('unary-- a)
;;      (contains-exp x a))
;;     (('binary-* a b)
;;      (or (contains-exp x a)
;;          (contains-exp x b)))
;;     (& (equal x exp))))

;; (defthmd linear-reduction-rule-1
;;   (implies
;;    (and
;;     ;;(in-conclusion-check (equal a b))
;;     (pair x y)
;;     (syntaxp (and (or (contains-exp x a) (contains-exp x b))
;;                   (or (contains-exp y a) (contains-exp y b))))
;;     (rationalp a)
;;     (rationalp b)
;;     (rationalp x)
;;     (rationalp y)
;;     (equal res (- a b))
;;     (bind-free (linear-reduction-binder x y res) (c1 c2 c3))
;;     (rationalp c1)
;;     (rationalp c2)
;;     (rationalp c3)
;;     (equal c1 (- c2))
;;     (equal res (+ (* c1 x) (* c2 y) c3))
;;     )
;;    (iff (equal a b)
;;         (if (equal c1 0) (equal c3 0)
;;           (equal (- x y) (- (/ c3 c1))))))
;;   :hints (("Goal" :in-theory (enable remove-reciporicals-=))))

;; (defthmd linear-reduction-rule-2
;;   (implies
;;    (and
;;     ;;(in-conclusion-check (equal a b))
;;     (pair x y)
;;     (syntaxp (and (or (contains-exp x a) (contains-exp x b))
;;                   (or (contains-exp y a) (contains-exp y b))))
;;     (rationalp a)
;;     (rationalp b)
;;     (rationalp x)
;;     (rationalp y)
;;     (equal res (- a b))
;;     (bind-free (linear-reduction-binder x y res) (c1 c2 c3))
;;     (rationalp c1)
;;     (rationalp c2)
;;     (rationalp c3)
;;     (equal c1 c2)
;;     (equal res (+ (* c1 x) (* c2 y) c3))
;;     )
;;    (iff (equal a b)
;;         (if (equal c1 0) (equal c3 0)
;;           (equal (+ x y) (- (/ c3 c1))))))
;;   :hints (("Goal" :in-theory (enable remove-reciporicals-=))))

(defun weighted-average (L0 m0 m1 R1)
  (let ((L0 (rfix L0))
        (m1 (rfix m1))
        (m0 (rfix m0))
        (R1 (rfix R1)))
    (/ (+ (* (+ L0 1/2) m0) (* (+ R1 1/2) m1))
       (+ L0 R1 1))))

(defthm linear-rfix
  (implies
   (rationalp x)
   (equal x (rfix x)))
  :rule-classes :linear)

(defthm weighted-average-bounds
  (implies
   (and
    (<= 0 (rfix L0))
    (<= 0 (rfix R1)))
   (and
    (implies
     (< (rfix m0) (rfix m1))
     (and
      (< (weighted-average L0 m0 m1 R1) (rfix m1))
      (< (rfix m0) (weighted-average L0 m0 m1 R1))))
    (implies
     (< (rfix m1) (rfix m0))
     (and
      (< (weighted-average L0 m0 m1 R1) (rfix m0))
      (< (rfix m1) (weighted-average L0 m0 m1 R1))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

(defthmd segmentMidpoint-is-weighted-average
  (implies
   (dhyps PL L R PR)
   (equal (segmentMidpoint PL L R PR)
          (weighted-average L PR PL R)))
  :hints (("Goal" :in-theory (enable remove-reciporicals-=))))

(defthmd dL=dR-reduction
  (implies
   (and
    (dLhyps PL L m1)
    (dRhyps m2 R PR)
    (< (rfix PL) (rfix PR)))
   (iff (equal (dL PL L m1) (dR m2 R PR))
        (equal (segmentMidpoint PL L R PR)
               (weighted-average L m2 m1 R))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-=))))

;; I think we can also say that the subsequent density is some sort
;; of weighted average ..

(defthmd dL-<-dR-reduction
  (implies
   (and
    (dLhyps PL L m1)
    (dRhyps m2 R PR)
    (< (rfix PL) (rfix PR)))
   (iff (< (dL PL L m1) (dR m2 R PR))
        (< (segmentMidpoint PL L R PR)
           (weighted-average L m2 m1 R))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

(defthmd dL->-dR-reduction
  (implies
   (and
    (dLhyps PL L m1)
    (dRhyps m2 R PR)
    (< (rfix PL) (rfix PR)))
   (iff (> (dL PL L m1) (dR m2 R PR))
        (> (segmentMidpoint PL L R PR)
           (weighted-average L m2 m1 R))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

(defthmd dR-<-reduction
  (implies
   (and
    (dRhyps m1 R PR)
    (dRhyps m2 R PR))
   (iff (< (dR m1 R PR) (dR m2 R PR))
        (< (rfix m1) (rfix m2))))
  :hints (("Goal" :in-theory (enable remove-reciporicals-<))))

;; If the new midoint it to the left of both of the
;; previous midpoints, the density of the left uav
;; was greater.

(encapsulate
 ()

 (local (in-theory (disable segmentMidpoint density dR dL)))

 (defthmd below-both-is-below-average
   (implies
    (and
     (dhyps PL0 L0 R0 PR0)
     (dhyps PL1 L1 R1 PR1)
     (dhyps PL0 L0 R1 PR1)
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL1 L1 R1 PR1)))
    (and
     (< (segmentMidpoint PL0 L0 R1 PR1)
        (weighted-average L0 (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0) R1))
     (< (segmentMidpoint PL0 L0 R1 PR1)
        (weighted-average L1 (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1) R0))))
   :hints (("Goal" :in-theory (enable remove-reciporicals-<))))
 
 (local (in-theory (disable weighted-average)))
 
 (defthmd below-both-implies-density-ordering
   (implies
    (and
     (dhyps PL0 L0 R0 PR0)
     (dhyps PL1 L1 R1 PR1)
     (dhyps PL0 L0 R1 PR1)
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL1 L1 R1 PR1)))
    (and
     (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
     (< (density PL0 L0 R1 PR1) (density PL1 L1 R1 PR1))
     (< (density PL0 L0 R0 PR0) (density PL0 L0 R1 PR1))
     ))
   :hints (("Goal" :use below-both-is-below-average)
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL0 L0 R0 PR0)
                     (DENSITY PL1 L1 R1 PR1))))
            :in-theory (enable density-to-dR
                               density-to-dL
                               dL-<-dR-reduction)
            :restrict ((density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))
                       (density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))))
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL0 L0 R0 PR0)
                     (DENSITY PL0 L0 R1 PR1))))
            :in-theory (enable density-to-dL
                               dL-<-reduction
                               ))
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL0 L0 R1 PR1)
                     (DENSITY PL1 L1 R1 PR1))))
            :in-theory (enable density-to-dR
                               dR-<-reduction
                               ))
           ))
 )

(encapsulate
 ()

 (local (in-theory (disable segmentMidpoint density dR dL)))

 (defthmd above-both-is-above-average
   (implies
    (and
     (dhyps PL0 L0 R0 PR0)
     (dhyps PL1 L1 R1 PR1)
     (dhyps PL0 L0 R1 PR1)
     (< (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL0 L0 R1 PR1))
     (< (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R1 PR1)))
    (and
     (< (weighted-average L0 (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0) R1)
        (segmentMidpoint PL0 L0 R1 PR1))
     (< (weighted-average L1 (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1) R0)
        (segmentMidpoint PL0 L0 R1 PR1))))
   :hints (("Goal" :in-theory (enable remove-reciporicals-<))))
 
 (local (in-theory (disable weighted-average)))
 
 (defthmd above-both-implies-density-ordering
   (implies
    (and
     (dhyps PL0 L0 R0 PR0)
     (dhyps PL1 L1 R1 PR1)
     (dhyps PL0 L0 R1 PR1)
     (< (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL0 L0 R1 PR1))
     (< (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R1 PR1)))
    (and
     (< (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0))
     (< (density PL1 L1 R1 PR1) (density PL0 L0 R1 PR1))
     (< (density PL0 L0 R1 PR1) (density PL0 L0 R0 PR0))
     ))
   :hints (("Goal" :use above-both-is-above-average)
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL1 L1 R1 PR1)
                     (DENSITY PL0 L0 R0 PR0)
                     )))
            :in-theory (enable density-to-dR
                               density-to-dL
                               dL->-dR-reduction)
            :restrict ((density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))
                       (density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))))
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL0 L0 R1 PR1)
                     (DENSITY PL0 L0 R0 PR0))))
            :in-theory (enable density-to-dL
                               dL-<-reduction
                               ))
           (pattern::hint
            (:and
             (:literally PL0 L0 R0 PR0 PL1 L1 R1 PR1)
             (not (< (DENSITY PL1 L1 R1 PR1)
                     (DENSITY PL0 L0 R1 PR1))))
            :in-theory (enable density-to-dR
                               dR-<-reduction
                               ))
           ))
 )



(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthmd segmentMidpoint-lt-reduction
       (implies
        (and
         (dhyps PL L R PR)
         (rationalp m))
        (iff (< (segmentMidpoint PL L R PR) m)
             (< (+ (RFIX PL) (RFIX PR) (* 2 (RFIX L) (RFIX PR)) (* 2 (RFIX PL) (RFIX R)))
                (* m (* 2 (+ 1 (RFIX L) (RFIX R)))))))
       :hints (("Goal" :in-theory (e/d (remove-reciporicals-< segmentMidpoint-is-weighted-average)
                                       (segmentMidpoint)))))
     
     (defthmd segmentMidpoint-gt-reduction
       (implies
        (and
         (dhyps PL L R PR)
         (rationalp m))
        (iff (< m (segmentMidpoint PL L R PR))
             (< (* m (* 2 (+ 1 (RFIX L) (RFIX R))))
                (+ (RFIX PL) (RFIX PR) (* 2 (RFIX L) (RFIX PR)) (* 2 (RFIX PL) (RFIX R))))))
       :hints (("Goal" :in-theory (e/d (remove-reciporicals-< segmentMidpoint-is-weighted-average)
                                       (segmentMidpoint)))))
     ))

  (encapsulate
      ()
    (local (in-theory (enable segmentMidpoint-lt-reduction segmentMidpoint-gt-reduction)))
    
    (defthmd equal-density-implies-segmentMidpoint
      (implies
       (dhyps PL L R PR)
       (iff (equal (dL PL L m) (dR m R PR))
            (equal (rfix m) (segmentMidpoint PL L R PR))))
      :hints (("Goal" :in-theory (e/d (equality-double-containment)
                                      (segmentMidpoint)))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (remove-reciporicals-<)
                                     (segmentMidpoint))))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (remove-reciporicals-< equality-double-containment)
                                     ())))
              (and stable-under-simplificationp
                   '(:cases ((equal (rfix PL) 0))))
              (and stable-under-simplificationp
                   '(:cases ((equal (rfix PR) 0))))
              ))
    ))

(encapsulate
    ()

  (local (in-theory (disable dl dr density segmentMidpoint)))
  
  (defthmd greater-density-has-greater-sway-<
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (< (rfix PL0) (rfix PR1))
      (< (rfix PL1) (rfix PR0))
      (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
      (<= (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
      ;;
      ;; U1 is able to bully U0 from the right
      ;;
      ;; U1:[    | R1 ]
      ;;    U0:[ L0  |    ]
      ;;
      )
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0)))
    :hints (("Goal" :in-theory (enable density-to-dL
                                       density-to-dR
                                       dL-<-dR-reduction
                                       remove-reciporicals-<
                                       )
             :restrict ((density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))
                        (density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))))))
                   
  (defthmd greater-density-has-greater-sway->
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (< (rfix PL0) (rfix PR1))
      (< (rfix PL1) (rfix PR0))
      (< (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0) )
      (<= (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
      ;;
      ;; U0 is able to bully U1 from the left
      ;;
      ;;    U0:[ L0  |    ]
      ;; U1:[    | R1 ]
      ;;
      )
     (< (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R1 PR1) ))
    :hints (("Goal" :in-theory (enable density-to-dL
                                       density-to-dR
                                       dL->-dR-reduction
                                       remove-reciporicals-<
                                       )
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))))

  (defthmd equal-density-equal-midpoint
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (< (rfix PL0) (rfix PR1))
      (< (rfix PL1) (rfix PR0))
      (equal (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
      (equal (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
      )
     (equal (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0)))
    :hints (("Goal" :in-theory (enable density-to-dR density-to-dL dL=dR-reduction)
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))))
  
  (defthmd equal-density-<-midpoint
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (< (rfix PL0) (rfix PR1))
      (< (rfix PL1) (rfix PR0))
      (equal (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
      (< (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
      )
     (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0)))
    :hints (("Goal" :in-theory (e/d (density-to-dR density-to-dL dL=dR-reduction)
                                    (WEIGHTED-AVERAGE))
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))))
  
  (defthmd equal-density->-midpoint
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (< (rfix PL0) (rfix PR1))
      (< (rfix PL1) (rfix PR0))
      (equal (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
      (> (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
      )
     (> (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0)))
    :hints (("Goal" :in-theory (e/d (density-to-dR density-to-dL dL=dR-reduction)
                                    (WEIGHTED-AVERAGE))
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))))

  )
  
;; I think it is density that we want to reason about based on changes
;; to the midpoint.

(defthmd new-density-as-weighted-average
  (implies
   (and
    (dhyps PL0 L0 R0 PR0)
    (dhyps PL1 L1 R1 PR1)
    (dhyps PL0 L0 R1 PR1))
   (equal (density PL0 L0 R1 PR1)
          (/ (+ (* (- (segmentMidpoint PL0 L0 R0 PR0) (rfix PL0)) (density PL0 L0 R0 PR0))
                (* (- (rfix PR1) (segmentMidpoint PL1 L1 R1 PR1)) (density PL1 L1 R1 PR1)))
             (- (rfix PR1) (rfix PL0)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (remove-reciporicals-=
                            segmentMidpoint-is-weighted-average)
                           (density)))
          (and stable-under-simplificationp
               '(:in-theory (enable remove-reciporicals-=)))))

;;
;; DAG: There is no "nice" formalization of the new midpoint w/to the old
;; midpoints.  The best formalization is simply as a weighted average
;; of the new endpoints.  (Though perhaps we could express *that* in terms of
;; density?)
;;
;; The specific property we want is that, if the new midpoint is not between
;; the existing midpoints, one of the UAVs has a higher density.
;;
;; More specifically, if the new midpoint is not the weighted average of the existing
;; midpoints, one of the UAVs has higher density.  Note that the weighted average
;; must be *between* the existing midpoints.  So, certainly, if the new midpoint is
;; not between the existing midpoints, one of the UAVs has higher density.
;;
;; DAG : I think this is currently our most important theorem ..
;; 

(encapsulate
    ()

  (in-theory (disable weighted-average  segmentMidpoint density dL dR))

  (defthmd density-average-relation-<
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (dhyps PL0 L0 R1 PR1)
      (< (segmentMidpoint PL0 L0 R1 PR1)
         (weighted-average L0 (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0) R1)))
     (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1)))
    :hints (("Goal" :in-theory (enable density-to-dR
                                       density-to-dL
                                       dL-<-dR-reduction)
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))
            ))
  
  (defthmd density-average-relation->
    (implies
     (and
      (dhyps PL0 L0 R0 PR0)
      (dhyps PL1 L1 R1 PR1)
      (dhyps PL0 L0 R1 PR1)
      (> (segmentMidpoint PL0 L0 R1 PR1)
         (weighted-average L0 (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0) R1)))
     (> (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1)))
    :hints (("Goal" :in-theory (enable density-to-dR
                                       density-to-dL
                                       dL->-dR-reduction)
             :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                        (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))
            ))

  )

;;
;; Frankly, it may be enough to talk about the weighted average.  The weighted average
;; is bound, and deviations from it can be bought only with density.
;;
;;           y0     y1          x0      x1      x2
;;           |      |           |       |       |
;;           v      v           v       v       v
;;                  
;;                            E0A     E1B      E2C
;;                              \       \       \
;; t0                         U0/\UA  U1/\UB  U2/\UC
;;                             /  \    /  \    /  \
;;                                 \  /    \  /    
;;                                  \/      \/      
;; t1                            EA1/    EB2/        
;;                                 /       /
;;                                /       /
;;                               /       /
;;                              /       /
;;                             /       /
;;                            /       /
;;                           /       /
;;                          /       /
;;                         /       /
;;                        /       /
;;                       /       /
;;                      /       /
;;                     /       /
;;                    /       /
;;                   /       /
;;                  /       /
;;                 /       /
;;                /       /
;;               /       /
;;              /       /
;;             /       /
;;            /       /
;;           /       /
;; t2     UA/\U1  UB/\U2             
;;            \    /             
;;             \  /             
;;              \/             
;;               \
;;
;;           ^      ^           ^       ^       ^
;;           |      |           |       |       |
;;           y0     y1          x0      x1      x2

;; t0:
;;     m(U0) < x0 < m(UA)   .. and they are equidistant from x0.
;;     m(U1) < x1 < m(UB)   ..
;;     m(U2) < x2 < m(UC)   ..
;;
;; t1:
;;     m(UA1) < y0 < x0 < m(UA)    ;; We move UA's midpoint from greater than x0 to less than y0.
;;     m(UB2) < y1 < x1 < m(UB)    ;; We move UB's midpoint from greater than x1 to less than y1.
;;
;; t2:
;;     m(UB2.L) < m(U1B.R)  ;; Can we move UB2.L's midpoint from less than y1 to greater than y1 ??

;; There are two ways to do this .. either d(UA1.R) > d(UB2.L) or m(UB2.L) < m(UA1.R)


;; So:
;; If d(E1B) <= d(E0A), then m(U1) < y0 and d(U1) < 1/(x0-y0)
;; If d(E2C) <= d(E1B), then m(U2) < y1 and d(U2) < 1/(x1-y1)
;;
;; The density is the reciporical of the segment length.
;; So, a large density means small segments and a small denstity means large segments.
;; 
;; The midpoints will be equidistant from the branch points.
;;
#|
dag

;; yeah .. that isn't it.  I think we need to consider both density and weight ..
;; as somewhat independent variables.  (d,w)  For any weight we can have a density
;; and for any density we can have a weight.  And we can set up ratios of these
;; two .. but at some point we must pay the piper.

(in-theory (disable DENSITY-IS-SEGMENT-INVERSE segment segmentMidpoint density dL dR))

(defthm dominators-must-have-higher-desnity
  (implies
   (and
    (dhyps PL1 L1 R1 PR1)
    (dhyps PL0 L0 R0 PR0)
    (dhyps PL0 L0 R1 PR1)
    (<= (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0)))
   (<= (WEIGHTED-AVERAGE L0 (SEGMENTMIDPOINT PL1 L1 R1 PR1)
                         (SEGMENTMIDPOINT PL0 L0 R0 PR0)
                         R1)
       (segmentMidpoint PL0 L0 R1 PR1)))
  :hints (("Goal" :in-theory (enable density-to-dR density-to-dL dL-<-dR-reduction)
           :restrict ((density-to-dR ((PL PL1) (L L1) (R R1) (PR PR1)))
                      (density-to-dL ((PL PL0) (L L0) (R R0) (PR PR0)))))))



|#

;; So .. while segmentMidpoint, as define above, has some nice properties, it
;; isn't an accurate model of

;; DAG: Note that we see this quite a bit .. fixing functions mess up
;; the linear/forward chaining rules.  Well, at least in this case, we
;; can define linear rules that, for example, reduce (rfix x) to x
;; when x is rationalp.

#+joe
(defthm typed-weighted-average-bounds
  (implies
   (and
    (<= 0 (rfix L0))
    (<= 0 (rfix R1))
    (rationalp m0)
    (rationalp m1))
   (and
    (implies
     (< m0 m1)
     (and
      (< (weighted-average L0 m0 m1 R1) m1)
      (< m0 (weighted-average L0 m0 m1 R1))))
    (implies
     (< m1 m0)
     (and
      (< (weighted-average L0 m0 m1 R1) m0)
      (< m1 (weighted-average L0 m0 m1 R1))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable weighted-average-bounds)
           :use weighted-average-bounds)))

(defthm weighted-average-same
  (implies
   (and
    (<= 0 (rfix L0))
    (<= 0 (rfix R1)))
   (equal (WEIGHTED-AVERAGE L0 W W R1)
          (rfix w)))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE))))

;;
;; I think these theorems reflect the ordering property we require to
;; prove the impossibility of arbitrary oscillation.
;;

(defthmd new-midpoint-to-the-left-of-both-implies-greater-right-density
  (implies
   (and
    (dhyps PL0 L0 R0 PR0)
    (dhyps PL1 L1 R1 PR1)
    
    (< (rfix PL0) (rfix PR1))
    (< (rfix PL1) (rfix PR0))
    
    (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 L0 R0 PR0))
    (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL1 L1 R1 PR1))
    
    )
   (< (density PL0 L0 R0 PR0) (density PL1 L1 R1 PR1))
   )
  :hints (("Goal" :use density-average-relation-<)
          (and stable-under-simplificationp
               '(:cases ((not (equal (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1))))))
          (and stable-under-simplificationp
               '(:cases ((not (< (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1))))))
          ))

(defthmd new-midpoint-to-the-right-of-both-implies-greater-left-density
  (implies
   (and
    (dhyps PL0 L0 R0 PR0)
    (dhyps PL1 L1 R1 PR1)
    
    (< (rfix PL0) (rfix PR1))
    (< (rfix PL1) (rfix PR0))
    
    (< (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL0 L0 R1 PR1))
    (< (segmentMidpoint PL1 L1 R1 PR1) (segmentMidpoint PL0 L0 R1 PR1))
    
    )
   (< (density PL1 L1 R1 PR1) (density PL0 L0 R0 PR0)))
  :hints (("Goal" :use density-average-relation->)
          (and stable-under-simplificationp
               '(:cases ((not (equal (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1))))))
          (and stable-under-simplificationp
               '(:cases ((not (< (segmentMidpoint PL0 L0 R0 PR0) (segmentMidpoint PL1 L1 R1 PR1))))))
          ))

(defthmd min-split-is-between-R+-and-L+
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (rationalp R1)
    (rationalp L0))
   (and (< (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 L0 R1 PR1))
        (< (segmentMidpoint PL0 L0 R1 PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1))))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

(defthmd split-is-below-min-split
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (< R1 L0)
    (rationalp R1)
    (rationalp L0))
   (< (/ (+ (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2)
      (segmentMidpoint PL0 L0 R1 PR1)))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

(defthmd split-is-above-min-split
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (< L0 R1)
    (rationalp R1)
    (rationalp L0))
   (< (segmentMidpoint PL0 L0 R1 PR1)
      (/ (+ (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2)))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))


(defthmd max-split-is-between-R+-and-L+
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (rationalp R1)
    (rationalp L0))
   (and (< (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) (+ R1 1) PR1))
        (< (segmentMidpoint PL0 (+ L0 1) (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1))))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

(defthmd split-is-above-max-split
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (< R1 L0)
    (rationalp R1)
    (rationalp L0))
   (< (segmentMidpoint PL0 (+ L0 1) (+ R1 1) PR1)
      (/ (+ (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2)))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

(defthmd split-is-below-max-split
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (< L0 R1)
    (rationalp R1)
    (rationalp L0))
   (< (/ (+ (segmentMidpoint PL0 L0 (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2)
      (segmentMidpoint PL0 (+ L0 1) (+ R1 1) PR1)))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

(defthmd split-is-between-min-split-and-max-split
  (implies
   (and
    (dhyps PL0 L0 R1 PR1)
    (rationalp R1)
    (rationalp L0))
   (and (<= (min (segmentMidpoint  PL0 (+ L0 1) (+ R1 1) PR1) (segmentMidpoint PL0    L0    R1 PR1))
            (/ (+ (segmentMidpoint PL0    L0    (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2))
        (<= (/ (+ (segmentMidpoint PL0    L0    (+ R1 1) PR1) (segmentMidpoint PL0 (+ L0 1) R1 PR1)) 2)
            (max (segmentMidpoint  PL0 (+ L0 1) (+ R1 1) PR1) (segmentMidpoint PL0    L0    R1 PR1)))))
  :hints (("Goal" :in-theory (enable WEIGHTED-AVERAGE
                                     remove-reciporicals-<
                                     segmentMidpoint-is-weighted-average))))

;; Technically "split point" is just the midpoint between two
;; segments.  In this model, we give it the L and R parameters
;; as seen by those two segments.
(defun splitPoint (PL L R PR)
  (let ((L (rfix L))
        (R (rfix R)))
    (/ (+ (segmentMidpoint PL L (1+ R) PR) (segmentMidpoint PL (1+ L) R PR)) 2)))


(in-theory (disable acl2::rational-equiv))

(defcong acl2::rational-equiv equal (density a b c d) 1
  :hints (("Goal" :in-theory (enable density))))

(defcong acl2::rational-equiv equal (SEGMENTMIDPOINT A B C D) 1
  :hints (("Goal" :in-theory (enable segmentmidpoint))))

(defcong acl2::rational-equiv equal (density a b c d) 2
  :hints (("Goal" :in-theory (enable density))))

(defcong acl2::rational-equiv equal (SEGMENTMIDPOINT A B C D) 2
  :hints (("Goal" :in-theory (enable segmentmidpoint))))

(defcong acl2::rational-equiv equal (density a b c d) 3
  :hints (("Goal" :in-theory (enable density))))

(defcong acl2::rational-equiv equal (SEGMENTMIDPOINT A B C D) 3
  :hints (("Goal" :in-theory (enable segmentmidpoint))))

(defcong acl2::rational-equiv equal (density a b c d) 4
  :hints (("Goal" :in-theory (enable density))))

(defcong acl2::rational-equiv equal (SEGMENTMIDPOINT A B C D) 4
  :hints (("Goal" :in-theory (enable segmentmidpoint))))


(defcong acl2::rational-equiv equal (segmentLength a b c d) 1)

(defcong acl2::rational-equiv equal (segmentLength a b c d) 2)

(defcong acl2::rational-equiv equal (segmentLength a b c d) 3)

(defcong acl2::rational-equiv equal (segmentLength a b c d) 4)

(in-theory (disable segmentLength DENSITY-IS-SEGMENTlength-INVERSE))

(defthmd segmentLength-normalization
  (implies
   (and
    (integerp P)
    (rationalp L)
    (rationalp R))
   (equal (segmentLength PL (+ L P) R PR)
          (segmentLength PL L (+ P R) PR)))
  :hints (("Goal" :in-theory (enable segmentLength))))

(defthmd segmentmidpoint-normalization
  (implies
   (and
    (integerp P)
    (rationalp L)
    (rationalp R))
   (equal (segmentmidpoint PL (+ P L) R PR)
          (+ (segmentmidpoint PL L (+ R P) PR) (* P (segmentLength PL L (+ R P) PR)))))
  :hints (("Goal" :in-theory (enable segmentLength segmentmidpoint))))

(defthm non-negative-segment-length
  (implies
   (dhyps PL0 L0 R0 PR0)
   (< 0 (SEGMENTLENGTH PL0 L0 R0 PR0)))
  :hints (("Goal" :in-theory (enable segmentlength)))
  :rule-classes :linear)


;; (encapsulate
;;     (
;;      ((wrap *) => *)
;;      )
;;   (local
;;    (encapsulate
;;        ()
;;      (defun wrap (x) (declare (ignore x)) t)
;;      ))
;;   (defthm wrap-true
;;     (implies
;;      (not (wrap x)) nil)
;;     :rule-classes (:forward-chaining))
;;   )
;;
;;
;; Right .. so the following theorem is falsifiable.  Under sufficiently sparse
;; configurations, we can violate this condition.
;;
;; (defthm golden
;;   (implies
;;    (and
;;     (dhyps PL0 L0 R0 PR0)
;;     (dhyps PL1 L1 R1 PR1)
;;     (dhyps PL0 L0 R1 PR1)
;;     (rationalp L0)
;;     (rationalp R1)
;;     (< (splitPoint PL0 (1- L0) R0 PR0)
;;        (splitPoint PL1 L1 (1- R1) PR1))
;;     (< (splitPoint PL0 L0 R1 PR1)
;;        (splitPoint PL0 (1- L0) R0 PR0))
;;     )
;;    (< (density PL0 L0 R0 PR0)
;;       (density PL1 L1 R1 PR1)))
;;   :hints (("Goal" :cases ((< (SEGMENTMIDPOINT PL0 L0 (+ 1 R1) PR1)
;;                              (SEGMENTMIDPOINT PL0 L0 R0 PR0))))
;;           (and stable-under-simplificationp
;;                `(:cases ((wrap (SEGMENTMIDPOINT PL0 L0 (+ 1 R1) PR1)))))
;;           (and stable-under-simplificationp
;;                `(:cases ((wrap (SEGMENTMIDPOINT PL0 (+ 1 L0) R1 PR1)))))
;;           ))


;;

