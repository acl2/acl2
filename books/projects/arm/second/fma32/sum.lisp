;; Cuong Chau <cuong.chau@arm.com>

;; February 2021

;; The events in this book are derived from the hand proofs developed by David
;; Russinoff <david.russinoff@arm.com>.

(in-package "RTL")

(include-book "addends")
(include-book "hc52")

(local (arith-5-for-rtl))

;; ======================================================================

(defthmd gout-add-rel
  (equal (equal (bitn (gout) 51) 1)
         (<= *2^52*
             (+ (add1) (add2))))
  :hints (("Goal"
           :use (:instance hc52-lemma-4
                           (x (add1))
                           (y (add2)))
           :in-theory (enable gout gin pin))))

(defthmd pout-add-rel
  (equal (equal (bitn (pout) 51) 1)
         (equal (+ (add1) (add2))
                (1- *2^52*)))
  :hints (("Goal"
           :use (:instance hc52-lemma-4
                           (x (add1))
                           (y (add2)))
           :in-theory (enable pout gin pin))))

(defthmd sum-rewrite
  (equal (sum)
         (if (equal (bitn (gout) 51) 0)
             (bits (lognot (+ (add1) (add2) (inc)))
                   50 0)
           (bits (+ (add1) (add2) (inc))
                 50 0)))
  :hints (("Goal"
           :use ((:instance hc52-lemma-2
                            (x (add1))
                            (y (add2)))
                 (:instance hc52-lemma-3
                            (x (add1))
                            (y (add2))))
           :in-theory (enable sum
                              gout
                              inc
                              gin
                              pin
                              bits-logior
                              bits-lognot
                              bits-logxor
                              computesum))))

(defthm fi-=-0
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 0))
           (equal (fi) 0))
  :hints (("Goal"
           :use pout-add-rel
           :in-theory (enable severe
                              fi
                              pout
                              gin
                              pin
                              inx-0
                              add1-rewrite
                              add2-rewrite
                              computesum))))

(defthm s-tilde-=-0
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 0))
           (equal (s-tilde) 0))
  :hints (("Goal" :use abs-s-tilde-rewrite-1)))

(defthm s-=-0
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 0))
           (equal (s) 0))
  :hints (("Goal" :use s-s-tilde-rel-1)))

(defthm fi-bounds-severe
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 1))
           (and (< 0 (fi))
                (< (fi) 1)))
  :hints (("Goal"
           :use (pout-add-rel
                 inx-0)
           :in-theory (enable severe
                              fi
                              pout
                              gin
                              pin
                              add1-rewrite
                              add2-rewrite
                              computesum)))
  :rule-classes :linear)

(defthm nonzero-s-tilde-when-inx-is-1
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 1))
           (not (equal (s-tilde) 0)))
  :hints (("Goal" :use abs-s-tilde-rewrite-1)))

(defthm nonzero-s-when-inx-is-1
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 1))
           (not (equal (s) 0)))
  :hints (("Goal" :use s-s-tilde-rel-1)))

(defthmd-nl s-tilde-ressign-1-rel-severe
  (implies (and (numeric-a-b-p)
                (equal (severe) 1)
                (equal (inx) 1))
           (equal (< 0 (s-tilde))
                  (equal (ressign-1) 0)))
  :hints (("Goal"
           :use (s-tilde-signlarger-rel-3
                 gout-add-rel
                 pout-add-rel
                 inx-0)
           :in-theory (enable severe
                              ressign-1
                              gout
                              pout
                              gin
                              pin
                              add1-rewrite
                              add2-rewrite
                              signlarger
                              computesum))))

(defthm-nl fi-lower-bound-non-severe
  (implies (and (numeric-a-b-p)
                (equal (severe) 0)
                (not-both-p&c-zeros-p))
           (< 0 (fi)))
  :hints (("Goal"
           :use pout-add-rel
           :in-theory (enable severe
                              not-both-p&c-zeros-p
                              fi
                              pout
                              gin
                              pin
                              mlarge
                              msmall
                              add1-rewrite
                              add2-rewrite
                              computesum)))
  :rule-classes :linear)

(defthmd sum-fi-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (equal (sum) (fl (fi))))
  :hints (("Goal"
           :use (gout-add-rel
                 pout-add-rel
                 add1+add2-upper-bound
                 add1-add2-lower-bound
                 add1-add2-upper-bound)
           :in-theory (e/d (acl2::scatter-exponents-theory
                            severe
                            sum-rewrite
                            fi
                            gout
                            pout
                            gin
                            pin
                            inc
                            inx-0
                            add1-rewrite
                            add2-rewrite
                            bits-lognot
                            bits-tail-sub-1
                            bits-tail-sub-2
                            computesum)
                           (acl2::gather-exponents-theory
                            add1+add2-upper-bound
                            add1-add2-lower-bound
                            add1-add2-upper-bound)))))

(defthmd s-tilde-ressign-1-rel-non-severe
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0))
           (equal (< 0 (s-tilde))
                  (equal (ressign-1) 0)))
  :hints (("Goal"
           :use (s-tilde-signlarger-rel-1
                 s-tilde-signlarger-rel-2
                 s-tilde-signlarger-rel-3
                 gout-add-rel
                 pout-add-rel)
           :in-theory (e/d (acl2::scatter-exponents-theory
                            severe
                            ressign-1
                            gout
                            pout
                            gin
                            pin
                            add1-rewrite
                            add2-rewrite
                            signlarger
                            computesum)
                           (acl2::gather-exponents-theory)))))

(defthm rationalp-fi
  (rationalp (fi))
  :hints (("Goal" :in-theory (enable fi)))
  :rule-classes :type-prescription)

(bvecthm bvecp10-scale
  (bvecp (scale) 10)
  :hints (("Goal" :in-theory (enable bvecp scale scale128))))

(defthmd sumexp-rewrite
  (implies (numeric-a-b-p)
           (equal (sumexp)
                  (+ (si (scale) 10)
                     (elarge)
                     794)))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (e/d (sumexp
                            elarge
                            si-bounds
                            bvecp)
                           (pexp-bounds)))))

(defthmd abs-s-tilde-rewrite-2
  (implies (numeric-a-b-p)
           (equal (abs (s-tilde))
                  (* (fi)
                     (expt 2 (- (sumexp) 1098)))))
  :hints (("Goal"
           :in-theory (e/d (abs-s-tilde-rewrite-1
                            sumexp-rewrite)
                           (abs)))))

(defthm s-tilde-sum-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (and (<= (* (sum)
                       (expt 2 (- (sumexp) 1098)))
                    (abs (s-tilde)))
                (< (abs (s-tilde))
                   (* (1+ (sum))
                      (expt 2 (- (sumexp) 1098))))))
  :hints (("Goal"
           :in-theory (e/d (sum-fi-rel
                            abs-s-tilde-rewrite-2)
                           (abs))))
  :rule-classes :linear)

(defthmd s-tilde-sum-inx-rel
  (implies (and (numeric-a-b-p)
                (equal (severe) 0))
           (equal (equal (inx) 0)
                  (equal (* (sum)
                            (expt 2 (- (sumexp) 1098)))
                         (abs (s-tilde)))))
  :hints (("Goal"
           :in-theory (e/d (inx-fi-rel
                            sum-fi-rel
                            abs-s-tilde-rewrite-2)
                           (abs)))))

(bitthm bitp-inx
  (bitp (inx))
  :hints (("Goal" :in-theory (enable inx computeaddends))))

(local
 (defthm aux-1
   (implies (and (< x y)
                 (<= y z))
            (< x z))
   :rule-classes nil))

(local
 (defthmd aux-2
   (implies (and (integerp x)
                 (< 0 x))
            (<= 1 x))))

(encapsulate
  ()

  (local
   (defthm-nl++ scale-elarge-inx-rel-aux
     (implies (and (<= 8388608 (pmant))
                   (<= (+ 27 (cexp)) (pexp)))
              (and (< (* (cmant) (expt 2 (cexp)))
                      (* (pmant) (expt 2 (pexp))))
                   (< (+ (expt 2 (pexp))
                         (* 4 (cmant) (expt 2 (cexp))))
                      (* 4 (pmant) (expt 2 (pexp))))))
     :hints (("Goal" :use (:instance aux-1
                                     (x (* (cmant) (expt 2 (cexp))))
                                     (y (expt 2 (+ 50 (cexp))))
                                     (z (* (pmant) (expt 2 (pexp)))))))
     :rule-classes :linear))

  (defthmd-nl++ scale-elarge-inx-rel
    (implies (and (numeric-a-b-p)
                  (or (< 15 (si (scale) 10))
                      (< 128 (elarge)))
                  (equal (severe) 1))
             (equal (inx) 0))
    :hints (("Goal"
             :use (fi-bounds-severe
                   scale-prop
                   pexp-bounds
                   pexp-=-4
                   cexp-=-128
                   ediff-lower-bound-when-clarger-is-0
                   ediff-lower-bound-when-clarger-is-1)
             :in-theory (e/d (mlarge
                              msmall
                              ediff
                              elarge
                              esmall
                              clarger
                              fi)
                             (fi-bounds-severe
                              scale-prop
                              pexp-bounds
                              pexp-=-4
                              cexp-=-128
                              ediff-lower-bound-when-clarger-is-0
                              ediff-lower-bound-when-clarger-is-1)))))

  (local
   (defthm-nl++ sum-lower-bound-non-severe-aux-1
     (implies (and (<= 8388608 (pmant))
                   (<= (+ 26 (cexp)) (pexp)))
              (and (< (* (cmant)
                         (expt 2 (+ (cexp) (- (pexp)))))
                      (pmant))
                   (< (+ 2
                         (* (cmant)
                            (expt 2 (+ 2 (cexp) (- (pexp))))))
                      (* 4 (pmant)))))
     :hints (("Goal" :use (:instance aux-1
                                     (x (* (cmant)
                                           (expt 2 (+ (cexp) (- (pexp))))))
                                     (y *2^22*)
                                     (z (pmant)))))
     :rule-classes :linear))

  (local
   (defthm-nl sum-lower-bound-non-severe-1-aux-1
     (implies (and (equal (clarger) 0)
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (equal (inx) 0))
              (<= 2 (sum)))
     :hints (("Goal"
              :use (fi-lower-bound-non-severe
                    pexp-=-4
                    (:instance expt-lemma-2
                               (x (cmant))
                               (i -24)
                               (j (+ 1 (cexp) (- (pexp)))))
                    (:instance aux-2
                               (x (/ (fi) 2))))
              :in-theory (e/d (mlarge
                               msmall
                               ediff
                               elarge
                               esmall
                               sum-fi-rel
                               inx-fi-rel
                               fi)
                              (fi-lower-bound-non-severe
                               pexp-=-4))))
     :rule-classes :linear))

  (local
   (defthm-nl++ sum-lower-bound-non-severe-aux-2
     (implies (and (<= 140737488355328 (cmant))
                   (<= (+ 2 (pexp)) (cexp)))
              (and (< (* (pmant)
                         (expt 2 (+ (- (cexp)) (pexp))))
                      (cmant))
                   (< (+ 2
                         (* (pmant)
                            (expt 2 (+ 2 (- (cexp)) (pexp)))))
                      (* 4 (cmant)))))
     :rule-classes :linear))

  (local
   (defthm-nl sum-lower-bound-non-severe-1-aux-2
     (implies (and (equal (clarger) 1)
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (or (< 15 (si (scale) 10))
                       (< 128 (elarge)))
                   (equal (severe) 0)
                   (equal (inx) 0))
              (<= 2 (sum)))
     :hints (("Goal"
              :cases ((<= 2 (ediff)))
              :use (fi-lower-bound-non-severe
                    scale-prop
                    cexp-=-128
                    (:instance aux-2
                               (x (/ (fi) 2))))
              :in-theory (e/d (mlarge
                               msmall
                               ediff
                               elarge
                               esmall
                               clarger
                               sum-fi-rel
                               inx-fi-rel
                               fi)
                              (fi-lower-bound-non-severe
                               scale-prop
                               cexp-=-128))))
     :rule-classes :linear))

  (defthm sum-lower-bound-non-severe-1
    (implies (and (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (or (< 15 (si (scale) 10))
                      (< 128 (elarge)))
                  (equal (severe) 0)
                  (equal (inx) 0))
             (<= 2 (sum)))
    :hints (("Goal" :use (sum-lower-bound-non-severe-1-aux-1
                          sum-lower-bound-non-severe-1-aux-2)))
    :rule-classes :linear)

  (local
   (defthm-nl++ sum-lower-bound-non-severe-aux-3
     (implies (and (<= 8388608 (pmant))
                   (<= (+ 27 (cexp)) (pexp)))
              (< *2^24*
                 (+ (* 4 (pmant))
                    (- (* (cmant)
                          (expt 2 (+ 2 (cexp) (- (pexp)))))))))
     :hints (("Goal" :use (:instance aux-1
                                     (x (+ (expt 2 (+ 24 (pexp)))
                                           (* 4 (cmant) (expt 2 (cexp)))))
                                     (y (* 3 (expt 2 (+ 23 (pexp)))))
                                     (z (* 4 (pmant) (expt 2 (pexp)))))))
     :rule-classes :linear))

  (local
   (defthm sum-lower-bound-non-severe-2-aux-1
     (implies (and (equal (clarger) 0)
                   (numeric-a-b-p)
                   (equal (severe) 0)
                   (equal (inx) 1))
              (<= *2^24* (sum)))
     :hints (("Goal"
              :use (ediff-lower-bound-when-clarger-is-0
                    pexp-=-4)
              :in-theory (e/d (mlarge
                               msmall
                               ediff
                               elarge
                               esmall
                               sum-fi-rel
                               fi)
                              (ediff-lower-bound-when-clarger-is-0
                               pexp-=-4))))
     :rule-classes :linear))

  (local
   (defthm-nl++ sum-lower-bound-non-severe-aux-4
     (implies (and (<= 140737488355328 (cmant))
                   (<= (+ 3 (pexp)) (cexp)))
              (< *2^24*
                 (+ (* 4 (cmant))
                    (- (* (pmant)
                          (expt 2 (+ 2 (- (cexp)) (pexp))))))))
     :rule-classes :linear))

  (local
   (defthm-nl sum-lower-bound-non-severe-2-aux-2
     (implies (and (equal (clarger) 1)
                   (numeric-a-b-p)
                   (or (< 15 (si (scale) 10))
                       (< 128 (elarge)))
                   (equal (severe) 0)
                   (equal (inx) 1))
              (<= *2^24* (sum)))
     :hints (("Goal"
              :use (ediff-lower-bound-when-clarger-is-1
                    scale-prop
                    cexp-=-128)
              :in-theory (e/d (mlarge
                               msmall
                               ediff
                               elarge
                               esmall
                               clarger
                               sum-fi-rel
                               fi)
                              (ediff-lower-bound-when-clarger-is-1
                               scale-prop
                               cexp-=-128))))
     :rule-classes :linear))

  (defthm sum-lower-bound-non-severe-2
    (implies (and (numeric-a-b-p)
                  (or (< 15 (si (scale) 10))
                      (< 128 (elarge)))
                  (equal (severe) 0)
                  (equal (inx) 1))
             (<= *2^24* (sum)))
    :hints (("Goal" :use (sum-lower-bound-non-severe-2-aux-1
                          sum-lower-bound-non-severe-2-aux-2)))
    :rule-classes :linear)
  )

(encapsulate
  ()

  (local
   (defthm-nl abs-s-tilde-upper-bound-2-aux-1
     (implies (and (numeric-a-b-p)
                   (equal (severe) 1))
              (< (abs (s-tilde))
                 (/ (spd (sp)) 2)))
     :hints (("Goal"
              :use (scale-elarge-inx-rel fi-=-0)
              :in-theory (e/d (abs-s-tilde-rewrite-1 sp)
                              (fi-=-0 abs))))
     :rule-classes :linear))

  (bvecthm bvecp51-sum
    (bvecp (sum) 51)
    :hints (("Goal" :in-theory (enable sum computesum))))

  (local
   (defthm-nl abs-s-tilde-upper-bound-2-aux-2
     (implies (and (numeric-a-b-p)
                   (equal (severe) 0)
                   (< (sumexp) 896))
              (< (abs (s-tilde))
                 (/ (spd (sp)) 2)))
     :hints (("Goal"
              :use s-tilde-sum-rel
              :in-theory (e/d (sp)
                              (s-tilde-sum-rel abs))))
     :rule-classes :linear))

  (bitthm bitp-severe
    (bitp (severe))
    :hints (("Goal" :in-theory (enable severe computesum))))

  (defthm-nl abs-s-tilde-upper-bound-2
    (implies (and (numeric-a-b-p)
                  (or (equal (severe) 1)
                      (< (sumexp) 896)))
             (< (abs (s-tilde))
                (/ (spd (sp)) 2)))
    :hints (("Goal"
             :use (abs-s-tilde-upper-bound-2-aux-1
                   abs-s-tilde-upper-bound-2-aux-2)))
    :rule-classes :linear)

  (defthm abs-s-upper-bound-2
    (implies (and (numeric-a-b-p)
                  (numeric-c-p)
                  (or (equal (severe) 1)
                      (< (sumexp) 896)))
             (< (abs (s))
                (/ (spd (sp)) 2)))
    :hints (("Goal"
             :use (s-tilde-=-s-1
                   abs-s-upper-bound-1
                   abs-s-tilde-lower-bound-1
                   abs-s-tilde-upper-bound-2)
             :in-theory (e/d (sp) (abs))))
    :rule-classes :linear)
  )


