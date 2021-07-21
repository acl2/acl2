;; Cuong Chau <cuong.chau@arm.com>

;; July 2021

;; The events in this book are derived from the hand proofs developed by David
;; Russinoff <david.russinoff@arm.com>.

(in-package "RTL")

(include-book "resrnd")

(local (arith-5-for-rtl))

;; ======================================================================

(local
 (defthm numeric-a-b-p-lemma
   (implies (numeric-a-b-p)
            (and (not (nanp (a) (sp)))
                 (not (infp (a) (sp)))
                 (not (nanp (b) (sp)))
                 (not (infp (b) (sp)))))
   :hints (("Goal" :in-theory (enable numeric-a-b-p
                                      nanp
                                      infp
                                      anan
                                      ainf
                                      bnan
                                      binf
                                      expf)))))

(local
 (defthm numeric-c-p-lemma
   (implies (numeric-c-p)
            (and (not (nanp (c) (sp)))
                 (not (infp (c) (sp)))))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      nanp
                                      infp
                                      cnan
                                      cinf
                                      c-scale
                                      scale128
                                      expf)))))

(local
 (defthmd ressign-0
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (equal (severe) 1)
                 (equal (inx) 0))
            (equal (ressign)
                   (logior1 (logand1 (csign) (psign))
                            (logand1 (log= (rmode) 1)
                                     (logior1 (csign) (psign))))))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               pnan
                               pinf
                               ressign)))))

(local
 (defthmd resexp-unf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (or (equal (severe) 1)
                     (< (sumexp) 896)))
            (equal (resexp) 0))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               pnan
                               pinf
                               resexp)))))

(local
 (defthmd resexp-ovf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< 1149 (- (sumexp) (clzprime))))
            (equal (resexp) 254))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               not-both-p&c-zeros-p
                               pnan
                               pinf
                               resexp)))))

(local
 (defthmd resmant-unf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (or (equal (severe) 1)
                     (< (sumexp) 896)))
            (equal (resmant) 0))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               pnan
                               pinf
                               resmant)))))

(local
 (defthmd resmant-ovf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< 1149 (- (sumexp) (clzprime))))
            (equal (resmant) 8388607))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               not-both-p&c-zeros-p
                               pnan
                               pinf
                               resmant)))))

(local
 (defthmd rndinc-0
   (implies (and (equal (severe) 1)
                 (equal (inx) 0))
            (equal (rndinc) 0))
   :hints (("Goal" :in-theory (enable rndinc)))))

(local
 (defthmd rndinc-unf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (or (and (equal (severe) 1)
                          (equal (inx) 1))
                     (and (equal (severe) 0)
                          (< (sumexp) 896))))
            (equal (rndinc)
                   (logior1 (log= (rmode) 5)
                            (if1 (ressign-1)
                                 (log= (rmode) 1)
                                 (log= (rmode) 0)))))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               not-both-p&c-zeros-p
                               pnan
                               pinf
                               rndinc)))))

(local
 (defthmd rndinc-ovf
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< 1149 (- (sumexp) (clzprime))))
            (equal (rndinc)
                   (lognot1
                    (logior1
                     (logior1 (log= (rmode) 2)
                              (logand1 (ressign-1)
                                       (log= (rmode) 0)))
                     (logand1 (lognot1 (ressign-1))
                              (log= (rmode) 1))))))
   :hints (("Goal"
            :use pexp-bounds
            :in-theory (enable numeric-a-b-p
                               numeric-c-p
                               not-both-p&c-zeros-p
                               pnan
                               pinf
                               rndinc)))))

(local
 (defthmd fma32-main-0
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 1)
                 (equal (inx) 0))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use s-=-0
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-0
                             resexp-unf
                             resmant-unf
                             rndinc-0
                             s
                             p
                             cval
                             psign-rewrite
                             csign-=-csign-orig
                             csign-orig
                             decode-fma-rmode
                             sgnf)
                            (s-=-0
                             abs))))))

(local
 (defthm rnd-ext-s-unf
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (or (equal (severe) 1)
                     (< (sumexp) 896)))
            (< (abs (rnd-ext (s)
                             (decode-fma-rmode (rmode))
                             24))
               (lpn (sp))))
   :hints (("Goal"
            :use (abs-s-upper-bound-2
                  (:instance rnd-ext-exactp-c
                             (a (/ (spd (sp)) 2))
                             (x (s))
                             (mode (decode-fma-rmode (rmode)))
                             (n 24))
                  (:instance rnd-ext-exactp-d
                             (a (- (/ (spd (sp)) 2)))
                             (x (s))
                             (mode (decode-fma-rmode (rmode)))
                             (n 24)))
            :in-theory (e/d (spd-sp lpn-sp)
                            (abs-s-upper-bound-2))))
   :rule-classes :linear))

(local
 (defthmd fma32-main-unf-severe
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 1)
                 (equal (inx) 1))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (abs-s-upper-bound-2
                  rnd-ext-s-unf
                  drnd-ext-s-1
                  s-tilde-ressign-1-rel-severe
                  s-s-tilde-rel-1)
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-rewrite
                             resexp-unf
                             resmant-unf
                             rndinc-unf
                             s-s-tilde-rel-2
                             s
                             p
                             cval
                             dencode
                             sgn
                             spd-sp
                             spn-sp)
                            (abs-s-upper-bound-2
                             rnd-ext-s-unf
                             abs))))))

(local
 (defthmd fma32-main-unf-non-severe
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< (sumexp) 896))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (abs-s-upper-bound-2
                  rnd-ext-s-unf
                  drnd-ext-s-1
                  s-tilde-ressign-1-rel-non-severe
                  s-s-tilde-rel-1)
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-rewrite
                             resexp-unf
                             resmant-unf
                             rndinc-unf
                             s-s-tilde-rel-2
                             s
                             p
                             cval
                             dencode
                             sgn
                             spd-sp
                             spn-sp)
                            (abs-s-upper-bound-2
                             rnd-ext-s-unf
                             abs))))))

(local
 (defthm rnd-ext-s-ovf
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< 1149 (- (sumexp) (clzprime))))
            (< (lpn (sp))
               (abs (rnd-ext (s)
                             (decode-fma-rmode (rmode))
                             24))))
   :hints (("Goal"
            :use (abs-s-lower-bound-2
                  (:instance rnd-ext-exactp-c
                             (a (- (expt 2 128)))
                             (x (s))
                             (mode (decode-fma-rmode (rmode)))
                             (n 24))
                  (:instance rnd-ext-exactp-d
                             (a (expt 2 128))
                             (x (s))
                             (mode (decode-fma-rmode (rmode)))
                             (n 24)))
            :in-theory (e/d (lpn-sp)
                            (abs-s-lower-bound-2))))
   :rule-classes :linear))

(local
 (defthmd fma32-main-ovf
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (< 1149 (- (sumexp) (clzprime))))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (rnd-ext-s-ovf
                  s-tilde-ressign-1-rel-non-severe
                  nonzero-s-s-tilde)
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-rewrite
                             resexp-ovf
                             resmant-ovf
                             rndinc-ovf
                             s-s-tilde-rel-2
                             s
                             p
                             cval
                             decode-fma-rmode
                             nencode
                             sgn
                             spn-sp
                             lpn-sp)
                            (rnd-ext-s-ovf
                             nonzero-s-s-tilde
                             abs))))))

(local
 (defthmd fma32-main-normal
   (implies (and (<= (spn (sp)) (abs (s)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (resrnd-rnd-ext-s-rel-3
                  s-tilde-ressign-1-rel-non-severe
                  nonzero-s-s-tilde)
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd-rnd-ext-s-rel-2
                             ressign-rewrite
                             s-s-tilde-rel-2
                             s
                             p
                             cval)
                            (nonzero-s-s-tilde
                             abs))))))

(local
 (defthmd fma32-main-denormal
   (implies (and (< (abs (s)) (spn (sp)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (drnd-ext-s-bounds
                  s-tilde-ressign-1-rel-non-severe
                  nonzero-s-s-tilde)
            :in-theory (e/d (data-=-resrnd
                             fma32-spec
                             resrnd-drnd-ext-s-rel-5
                             resrnd-drnd-ext-s-rel-6
                             resrnd-drnd-ext-s-rel-7
                             ressign-rewrite
                             s-s-tilde-rel-2
                             s
                             p
                             cval)
                            (drnd-ext-s-bounds
                             nonzero-s-s-tilde
                             abs))))))

(local
 (defthmd fma32-main-non-special
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (fma32-main-0
                  fma32-main-unf-severe
                  fma32-main-unf-non-severe
                  fma32-main-ovf
                  fma32-main-normal
                  fma32-main-denormal)
            :in-theory (enable decode-fma-rmode)))))

(defthmd fma32-main
  (equal (fma32      (a) (b) (c) (d) (rmode) (scaleop))
         (fma32-spec (a) (b) (c) (d) (rmode) (scaleop)))
  :hints (("Goal"
           :use (fma32-main-special fma32-main-non-special)
           :in-theory (enable fma32-lemma))))

(defthmd fma32-correct
  (implies (input-constraints a b c d rmode scaleop)
           (equal (fma32      a b c d rmode scaleop)
                  (fma32-spec a b c d rmode scaleop)))
  :hints (("Goal"
           :use (:functional-instance
                 fma32-main
                 (a (lambda ()
                      (if (input-constraints
                           a b c d rmode scaleop)
                          a
                        (a))))
                 (b (lambda ()
                      (if (input-constraints
                           a b c d rmode scaleop)
                          b
                        (b))))
                 (c (lambda ()
                      (if (input-constraints
                           a b c d rmode scaleop)
                          c
                        (c))))
                 (d (lambda ()
                      (if (input-constraints
                           a b c d rmode scaleop)
                          d
                        (d))))
                 (rmode (lambda ()
                          (if (input-constraints
                               a b c d rmode scaleop)
                              rmode
                            (rmode))))
                 (scaleop (lambda ()
                            (if (input-constraints
                                 a b c d rmode scaleop)
                                scaleop
                              (scaleop))))))))


