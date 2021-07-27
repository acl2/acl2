;; Cuong Chau <cuong.chau@arm.com>

;; February 2021

;; Prove correctness for special inputs

(in-package "RTL")

(include-book "prelim")
(include-book "spec")

(local
 (in-theory (disable bits-neg-indices
                     bits-reverse-indices
                     bits-tail-gen
                     neg-bitn-0
                     neg-bitn-1)))

;; ======================================================================

(defundd numeric-a-b-p ()
  (and (equal (anan) 0)
       (equal (ainf) 0)
       (equal (bnan) 0)
       (equal (binf) 0)))

(defundd numeric-c-p ()
  (and (equal (cnan) 0)
       (equal (cinf) 0)))

(defundd not-both-p&c-zeros-p ()
  (or (equal (pzero) 0)
      (equal (czero) 0)))

(defundd csign-orig ()
  (bitn (c) 31))

(defthmd csign-=-csign-orig
  (equal (csign) (csign-orig))
  :hints (("Goal" :in-theory (enable csign
                                     csign-orig
                                     c-scale
                                     scale128))))

(defundd cexp-orig ()
  (if (equal (bits (c) 30 23) 0)
      1
    (bits (c) 30 23)))

(bvecthm bvecp8-cexp-orig
  (bvecp (cexp-orig) 8)
  :hints (("Goal" :in-theory (enable cexp-orig))))

(defthm cexp-orig-num-upper-bound
  (implies (numeric-c-p)
           (<= (cexp-orig) 254))
  :hints (("Goal" :in-theory (e/d (numeric-c-p
                                   cnan
                                   cinf
                                   cexp-orig
                                   c-scale
                                   scale128)
                                  (bits-tail-gen))))
  :rule-classes :linear)

(defundd cmant-orig ()
  (if (equal (bits (c) 30 23) 0)
      (bits (c) 22 0)
    (cat 1 1
         (bits (c) 22 0) 23)))

(bvecthm bvecp24-cmant-orig
  (bvecp (cmant-orig) 24)
  :hints (("Goal" :in-theory (enable cmant-orig))))

(defthmd psign-rewrite
  (equal (psign)
         (logxor (bitn (a) 31) (bitn (b) 31)))
  :hints (("Goal" :in-theory (enable psign fmul32))))

(local
 (defthmd pnan-or-pinf
   (equal (numeric-a-b-p)
          (and (equal (pnan) 0)
               (equal (pinf) 0)))
   :hints (("Goal" :in-theory (enable numeric-a-b-p
                                      pnan
                                      pinf
                                      anan
                                      ainf
                                      bnan
                                      binf
                                      pexp
                                      rexp
                                      bvecp
                                      scale128
                                      fmul32)))))

(local
 (defthmd ressign-special-1
   (implies (or (not (numeric-a-b-p))
                (not (numeric-c-p)))
            (equal (ressign)
                   (if1 (logior1 (logior1 (cnan) (pnan))
                                 (logand1 (logand1 (cinf) (pinf))
                                          (logxor (csign) (psign))))
                        0
                        (if1 (cinf) (csign) (psign)))))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      ressign
                                      pnan-or-pinf)))))

(local
 (defthmd ressign-special-2
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not (not-both-p&c-zeros-p)))
            (equal (ressign)
                   (logior1 (logand1 (csign) (psign))
                            (logand1 (log= (rmode) 1)
                                     (logior1 (csign) (psign))))))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      not-both-p&c-zeros-p
                                      ressign
                                      pnan-or-pinf)))))

(local
 (defthmd resexp-special-1
   (implies (or (not (numeric-a-b-p))
                (not (numeric-c-p)))
            (equal (resexp) 255))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      resexp
                                      pnan-or-pinf)))))

(local
 (defthmd resexp-special-2
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not (not-both-p&c-zeros-p)))
            (equal (resexp) 0))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      not-both-p&c-zeros-p
                                      resexp
                                      pnan-or-pinf)))))

(local
 (defthmd resmant-special-1
   (implies (or (not (numeric-a-b-p))
                (not (numeric-c-p)))
            (equal (resmant)
                   (if1 (logior1 (logior1 (cnan) (pnan))
                                 (logand1 (logand1 (cinf) (pinf))
                                          (logxor (csign) (psign))))
                        4194304
                        0)))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      resmant
                                      pnan-or-pinf)))))

(local
 (defthmd resmant-special-2
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not (not-both-p&c-zeros-p)))
            (equal (resmant) 0))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      not-both-p&c-zeros-p
                                      resmant
                                      pnan-or-pinf)))))

(local
 (defthmd rndinc-special
   (implies (or (not (numeric-a-b-p))
                (not (numeric-c-p))
                (not (not-both-p&c-zeros-p)))
            (equal (rndinc) 0))
   :hints (("Goal" :in-theory (enable numeric-c-p
                                      not-both-p&c-zeros-p
                                      rndinc
                                      pnan-or-pinf)))))

(local
 (defthmd numeric-a-b-p-rewrite
   (equal (numeric-a-b-p)
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
                                      expf
                                      unsupp
                                      encodingp)))))

(local
 (defthmd pnan-lemma
   (equal (equal (pnan) 1)
          (or (equal (anan) 1)
              (equal (bnan) 1)
              (and (equal (ainf) 1)
                   (equal (bzero) 1))
              (and (equal (azero) 1)
                   (equal (binf) 1))))
   :hints (("Goal" :in-theory (enable pnan
                                      anan
                                      ainf
                                      azero
                                      bnan
                                      binf
                                      bzero
                                      pexp
                                      rexp
                                      bvecp
                                      scale128
                                      fmul32)))))

(local
 (defthmd pinf-lemma
   (equal (equal (pinf) 1)
          (and (equal (anan) 0)
               (equal (azero) 0)
               (equal (bnan) 0)
               (equal (bzero) 0)
               (or (equal (ainf) 1)
                   (equal (binf) 1))))
   :hints (("Goal"
            :use ((:instance bits-plus-bits
                             (x (a))
                             (m 0)
                             (p 23)
                             (n 30))
                  (:instance bits-plus-bits
                             (x (b))
                             (m 0)
                             (p 23)
                             (n 30)))
            :in-theory (enable pinf
                               anan
                               ainf
                               azero
                               bnan
                               binf
                               bzero
                               pexp
                               rexp
                               bvecp
                               scale128
                               fmul32)))))

(local
 (defthmd pzero-lemma
   (implies (equal (pzero) 1)
            (or (equal (azero) 1)
                (equal (bzero) 1)))
   :hints (("Goal"
            :in-theory (enable pzero
                               azero
                               bzero
                               pexp
                               rexp
                               bvecp
                               scale128
                               fmul32)))))

(local
 (defthmd anan-lemma
   (equal (equal (anan) 1)
          (nanp (a) (sp)))
   :hints (("Goal" :in-theory (enable nanp
                                      anan
                                      expf
                                      manf
                                      unsupp
                                      encodingp)))))

(local
 (defthmd ainf-lemma
   (equal (equal (ainf) 1)
          (infp (a) (sp)))
   :hints (("Goal" :in-theory (enable infp
                                      ainf
                                      expf
                                      manf
                                      unsupp
                                      encodingp)))))

(local
 (defthmd azero-lemma
   (equal (equal (azero) 1)
          (zerp (a) (sp)))
   :hints (("Goal"
            :use (:instance bits-plus-bits
                            (x (a))
                            (m 0)
                            (p 23)
                            (n 30))
            :in-theory (enable zerp
                               azero
                               expf
                               manf
                               encodingp)))))

(local
 (defthmd bnan-lemma
   (equal (equal (bnan) 1)
          (nanp (b) (sp)))
   :hints (("Goal" :in-theory (enable nanp
                                      bnan
                                      expf
                                      manf
                                      unsupp
                                      encodingp)))))

(local
 (defthmd binf-lemma
   (equal (equal (binf) 1)
          (infp (b) (sp)))
   :hints (("Goal" :in-theory (enable infp
                                      binf
                                      expf
                                      manf
                                      unsupp
                                      encodingp)))))

(local
 (defthmd bzero-lemma
   (equal (equal (bzero) 1)
          (zerp (b) (sp)))
   :hints (("Goal"
            :use (:instance bits-plus-bits
                            (x (b))
                            (m 0)
                            (p 23)
                            (n 30))
            :in-theory (enable zerp
                               bzero
                               expf
                               manf
                               encodingp)))))

(local
 (defthmd cnan-lemma
   (equal (equal (cnan) 1)
          (nanp (c) (sp)))
   :hints (("Goal" :in-theory (enable nanp
                                      cnan
                                      c-scale
                                      scale128
                                      expf
                                      manf
                                      bvecp
                                      unsupp
                                      encodingp)))))

(local
 (defthmd cinf-lemma
   (equal (equal (cinf) 1)
          (infp (c) (sp)))
   :hints (("Goal" :in-theory (enable infp
                                      cinf
                                      c-scale
                                      scale128
                                      expf
                                      manf
                                      bvecp
                                      unsupp
                                      encodingp)))))

(local
 (defthmd fma32-main-special-1
   (implies (or (not (numeric-a-b-p))
                (not (numeric-c-p)))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d)
                               (rmode) (scaleop))))
   :hints (("Goal"
            :use (pnan-or-pinf
                  numeric-a-b-p-rewrite
                  pnan-lemma
                  pinf-lemma
                  anan-lemma
                  ainf-lemma
                  azero-lemma
                  bnan-lemma
                  binf-lemma
                  bzero-lemma
                  cnan-lemma
                  cinf-lemma)
            :in-theory (e/d (numeric-c-p
                             data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-special-1
                             resexp-special-1
                             resmant-special-1
                             rndinc-special
                             psign-rewrite
                             csign-=-csign-orig
                             csign-orig
                             logxor-of-bits-rewrite
                             sgnf)
                            (logxor-commutative-2))))))

(defthmd decode-azero
  (implies (equal (azero) 1)
           (equal (decode (a) (sp))
                  0))
  :hints (("Goal"
           :use (:instance bits-plus-bits
                           (x (a))
                           (m 0)
                           (p 23)
                           (n 30))
           :in-theory (enable azero
                              decode
                              ddecode
                              expf
                              manf))))

(defthmd decode-bzero
  (implies (equal (bzero) 1)
           (equal (decode (b) (sp))
                  0))
  :hints (("Goal"
           :use (:instance bits-plus-bits
                           (x (b))
                           (m 0)
                           (p 23)
                           (n 30))
           :in-theory (enable bzero
                              decode
                              ddecode
                              expf
                              manf))))

(defthmd decode-czero
  (implies (equal (czero) 1)
           (equal (decode (c) (sp))
                  0))
  :hints (("Goal"
           :use (:instance bits-plus-bits
                           (x (c))
                           (m 0)
                           (p 23)
                           (n 30))
           :in-theory (enable czero
                              c-scale
                              scale128
                              decode
                              ddecode
                              expf
                              manf
                              pos-cat))))

(local
 (defthmd fma32-main-special-2
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not (not-both-p&c-zeros-p)))
            (equal (data)
                   (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
   :hints (("Goal"
            :use (pzero-lemma
                  azero-lemma
                  bzero-lemma
                  cnan-lemma
                  cinf-lemma)
            :in-theory (e/d (numeric-a-b-p-rewrite
                             numeric-c-p
                             not-both-p&c-zeros-p
                             data-=-resrnd
                             fma32-spec
                             resrnd
                             res
                             ressign-special-2
                             resexp-special-2
                             resmant-special-2
                             rndinc-special
                             psign-rewrite
                             csign-=-csign-orig
                             csign-orig
                             decode-azero
                             decode-bzero
                             decode-czero
                             decode-fma-rmode
                             sgnf)
                            ())))))

(defthmd fma32-main-special
  (implies (or (not (numeric-a-b-p))
               (not (numeric-c-p))
               (not (not-both-p&c-zeros-p)))
           (equal (data)
                  (fma32-spec (a) (b) (c) (d) (rmode) (scaleop))))
  :hints (("Goal" :use (fma32-main-special-1 fma32-main-special-2))))
