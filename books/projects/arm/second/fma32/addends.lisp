;; Cuong Chau <cuong.chau@arm.com>

;; March 2021

;; The events in this book are derived from the hand proofs developed by David
;; Russinoff <david.russinoff@arm.com>.

(in-package "RTL")

(include-book "special")

(local (arith-5-for-rtl))

(local (in-theory (disable bits-fl)))

;; ======================================================================

(defundd p ()
  (* (decode (a) (sp))
     (decode (b) (sp))))

(defundd cval ()
  (decode (c) (sp)))

(defthmd cval-rewrite
  (equal (cval)
         (* (if (equal (csign-orig) 0) 1 -1)
            (expt 2 (- (cexp-orig) 150))
            (cmant-orig)))
  :hints (("Goal" :in-theory (enable cval
                                     csign-orig
                                     cexp-orig
                                     cmant-orig
                                     decode
                                     ddecode
                                     ndecode
                                     sgnf
                                     expf
                                     manf
                                     cat))))

(defundd s ()
  (if (equal (scaleop) 0)
      (+ (p) (cval))
    (* (expt 2 (si (d) 32))
       (+ (p) (cval)))))

(defthm natp-rexp
  (natp (rexp))
  :hints (("Goal" :in-theory (enable rexp fmul32)))
  :rule-classes :type-prescription)

(defthm natp-pexp
  (natp (pexp))
  :hints (("Goal" :in-theory (enable pexp scale128)))
  :rule-classes :type-prescription)

(bvecthm bvecp48-pmant
  (bvecp (pmant) 48)
  :hints (("Goal" :in-theory (enable pmant fmul32 bvecp))))

(defthm natp-cexp
  (natp (cexp))
  :hints (("Goal" :in-theory (enable cexp)))
  :rule-classes :type-prescription)

(defthm cexp-bounds
  (and (<= 128 (cexp))
       (<= (cexp) 383))
  :hints (("Goal" :in-theory (enable cexp bvecp)))
  :rule-classes :linear)

(defthm cexp-num-upper-bound
  (implies (numeric-c-p)
           (<= (cexp) 382))
  :hints (("Goal" :in-theory (enable numeric-c-p
                                     cexp
                                     cnan
                                     cinf
                                     bvecp)))
  :rule-classes :linear)

(bvecthm bvecp48-cmant
  (bvecp (cmant) 48)
  :hints (("Goal" :in-theory (enable cmant))))

(defthm zero-prod
  (implies (and (numeric-a-b-p)
                (equal (p) 0))
           (and (equal (rexp) 0)
                (equal (pmant) 0)))
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
           :in-theory (enable numeric-a-b-p
                              p
                              anan
                              ainf
                              bnan
                              binf
                              rexp
                              pmant
                              cat
                              decode
                              ddecode
                              expf
                              manf
                              fmul32))))

(defthm rexp-bounds
  (implies (and (numeric-a-b-p)
                (not (equal (p) 0)))
           (and (<= 4 (rexp))
                (<= (rexp) 510)))
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
           :in-theory (enable numeric-a-b-p
                              p
                              anan
                              ainf
                              bnan
                              binf
                              rexp
                              bvecp
                              decode
                              ddecode
                              expf
                              manf
                              fmul32)))
  :rule-classes :linear)

(defthm-nl rexp-=-4
  (implies (and (< (pmant) (expt 2 23))
                (not (equal (p) 0)))
           (equal (rexp) 4))
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
           :in-theory (enable p
                              rexp
                              pmant
                              cat
                              bvecp
                              decode
                              ddecode
                              expf
                              manf
                              fmul32))))

(defthmd-nl p-rewrite
  (implies (numeric-a-b-p)
           (equal (p)
                  (* (if (equal (psign) 0) 1 -1)
                     (expt 2 (- (rexp) 302))
                     (pmant))))
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
           :in-theory (e/d (numeric-a-b-p
                            p
                            psign
                            rexp
                            pmant
                            anan
                            ainf
                            bnan
                            binf
                            decode
                            ddecode
                            ndecode
                            sgnf
                            expf
                            manf
                            bvecp
                            cat
                            fmul32)
                           (logand1
                            logior1
                            bits-tail-gen)))))

(defthmd p-=-0
  (equal (equal (p) 0)
         (or (equal (bits (a) 30 0) 0)
             (equal (bits (b) 30 0) 0)))
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
           :in-theory (enable p
                              decode
                              ddecode
                              ndecode
                              expf
                              manf))))

;; ======================================================================

(defundd p-tilde ()
  (* (if (equal (psign) 0) 1 -1)
     (expt 2 (- (pexp) 302))
     (pmant)))

(defundd c-tilde ()
  (* (if (equal (csign) 0) 1 -1)
     (expt 2 (- (cexp) 302))
     (cmant)))

(defundd s-tilde ()
  (* (expt 2 (si (scale) 10))
     (+ (p-tilde) (c-tilde))))

(defundd adj-cond-p ()
  (and (equal (scaleop) 1)
       (<= 16 (si (d) 32))
       (not (equal (p) 0))
       (equal (cdenorm) 1)
       (<= 64 (abexp))
       (< (abexp) 256)))

(defthm integerp-scale
  (integerp (scale))
  :hints (("Goal" :in-theory (enable scale scale128)))
  :rule-classes :type-prescription)

(defthm scale-lemma-1
  (implies (equal (scaleop) 0)
           (equal (scale) 0))
  :hints (("Goal" :in-theory (enable scale))))

(defthm scale-lemma-2
  (implies (and (equal (scaleop) 1)
                (< 511 (si (d) 32)))
           (equal (scale) 511))
  :hints (("Goal"
           :use (:instance bitn-plus-bits
                           (x (d))
                           (m 0)
                           (n 31))
           :in-theory (enable scale
                              scale128))))

(defthm scale-lemma-3
  (implies (and (equal (scaleop) 1)
                (< (si (d) 32) -512))
           (equal (scale) 512))
  :hints (("Goal"
           :in-theory (enable scale scale128))))

(defthmd scale-lemma-4
  (implies (and (not (equal (scaleop) 0))
                (<= -512 (si (d) 32))
                (<= (si (d) 32) 511))
           (equal (scale)
                  (if (and (adj-cond-p)
                           (numeric-a-b-p))
                      (bits (- (si (d) 32) 128) 9 0)
                    (bits (si (d) 32) 9 0))))
  :hints (("Goal"
           :use (:instance bits-plus-mult-2
                           (x (+ 896 (si (d) 32)))
                           (y #x3FFFFF)
                           (k 10)
                           (m 0)
                           (n 9))
           :in-theory (e/d (scale
                            adj-cond-p
                            numeric-a-b-p
                            anan
                            ainf
                            bnan
                            binf
                            cdenorm
                            abexp
                            scale128
                            bvecp
                            p-=-0)
                           (bits-tail-gen)))))

(local
 (defthm rexp-abexp-rel-1
   (implies (and (numeric-a-b-p)
                 (not (equal (pmant) 0)))
            (<= (+ 2 (abexp)) (rexp)))
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
            :in-theory (enable numeric-a-b-p
                               pmant
                               rexp
                               abexp
                               anan
                               ainf
                               bnan
                               binf
                               bvecp
                               cat
                               fmul32)))
   :rule-classes :linear))

(local
 (defthm rexp-abexp-rel-2
   (implies (numeric-a-b-p)
            (<= (rexp)
                (+ 4 (abexp))))
   :hints (("Goal"
            :in-theory (enable numeric-a-b-p
                               rexp
                               abexp
                               anan
                               ainf
                               bnan
                               binf
                               bvecp
                               fmul32)))
   :rule-classes :linear))

(defthm-nl abs-cval-lower-bound
  (implies (not (equal (bits (c) 30 0) 0))
           (<= (spd (sp))
               (abs (cval))))
  :hints (("Goal"
           :use (:instance bits-plus-bits
                           (x (c))
                           (m 0)
                           (p 23)
                           (n 30))
           :in-theory (enable cval-rewrite
                              cexp-orig
                              cmant-orig
                              cat
                              sp)))
  :rule-classes :linear)

(local
 (defthmd abs-cval-upper-bound-aux
   (implies (and (<= x y)
                 (not (equal x y))
                 (integerp x)
                 (integerp y))
            (<= x (1- y)))))

(defthm-nl abs-cval-upper-bound
  (implies (not (equal (cexp-orig) 255))
           (<= (abs (cval))
               (lpn (sp))))
  :hints (("Goal"
           :use (:instance abs-cval-upper-bound-aux
                           (x (bits (c) 30 23))
                           (y 255))
           :in-theory (enable cval-rewrite
                              cexp-orig
                              cmant-orig
                              cat
                              sp)))
  :rule-classes :linear)

(defthmd pexp-rexp-rel-1
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (pexp)
                  (+ 128 (rexp))))
  :hints (("Goal"
           :use rexp-abexp-rel-2
           :in-theory (e/d (adj-cond-p
                            numeric-a-b-p
                            anan
                            ainf
                            bnan
                            binf
                            cdenorm
                            abexp
                            pexp
                            scale128
                            bvecp
                            p-=-0)
                           (bits-tail-gen
                            rexp-abexp-rel-2)))))

(defthmd p-tilde-p-rel-1
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (p-tilde)
                  (* (expt 2 128) (p))))
  :hints (("Goal"
           :in-theory (enable p-tilde
                              p-rewrite
                              pexp-rexp-rel-1))))

(defthmd pexp-rexp-rel-2
  (implies (not (adj-cond-p))
           (equal (pexp) (rexp)))
  :hints (("Goal" :in-theory (enable adj-cond-p
                                     pexp
                                     cdenorm
                                     abexp
                                     scale128
                                     p-=-0))))

(defthmd p-tilde-p-rel-2
  (implies (and (not (adj-cond-p))
                (numeric-a-b-p))
           (equal (p-tilde) (p)))
  :hints (("Goal"
           :in-theory (enable p-tilde
                              p-rewrite
                              pexp-rexp-rel-2))))

(def-gl-rule clz24-expo
  :hyp (and (bvecp x 24)
            (< 0 x))
  :concl (equal (clz24 x) (- 23 (expo x)))
  :g-bindings (gl::auto-bindings
               (:nat x 24)))

(defthmd clz-c-rewrite
  (implies (not (equal (bits (c) 22 0) 0))
           (equal (clz-c)
                  (- 23 (expo (bits (c) 22 0)))))
  :hints (("Goal"
           :use ((:instance expo-monotone
                            (x 1)
                            (y (bits (c) 22 0)))
                 (:instance expo-monotone
                            (x (bits (c) 22 0))
                            (y (expt 2 23))))
           :in-theory (enable clz-c bvecp))))

(defthm cexp-orig-denorm
  (implies (equal (cdenorm) 1)
           (equal (cexp-orig) 1))
  :hints (("Goal" :in-theory (enable cdenorm cexp-orig))))

(defthmd cexp-rewrite
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (cexp)
                  (- 257 (clz-c))))
  :hints (("Goal"
          :use ((:instance expo-monotone
                           (x 1)
                           (y (bits (c) 22 0)))
                (:instance expo-monotone
                           (x (bits (c) 22 0))
                           (y (expt 2 23))))
          :in-theory (e/d (adj-cond-p
                           numeric-a-b-p
                           anan
                           ainf
                           bnan
                           binf
                           cdenorm
                           abexp
                           cexp
                           c-scale
                           scale128
                           bvecp
                           clz-c-rewrite
                           p-=-0)
                          (bits-tail-gen)))))

(defthmd-nl cmant-cmant-orig-rel-1
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (cmant)
                  (* (cmant-orig)
                     (expt 2 (+ 24 (clz-c))))))
  :hints (("Goal"
          :expand ((:free (y1 y2 n)
                          (cat 1 1 (* y1 y2) n))
                   (:free (x1 x2 m y n)
                          (cat (* x1 x2) m y n)))
          :use ((:instance expo-lower-bound
                           (x (bits (c) 22 0)))
                (:instance expo-upper-bound
                           (x (bits (c) 22 0)))
                (:instance expo-monotone
                           (x 1)
                           (y (bits (c) 22 0)))
                (:instance expo-monotone
                           (x (bits (c) 22 0))
                           (y (expt 2 23))))
          :in-theory (e/d (adj-cond-p
                           numeric-a-b-p
                           anan
                           ainf
                           bnan
                           binf
                           cdenorm
                           abexp
                           cmant
                           cmant-orig
                           c-scale
                           scale128
                           bvecp
                           clz-c-rewrite
                           bits-tail-sub-1
                           p-=-0)
                          (bits-tail-gen)))))

(defthmd c-tilde-cval-rel-1
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (equal (c-tilde)
                  (* (expt 2 128) (cval))))
  :hints (("Goal"
           :in-theory (enable adj-cond-p
                              c-tilde
                              cval-rewrite
                              csign-=-csign-orig
                              cexp-rewrite
                              cmant-cmant-orig-rel-1))))

(defthmd cexp-cexp-orig-rel-1
  (implies (not (adj-cond-p))
           (equal (cexp)
                  (if (equal (bits (c) 30 23) 0)
                      (+ 127 (cexp-orig))
                    (+ 128 (cexp-orig)))))
  :hints (("Goal" :in-theory (enable adj-cond-p
                                     cexp
                                     cexp-orig
                                     cdenorm
                                     abexp
                                     c-scale
                                     scale128
                                     bvecp
                                     p-=-0))))

(defthmd cmant-cmant-orig-rel-2
  (implies (not (adj-cond-p))
           (equal (cmant)
                  (if (equal (bits (c) 30 23) 0)
                      (* (cmant-orig) (expt 2 25))
                    (* (cmant-orig) (expt 2 24)))))
  :hints (("Goal" :in-theory (enable adj-cond-p
                                     cmant
                                     cmant-orig
                                     cdenorm
                                     abexp
                                     c-scale
                                     scale128
                                     bvecp
                                     cat
                                     p-=-0))))

(defthmd c-tilde-cval-rel-2
  (implies (not (adj-cond-p))
           (equal (c-tilde) (cval)))
  :hints (("Goal"
           :in-theory (enable c-tilde
                              cval-rewrite
                              csign-=-csign-orig
                              cexp-cexp-orig-rel-1
                              cmant-cmant-orig-rel-2))))

(defthmd-nl s-s-tilde-rel-1
  (implies (numeric-a-b-p)
           (equal (equal (s-tilde) 0)
                  (equal (s) 0)))
  :hints (("Goal"
           :use (p-tilde-p-rel-1
                 p-tilde-p-rel-2
                 c-tilde-cval-rel-1
                 c-tilde-cval-rel-2)
           :in-theory (enable s
                              s-tilde))))

(defthmd s-s-tilde-rel-2
  (implies (numeric-a-b-p)
           (equal (< 0 (s-tilde))
                  (< 0 (s))))
  :hints (("Goal"
           :use (p-tilde-p-rel-1
                 p-tilde-p-rel-2
                 c-tilde-cval-rel-1
                 c-tilde-cval-rel-2)
           :in-theory (enable s s-tilde))))

(defthm-nl s-s-tilde-rel-3
  (implies (and (numeric-a-b-p)
                (equal (scaleop) 1)
                (< (si (d) 32) -512))
           (<= (abs (s))
               (abs (s-tilde))))
  :hints (("Goal"
           :in-theory (enable s
                              s-tilde
                              p-rewrite
                              p-tilde
                              pexp-rexp-rel-2
                              c-tilde-cval-rel-2
                              adj-cond-p)))
  :rule-classes :linear)

(local
 (defthmd aux-1
   (implies (and (<= 0 x)
                 (rationalp x)
                 (posp y))
            (<= x (* x y)))
   :rule-classes :linear))

(local
 (defthmd-nl aux-2
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (integerp x)
                 (integerp y)
                 (<= k i)
                 (<= k j)
                 (not (equal (+ (* (expt 2 i) x)
                                (* (expt 2 j) y))
                             0)))
            (<= (expt 2 k)
                (abs (+ (* (expt 2 i) x)
                        (* (expt 2 j) y)))))
   :hints (("Goal"
            :use (:instance aux-1
                            (x (expt 2 k))
                            (y (abs (+ (* (expt 2 (- i k))
                                          x)
                                       (* (expt 2 (- j k))
                                          y)))))))
   :rule-classes :linear))

(defthm-nl abs-s-lower-bound-1
  (implies (and (numeric-a-b-p)
                (not (equal (s) 0))
                (equal (scaleop) 1)
                (< 511 (si (d) 32)))
           (< (* 2 (lpn (sp)))
              (abs (s))))
  :hints (("Goal"
           :use (:instance aux-2
                           (x (* (if (equal (psign) 0) 1 -1)
                                 (pmant)))
                           (y (* (if (equal (csign-orig) 0) 1 -1)
                                 (cmant-orig)))
                           (i (- (rexp) 302))
                           (j (- (cexp-orig) 150))
                           (k -302))
           :in-theory (e/d (s
                            p-rewrite
                            cval-rewrite
                            sp)
                           ())))
  :rule-classes :linear)

(defthm abs-s-tilde-lower-bound-1
  (implies (and (numeric-a-b-p)
                (not (equal (s) 0))
                (equal (scaleop) 1)
                (< 511 (si (d) 32)))
           (< (* 2 (lpn (sp)))
              (abs (s-tilde))))
  :hints (("Goal"
           :use s-s-tilde-rel-1
           :in-theory (e/d (acl2::scatter-exponents-theory
                            s-tilde
                            p-tilde
                            c-tilde
                            sp)
                           (acl2::gather-exponents-theory))))
  :rule-classes :linear)

(defthm abs-c-tilde-upper-bound
  (implies (and (numeric-c-p)
                (< (si (d) 32) 16))
           (<= (abs (c-tilde))
               (lpn (sp))))
  :hints (("Goal" :in-theory (enable c-tilde-cval-rel-2
                                     adj-cond-p)))
  :rule-classes :linear)

(defthm-nl abs-s-tilde-upper-bound-1
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (equal (scaleop) 1)
                (< (si (d) 32) -512))
           (< (abs (s-tilde))
              (/ (spd (sp))
                 2)))
  :hints (("Goal"
           :use (abs-c-tilde-upper-bound
                 rexp-bounds)
           :in-theory (e/d (s-tilde
                            p-tilde
                            pexp-rexp-rel-2
                            adj-cond-p
                            sp)
                           (abs-c-tilde-upper-bound
                            rexp-bounds))))
  :rule-classes :linear)

(defthm abs-s-upper-bound-1
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (equal (scaleop) 1)
                (< (si (d) 32) -512))
           (< (abs (s))
              (/ (spd (sp))
                 2)))
  :hints (("Goal"
           :use (s-s-tilde-rel-3
                 abs-s-tilde-upper-bound-1)))
  :rule-classes :linear)

(defthmd s-tilde-=-s-1
  (implies (and (numeric-a-b-p)
                (or (equal (scaleop) 0)
                    (and (<= -512 (si (d) 32))
                         (<= (si (d) 32) 511))))
           (equal (s-tilde) (s)))
  :hints (("Goal"
           :use ((:instance si-bits
                            (x (- (si (d) 32) 128))
                            (n 10))
                 (:instance si-bits
                            (x (si (d) 32))
                            (n 10)))
           :in-theory (enable s
                              s-tilde
                              scale-lemma-4
                              p-tilde-p-rel-1
                              p-tilde-p-rel-2
                              c-tilde-cval-rel-1
                              c-tilde-cval-rel-2
                              adj-cond-p))))

(local
 (defthm c-scale-adj-exp-lower-bound
   (implies (and (adj-cond-p)
                 (numeric-a-b-p))
            (< 0 (bits (c-scale) 30 23)))
   :hints (("Goal" :in-theory (e/d (adj-cond-p
                                    numeric-a-b-p
                                    anan
                                    ainf
                                    bnan
                                    binf
                                    cdenorm
                                    abexp
                                    c-scale
                                    scale128
                                    bvecp
                                    clz-c-rewrite
                                    p-=-0)
                                   (bits-tail-gen))))
   :rule-classes :linear))

(defthm adj-cmant-low-bound
  (implies (and (adj-cond-p)
                (numeric-a-b-p))
           (<= (expt 2 47) (cmant)))
  :hints (("Goal" :in-theory (enable cmant cat bvecp)))
  :rule-classes :linear)

(local
 (defthm rexp-abexp-rel-3
   (implies (and (numeric-a-b-p)
                 (< 4 (rexp)))
            (<= (rexp) (+ 3 (abexp))))
   :hints (("Goal"
            :in-theory (enable numeric-a-b-p
                               rexp
                               abexp
                               anan
                               ainf
                               bnan
                               binf
                               bvecp
                               fmul32)))
   :rule-classes :linear))

(defthm cdenorm-=-1
 (implies (and (< 0 (cmant))
               (< (cmant) (expt 2 47)))
          (equal (cdenorm) 1))
 :hints (("Goal" :in-theory (enable cmant
                                    cdenorm
                                    c-scale
                                    scale128
                                    bvecp
                                    cat))))

(defthm scale-prop
  (implies (and (numeric-a-b-p)
                (< 0 (cmant))
                (< (cmant) (expt 2 47))
                (<= 67 (pexp))
                (<= (pexp) 257))
           (< (si (scale) 10) 16))
  :hints (("Goal"
           :cases ((equal (scaleop) 0)
                   (equal (scaleop) 1))
           :use (rexp-abexp-rel-1
                 scale-lemma-4
                 pexp-rexp-rel-1
                 pexp-rexp-rel-2
                 (:instance si-bits
                            (x (si (d) 32))
                            (n 10)))
           :in-theory (e/d (p-rewrite
                            adj-cond-p)
                           (rexp-abexp-rel-1))))
  :rule-classes :linear)

(defthm pexp-=-0
  (implies (and (numeric-a-b-p)
                (equal (pmant) 0))
           (equal (pexp) 0))
  :hints (("Goal"
           :use (pexp-rexp-rel-1
                 pexp-rexp-rel-2)
           :in-theory (enable p-rewrite
                              adj-cond-p))))

(defthm pexp-bounds
  (implies (and (numeric-a-b-p)
                (< 0 (pmant)))
           (and (<= 4 (pexp))
                (<= (pexp) 510)))
  :hints (("Goal"
           :use (rexp-bounds
                 pexp-rexp-rel-1
                 pexp-rexp-rel-2)
           :in-theory (e/d (p-rewrite
                            adj-cond-p)
                           (rexp-bounds))))
  :rule-classes :linear)

(local
 (defthm-nl abexp-=-0
   (implies (and (< 0 (pmant))
                 (< (pmant) (expt 2 23)))
            (equal (abexp) 0))
   :hints (("Goal"
            :use ((:instance bits-plus-bits (x (a))
                             (m 0)
                             (p 23)
                             (n 30))
                  (:instance bits-plus-bits (x (b))
                             (m 0)
                             (p 23)
                             (n 30)))
            :in-theory (enable abexp
                               pmant
                               bvecp
                               cat
                               fmul32)))))

(defthm pexp-=-4
  (implies (and (numeric-a-b-p)
                (< 0 (pmant))
                (< (pmant) (expt 2 23)))
           (equal (pexp) 4))
  :hints (("Goal"
           :use (pexp-rexp-rel-1
                 pexp-rexp-rel-2)
           :in-theory (enable adj-cond-p))))

(defthm integerp-cmant>>24
  (integerp (* 1/16777216 (cmant)))
  :hints (("Goal" :in-theory (enable cmant bvecp cat)))
  :rule-classes :type-prescription)

(defthm cexp-=-128
  (implies (< (cmant) (expt 2 47))
           (equal (cexp) 128))
  :hints (("Goal" :in-theory (enable cexp cmant bvecp cat))))

(defthm cmant-lower-bound
  (implies (< 0 (cmant))
           (<= (expt 2 25) (cmant)))
  :hints (("Goal" :in-theory (enable cmant bvecp cat)))
  :rule-classes :linear)

;; ======================================================================

(defundd elarge ()
  (if (equal (clarger) 0)
      (pexp)
    (cexp)))

(defundd esmall ()
  (if (equal (clarger) 0)
      (cexp)
    (pexp)))

(defundd mlarge ()
  (if (equal (clarger) 0)
      (pmant)
    (cmant)))

(defundd msmall ()
  (if (equal (clarger) 0)
      (cmant)
    (pmant)))

(defundd ediff ()
  (- (elarge) (esmall)))

(defundd fi ()
  (if (equal (sub) 0)
      (* 4 (+ (mlarge)
              (* (msmall) (expt 2 (- (ediff))))))
    (abs (* 4 (- (mlarge)
                 (* (msmall) (expt 2 (- (ediff)))))))))

(bvecthm bvecp52-add1
  (bvecp (add1) 52)
  :hints (("Goal" :in-theory (enable add1 computeaddends))))

(bvecthm bvecp52-add2
  (bvecp (add2) 52)
  :hints (("Goal" :in-theory (enable add2 computeaddends))))

(defthm pzero-pmant-rel
  (implies (numeric-a-b-p)
           (equal (equal (pzero) 0)
                  (not (equal (pmant) 0))))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm czero-cmant-rel
  (equal (equal (czero) 0)
         (not (equal (cmant) 0)))
  :hints (("Goal"
           :use (:instance bits-plus-bits (x (c-scale))
                           (m 0)
                           (p 23)
                           (n 30))
           :in-theory (enable czero
                              cmant
                              bvecp
                              cat))))

(defthmd-nl add1-rewrite
  (implies (numeric-a-b-p)
           (equal (add1)
                  (+ (expt 2 51)
                     (fl (* (msmall)
                            (expt 2 (- 2 (ediff))))))))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (e/d (add1
                            msmall
                            ediff
                            elarge
                            esmall
                            clarger
                            bvecp
                            cat
                            bits-lognot
                            computeaddends)
                           (log<>
                            pexp-bounds)))
          ("Subgoal 4"
           :use ((:instance expt-lemma-6
                            (x (pmant))
                            (r 2)
                            (i (+ 2 (pexp) (- (cexp)))))
                 (:instance bits-fl-diff-alt
                            (x (* (pmant)
                                  (expt 2 (+ 65 (pexp) (- (cexp))))))
                            (i 112)
                            (j 63))
                 (:instance fl-unique
                            (x (* (pmant)
                                  (expt 2 (+ -48 (pexp) (- (cexp))))))
                            (n 0))))
          ("Subgoal 2"
           :use ((:instance expt-lemma-6
                            (x (cmant))
                            (r 2)
                            (i (+ 2 (cexp) (- (pexp)))))
                 (:instance expt-lemma-6
                            (x (cmant))
                            (r 2)
                            (i (+ -48 (cexp) (- (pexp)))))
                 (:instance bits-fl-diff-alt
                            (x (* (cmant)
                                  (expt 2 (+ 65 (cexp) (- (pexp))))))
                            (i 112)
                            (j 63))
                 (:instance n<=fl-linear
                            (x (* (cmant)
                                  (expt 2 (+ -48 (cexp) (- (pexp))))))
                            (n 1))
                 (:instance fl-unique
                            (x (* (cmant)
                                  (expt 2 (+ -48 (cexp) (- (pexp))))))
                            (n 0))))))

(local
 (defthmd aux-3
   (implies (and (<= x y)
                 (< 0 x)
                 (< y 1))
            (not (integerp x)))))

(defthmd inx-0
  (implies (numeric-a-b-p)
           (equal (equal (inx) 0)
                  (integerp (* (msmall)
                               (expt 2 (- 2 (ediff)))))))
  :hints (("Goal"
           :use ((:instance aux-3
                            (x (* (pmant)
                                  (expt 2 (+ 2 (- (cexp)) (pexp)))))
                            (y (* (pmant)
                                  (expt 2 -62))))
                 (:instance aux-3
                            (x (* (cmant)
                                  (expt 2 (+ 2 (cexp) (- (pexp))))))
                            (y (* (cmant)
                                  (expt 2 -62))))
                 (:instance exact-bits-3
                            (x (if (<= (pexp) (cexp))
                                   (* (pmant)
                                      (expt 2 (+ 65 (- (cexp)) (pexp))))
                                 (* (cmant)
                                    (expt 2 (+ 65 (cexp) (- (pexp)))))))
                            (k 63)))
           :in-theory (e/d (inx
                            msmall
                            ediff
                            elarge
                            esmall
                            clarger
                            bvecp
                            cat
                            bits-lognot
                            computeaddends)
                           ()))))

(defthmd add2-rewrite
  (equal (add2)
         (if (equal (sub) 0)
             (+ (expt 2 51)
                (* 4 (mlarge)))
           (+ (expt 2 51)
              (- (* 4 (mlarge)))
              -1)))
  :hints (("Goal"
           :in-theory (e/d (add2
                            mlarge
                            bvecp
                            cat
                            bits-lognot
                            computeaddends)
                           ()))))

(defthm add1+add2-lower-bound
  (implies (and (numeric-a-b-p)
                (equal (sub) 0)
                (not-both-p&c-zeros-p))
           (< (expt 2 52)
              (+ (add1) (add2))))
  :hints (("Goal" :in-theory (enable not-both-p&c-zeros-p
                                     add1-rewrite
                                     add2-rewrite
                                     clarger
                                     mlarge
                                     msmall)))
  :rule-classes :linear)

(local
 (defthm-nl aux-4
   (implies (and (< a x)
                 (<= b y)
                 (<= 0 a)
                 (< 0 b)
                 (rationalp a)
                 (rationalp x))
            (< (* a b) (* x y)))
   :rule-classes nil))

(defthm-nl add1+add2-upper-bound
  (implies (and (numeric-a-b-p)
                (equal (sub) 0))
           (< (+ (add1) (add2))
              (+ (expt 2 52) (expt 2 51))))
  :hints (("Goal"
           :use (:instance aux-4
                           (a (if (<= (pexp) (cexp))
                                  (pmant)
                                (cmant)))
                           (b (if (<= (pexp) (cexp))
                                  (expt 2 (+ 2 (- (cexp)) (pexp)))
                                (expt 2 (+ 2 (cexp) (- (pexp))))))
                           (x (expt 2 48))
                           (y 4))
           :in-theory (enable add1-rewrite
                              add2-rewrite
                              clarger
                              ediff
                              elarge
                              esmall
                              mlarge
                              msmall)))
  :rule-classes :linear)

(defthm add1-add2-lower-bound
  (implies (and (numeric-a-b-p)
                (equal (sub) 1))
           (< (+ (expt 2 51) (expt 2 50))
              (+ (add1) (add2))))
  :hints (("Goal" :in-theory (enable add1-rewrite
                                     add2-rewrite
                                     clarger
                                     mlarge
                                     msmall)))
  :rule-classes :linear)

(defthm-nl add1-add2-upper-bound
  (implies (and (numeric-a-b-p)
                (equal (sub) 1))
           (< (+ (add1) (add2))
              (+ (expt 2 52) (expt 2 50))))
  :hints (("Goal"
           :use (:instance aux-4
                           (a (if (<= (pexp) (cexp))
                                  (pmant)
                                (cmant)))
                           (b (if (<= (pexp) (cexp))
                                  (expt 2 (+ 2 (- (cexp)) (pexp)))
                                (expt 2 (+ 2 (cexp) (- (pexp))))))
                           (x (expt 2 48))
                           (y 4))
           :in-theory (enable add1-rewrite
                              add2-rewrite
                              clarger
                              ediff
                              elarge
                              esmall
                              mlarge
                              msmall)))
  :rule-classes :linear)

(defthmd inx-fi-rel
  (implies (numeric-a-b-p)
           (equal (equal (inx) 0)
                  (integerp (fi))))
  :hints (("Goal" :in-theory (enable inx-0 fi))))

(defthm ediff-lower-bound-when-clarger-is-0
  (implies (and (equal (inx) 1)
                (equal (clarger) 0))
           (<= 27 (ediff)))
  :hints (("Goal"
           :use ((:instance exact-bits-3
                            (x (* (cmant)
                                  (expt 2 (+ 65 (cexp) (- (pexp))))))
                            (k 63))
                 (:instance expt-lemma-2
                            (x (cmant))
                            (i -24)
                            (j (+ 2 (cexp) (- (pexp))))))
           :in-theory (enable inx
                              clarger
                              ediff
                              elarge
                              esmall
                              bvecp
                              cat
                              bits-lognot
                              computeaddends)))
  :rule-classes :linear)

(defthm ediff-lower-bound-when-clarger-is-1
  (implies (and (equal (inx) 1)
                (equal (clarger) 1))
           (<= 3 (ediff)))
  :hints (("Goal"
           :use (:instance exact-bits-3
                           (x (* (pmant)
                                 (expt 2 (+ 65 (- (cexp)) (pexp)))))
                           (k 63))
           :in-theory (enable inx
                              clarger
                              ediff
                              elarge
                              esmall
                              bvecp
                              cat
                              bits-lognot
                              computeaddends)))
  :rule-classes :linear)

(bitthm bitp-psign
  (bitp (psign))
  :hints (("Goal" :in-theory (enable psign-rewrite))))

(bitthm bitp-csign
  (bitp (csign))
  :hints (("Goal" :in-theory (enable csign))))

(defthmd s-tilde-rewrite
  (implies (numeric-a-b-p)
           (equal (s-tilde)
                  (if (equal (sub) 0)
                      (* (if (equal (signlarger) 0) 1 -1)
                         (expt 2 (+ (si (scale) 10)
                                    (elarge)
                                    -302))
                         (+ (mlarge)
                            (* (msmall)
                               (expt 2 (- (ediff))))))
                    (* (if (equal (signlarger) 0) 1 -1)
                       (expt 2 (+ (si (scale) 10)
                                  (elarge)
                                  -302))
                       (- (mlarge)
                          (* (msmall)
                             (expt 2 (- (ediff)))))))))
  :hints (("Goal" :in-theory (e/d (s-tilde
                                   signlarger
                                   clarger
                                   p-tilde
                                   c-tilde
                                   ediff
                                   elarge
                                   esmall
                                   mlarge
                                   msmall
                                   sub)
                                  ()))))

(defthmd abs-s-tilde-rewrite-1
  (implies (numeric-a-b-p)
           (equal (abs (s-tilde))
                  (* (fi)
                     (expt 2 (+ (si (scale) 10) (elarge) -304)))))
  :hints (("Goal" :in-theory (enable s-tilde-rewrite fi))))

(defthmd s-tilde-signlarger-rel-1
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (sub) 0))
           (equal (< 0 (s-tilde))
                  (equal (signlarger) 0)))
  :hints (("Goal" :in-theory (enable not-both-p&c-zeros-p
                                     mlarge
                                     msmall
                                     s-tilde-rewrite))))

(defthmd s-tilde-signlarger-rel-2
  (implies (and (equal (sub) 1)
                (< (* (msmall) (expt 2 (- (ediff))))
                   (mlarge)))
           (equal (< 0 (s-tilde))
                  (equal (signlarger) 0)))
  :hints (("Goal"
           :in-theory (e/d (acl2::scatter-exponents-theory
                            acl2::prefer-positive-exponents-scatter-exponents-theory
                            s-tilde
                            sub
                            ediff
                            elarge
                            esmall
                            mlarge
                            msmall
                            signlarger
                            p-tilde
                            c-tilde
                            clarger)
                           (acl2::gather-exponents-theory)))))

(defthmd s-tilde-signlarger-rel-3
  (implies (and (equal (sub) 1)
                (< (mlarge)
                   (* (msmall) (expt 2 (- (ediff))))))
           (equal (< 0 (s-tilde))
                  (equal (signlarger) 1)))
  :hints (("Goal"
           :in-theory (e/d (acl2::scatter-exponents-theory
                            acl2::prefer-positive-exponents-scatter-exponents-theory
                            s-tilde
                            sub
                            ediff
                            elarge
                            esmall
                            mlarge
                            msmall
                            signlarger
                            p-tilde
                            c-tilde
                            clarger)
                           (acl2::gather-exponents-theory)))))
