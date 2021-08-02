;; Cuong Chau <cuong.chau@arm.com>

;; July 2021

;; The events in this book are derived from the hand proofs developed by David
;; Russinoff <david.russinoff@arm.com>.

(in-package "RTL")

(include-book "lza")
(include-book "sum")

(local (arith-5-for-rtl))

;; ======================================================================

(defundd sumshft-prime ()
  (* (sum) (expt 2 (clzprime))))

(defundd sig&grd ()
  (if (equal (overshft) 0)
      (bits (sumshft) 76 52)
    (bits (sumshft) 77 53)))

(defundd omega ()
  (+ (sumexp) (- (clzprime)) 1))

(defundd vec ()
  (if1 (log<= (sumexp) 971)
       (setbitn (lzaguts (add1) (add2))
                77
                (- 972 (sumexp))
                1)
       (lzaguts (add1) (add2))))

(bvecthm bvecp50-lzaguts
  (bvecp (lzaguts x y) 50)
  :hints (("Goal" :in-theory (enable lzaguts))))

(defthm expo-lzaguts-upper-bound
  (<= (expo (lzaguts x y)) 49)
  :hints (("Goal" :use (:instance expo-monotone
                                  (x (lzaguts x y))
                                  (y (1- (expt 2 50))))))
  :rule-classes :linear)

(local
 (defthmd expo-vec-sumexp-rel
   (implies (and (<= 896 (sumexp))
                 (<= (sumexp) 971)
                 (<= (expo (lzaguts (add1) (add2)))
                     (- 972 (sumexp))))
            (equal (expo (vec))
                   (- 972 (sumexp))))
   :hints (("Goal"
            :in-theory (e/d (vec bvecp)
                            (setbitn))))))

(defthm bitn-add1-51
  (equal (bitn (add1) 51) 1)
  :hints (("Goal" :in-theory (enable add1 computeaddends))))

(defthm bitn-add1-50
  (equal (bitn (add1) 50) 0)
  :hints (("Goal" :in-theory (enable add1 computeaddends))))

(defthm bits-add2-51-&-50
  (equal (bitn (add2) 50)
         (lognot1 (bitn (add2) 51)))
  :hints (("Goal"
           :use (:instance bitn-plus-mult
                           (x (if1 (clarger)
                                   (* 4 (cmant))
                                   (* 4 (pmant))))
                           (k 1)
                           (m 51)
                           (n 50))
           :in-theory (enable add2
                              computeaddends
                              bvecp
                              cat
                              bvecp-bitn-1
                              bits-lognot))))

(local
 (defthm lza-lemma
   (implies (or (< (+ (add1) (add2))
                   (- (expt 2 52) 2))
                (< (expt 2 52)
                   (+ (add1) (add2))))
            (and (< 0 (lzaguts (add1) (add2)))
                 (<= (expo (lzaguts (add1) (add2)))
                     (expo (sum)))
                 (<= (expo (sum))
                     (1+ (expo (lzaguts (add1) (add2)))))))
   :hints (("Goal"
            :cases ((equal (inc) 0))
            :use (gout-add-rel
                  (:instance lza-pos-lemma-gl
                             (x (add1))
                             (y (add2)))
                  (:instance lza-neg-lemma-gl
                             (x (add1))
                             (y (add2))))
            :in-theory (enable sum-rewrite)))
   :rule-classes :linear))

(def-gl-rule bvecp7-clz77
  :hyp (bvecp x 77)
  :concl (bvecp (clz77 x) 7)
  :g-bindings (gl::auto-bindings (:nat x 77)))

(def-gl-rule clz77-expo
  :hyp (and (bvecp x 77)
            (< 0 x))
  :concl (equal (clz77 x) (- 76 (expo x)))
  :g-bindings (gl::auto-bindings (:nat x 77)))

(bvecthm bvecp7-lza
  (bvecp (lza) 7)
  :hints (("Goal" :in-theory (enable lza lzaguts))))

(defthm pos-lza
  (implies (not (equal (overshft) 0))
           (< 0 (lza)))
  :hints (("Goal"
           :use (:instance expo-monotone
                           (x (sum))
                           (y (expt 2 51)))
           :in-theory (enable overshft
                              sumshft)))
  :rule-classes :linear)

(defthmd lza-rewrite
  (implies (not (equal (vec) 0))
           (equal (lza)
                  (- 76 (expo (vec)))))
  :hints (("Goal" :in-theory (enable vec lza lzaguts))))

(defthm lza-props
  (implies (and (< (expo (sum))
                   (- 972 (sumexp)))
                (<= 896 (sumexp)))
           (and (equal (lza) (- (sumexp) 896))
                (<= (lza) (- 76 (expo (sum))))))
  :hints (("Goal"
           :use (lza-lemma
                 lza-rewrite
                 expo-vec-sumexp-rel)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (< (expo (sum))
                     (- 972 (sumexp)))
                  (<= 896 (sumexp)))
             (equal (lza) (- (sumexp) 896))))
   (:linear
    :corollary
    (implies (and (< (expo (sum))
                     (- 972 (sumexp)))
                  (<= 896 (sumexp)))
             (<= (lza) (- 76 (expo (sum))))))))

(defthmd clzprime-props-1
  (implies (and (< (expo (sum))
                   (- 972 (sumexp)))
                (<= 896 (sumexp)))
           (and (equal (clzprime) (- (sumexp) 896))
                (<= (clzprime) (- 76 (expo (sum))))))
  :hints (("Goal"
           :cases ((equal (sum) 0))
           :in-theory (enable clzprime
                              overshft
                              sumshft
                              bvecp
                              bitn-expo-rel-1
                              bitn-bits)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (< (expo (sum))
                     (- 972 (sumexp)))
                  (<= 896 (sumexp)))
             (equal (clzprime) (- (sumexp) 896))))
   (:linear
    :corollary
    (implies (and (< (expo (sum))
                     (- 972 (sumexp)))
                  (<= 896 (sumexp)))
             (<= (clzprime) (- 76 (expo (sum))))))))

(defthm omega-=-897
  (implies (and (< (expo (sum))
                   (- 972 (sumexp)))
                (<= 896 (sumexp)))
           (equal (omega) 897))
  :hints (("Goal" :in-theory (enable omega clzprime-props-1))))

(encapsulate
  ()

  (local
   (defthm clzprime-props-2-aux-1
     (implies (or (equal (+ (add1) (add2))
                         (- (expt 2 52) 2))
                  (equal (+ (add1) (add2))
                         (expt 2 52)))
              (<= (sum) 1))
     :hints (("Goal"
              :cases ((equal (inc) 0))
              :use gout-add-rel
              :in-theory (enable sum-rewrite)))
     :rule-classes :linear))

  (local
   (defthm clzprime-props-2-aux-2
     (implies (and (equal (severe) 0)
                   (<= (- (expt 2 52) 2)
                       (+ (add1) (add2)))
                   (<= (+ (add1) (add2))
                       (expt 2 52)))
              (<= (sum) 1))
     :hints (("Goal"
              :use (pout-add-rel
                    clzprime-props-2-aux-1)
              :in-theory (enable severe
                                 pout
                                 gin
                                 pin
                                 computesum)))
     :rule-classes :linear))

  (local
   (defthm clzprime-props-2-aux-3
     (implies (and (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= (- (expt 2 52) 2)
                       (+ (add1) (add2)))
                   (<= (+ (add1) (add2))
                       (expt 2 52)))
              (< (expo (sum))
                 (- 972 (sumexp))))
     :hints (("Goal"
              :use (sum-lower-bound-non-severe-1
                    sum-lower-bound-non-severe-2
                    (:instance expo-monotone
                               (x (sum))
                               (y 1)))
              :in-theory (e/d (sumexp-rewrite)
                              (sum-lower-bound-non-severe-1
                               sum-lower-bound-non-severe-2))))
     :rule-classes :linear))

  (defthmd clzprime-props-2
    (implies (and (<= (- 972 (sumexp))
                      (expo (sum)))
                  (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp)))
             (equal (clzprime) (- 76 (expo (sum)))))
    :hints (("Goal"
             :use (lza-lemma
                   lza-rewrite
                   expo-vec-sumexp-rel
                   clzprime-props-2-aux-3
                   (:instance expo-shift-alt
                              (x (sum))
                              (n (lza))))
             :in-theory (e/d (clzprime
                              overshft
                              sumshft
                              vec
                              bvecp
                              bitn-expo-rel-1
                              bitn-expo-rel-2
                              bitn-bits)
                             (clzprime-props-2-aux-3
                              expo-shift-alt
                              setbitn)))))

  (local
   (defthm omega-lower-bound-aux
     (implies (and (<= (- 972 (sumexp))
                       (expo (sum)))
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp)))
              (<= 897 (omega)))
     :hints (("Goal" :in-theory (enable omega clzprime-props-2)))
     :rule-classes :linear))

  (defthm omega-lower-bound
    (implies (and (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp)))
             (<= 897 (omega)))
    :hints (("Goal" :use omega-lower-bound-aux))
    :rule-classes :linear)

  (defthm omega-upper-bound
    (implies (<= (sumexp) (+ 1149 (clzprime)))
             (<= (omega) 1150))
    :hints (("Goal" :in-theory (enable omega)))
    :rule-classes :linear)
  )

(bvecthm bvecp7-clzprime
  (bvecp (clzprime) 7)
  :hints (("Goal" :in-theory (enable clzprime))))

(local
 (defthm sum-lower-bound-non-severe-3
   (implies (and (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= (- 972 (sumexp))
                     (expo (sum))))
            (<= 2 (sum)))
   :hints (("Goal"
            :use (sum-lower-bound-non-severe-1
                  sum-lower-bound-non-severe-2
                  (:instance expo-lower-bound
                             (x (sum))))
            :in-theory (e/d (sumexp-rewrite)
                            (sum-lower-bound-non-severe-1
                             sum-lower-bound-non-severe-2))))
   :rule-classes :linear))

(local
 (defthm-nl aux-1
   (implies (and (<= a x)
                 (<= b y)
                 (<= 0 a)
                 (<= 0 b)
                 (rationalp a)
                 (rationalp x))
            (<= (* a b) (* x y)))
   :rule-classes nil))

(defthm abs-s-tilde-lower-bound-2
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (< 1149 (- (sumexp) (clzprime))))
           (<= (expt 2 128)
               (abs (s-tilde))))
  :hints (("Goal"
           :use (clzprime-props-2
                 (:instance aux-1
                            (a (expt 2 (expo (sum))))
                            (b (expt 2 (- 128 (expo (sum)))))
                            (x (sum))
                            (y (expt 2 (- (sumexp) 1098)))))
           :in-theory (enable expo-lower-bound
                              sp)))
  :rule-classes :linear)

(defthm abs-s-lower-bound-2
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (< 1149 (- (sumexp) (clzprime))))
           (<= (expt 2 128)
               (abs (s))))
  :hints (("Goal"
           :use (s-tilde-=-s-1
                 s-s-tilde-rel-1
                 abs-s-lower-bound-1
                 abs-s-tilde-lower-bound-2
                 abs-s-tilde-upper-bound-1)
           :in-theory (e/d (sp)
                           (abs))))
  :rule-classes :linear)

(defthmd ressign-rewrite
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (or (equal (severe) 0)
                    (equal (inx) 1)))
           (equal (ressign) (ressign-1)))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (enable numeric-a-b-p
                              numeric-c-p
                              not-both-p&c-zeros-p
                              pnan
                              pinf
                              ressign))))

(defthmd resexp-rewrite
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resexp)
                  (if1 (logand1 (logand1 (log= (lza) (- (sumexp) 896))
                                         (lognot1 (overshft)))
                                (lognot1 (bitn (sumshft) 76)))
                       (setbitn (resexp-2) 8 0 0)
                       (resexp-2))))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (enable numeric-a-b-p
                              numeric-c-p
                              not-both-p&c-zeros-p
                              pnan
                              pinf
                              resexp))))

(defthmd resmant-rewrite
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resmant)
                  (if1 (overshft)
                       (bits (sumshft) 76 54)
                       (bits (sumshft) 75 53))))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (enable numeric-a-b-p
                              numeric-c-p
                              not-both-p&c-zeros-p
                              pnan
                              pinf
                              resmant))))

(defthm resexp-denormal
  (implies (and (equal (bitn (sig&grd) 24) 0)
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resexp) 0))
  :hints (("Goal"
           :use (clzprime-props-1 clzprime-props-2)
           :in-theory (enable sig&grd
                              resexp-2
                              overshft
                              sumshft
                              clzprime
                              bitn-expo-rel-2
                              bitn-bits
                              resexp-rewrite))))

(defthm omega-denormal
  (implies (and (equal (bitn (sig&grd) 24) 0)
                (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (omega) 897))
  :hints (("Goal"
           :use (clzprime-props-1 clzprime-props-2)
           :in-theory (enable sig&grd
                              overshft
                              sumshft
                              clzprime
                              bitn-expo-rel-2
                              bitn-bits))))

(local
 (defthm aux-2
   (implies (and (<= 897 x)
                 (<= x 1150)
                 (rationalp x))
            (equal (mod x 256)
                   (if (< x 1024)
                       (- x 768)
                     (- x 1024))))))

(encapsulate
  ()

  (local
   (defthm resexp-normal-aux-1
     (implies (and (equal (bitn (+ 1 (- (clzprime)) (sumexp))
                                7)
                          0)
                   (<= (+ 897 (clzprime)) (+ 1 (sumexp)))
                   (<= (sumexp) (+ 1149 (clzprime))))
              (equal (bits (+ 1 (- (clzprime)) (sumexp))
                           6 0)
                     (+ (sumexp) (- (clzprime)) -1023)))
     :hints (("Goal"
              :use ((:instance bitn-plus-bits
                               (x (omega))
                               (m 0)
                               (n 7))
                    (:instance bits-mod
                               (x (omega))
                               (i 7)))
              :in-theory (enable omega)))))

  (local
   (defthm resexp-normal-aux-2
     (implies (and (not (equal (bitn (+ 1 (- (clzprime)) (sumexp))
                                     7)
                               0))
                   (<= (+ 897 (clzprime)) (+ 1 (sumexp)))
                   (<= (sumexp) (+ 1149 (clzprime))))
              (equal (bits (+ 1 (- (clzprime)) (sumexp))
                           6 0)
                     (+ (sumexp) (- (clzprime)) -895)))
     :hints (("Goal"
              :use ((:instance bitn-plus-bits
                               (x (omega))
                               (m 0)
                               (n 7))
                    (:instance bits-mod
                               (x (omega))
                               (i 7)))
              :in-theory (enable omega)))))

  (defthmd resexp-normal
    (implies (and (equal (bitn (sig&grd) 24) 1)
                  (numeric-a-b-p)
                  (numeric-c-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp))
                  (<= (sumexp) (+ 1149 (clzprime))))
             (equal (resexp)
                    (- (omega) 896)))
    :hints (("Goal"
             :use omega-lower-bound
             :in-theory (e/d (sig&grd
                              resexp-2
                              omega
                              bitn-bits
                              bvecp
                              cat
                              resexp-rewrite)
                             (omega-lower-bound)))))

  (defthm resexp-normal-bounds
    (implies (and (equal (bitn (sig&grd) 24) 1)
                  (numeric-a-b-p)
                  (numeric-c-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp))
                  (<= (sumexp) (+ 1149 (clzprime))))
             (and (<= 1 (resexp))
                  (<= (resexp) 254)))
    :hints (("Goal" :in-theory (enable resexp-normal)))
    :rule-classes :linear)
  )

(defthmd resmant-sumshft-prime-rel
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resmant)
                  (bits (sumshft-prime) 75 53)))
  :hints (("Goal"
           :use (:instance bits-shift-up-1-alt
                           (x (* (sum) (expt 2 (+ -1 (lza)))))
                           (k 1)
                           (i 76)
                           (j 54))
           :in-theory (enable resmant-rewrite
                              sumshft-prime
                              sumshft
                              clzprime
                              bvecp))))

(defthmd resmant-sig&grd-rel
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resmant)
                  (bits (sig&grd) 23 1)))
  :hints (("Goal" :in-theory (enable resmant-rewrite sig&grd))))

(defthmd grd-sumshft-prime-rel
  (equal (grd)
         (bitn (sumshft-prime) 52))
  :hints (("Goal"
           :in-theory (enable grd
                              sumshft-prime
                              sumshft
                              clzprime
                              bvecp
                              bitn-shift-up-alt
                              bitn-bits))))

(defthmd grd-sig&grd-rel
  (equal (grd)
         (bitn (sig&grd) 0))
  :hints (("Goal" :in-theory (enable grd sig&grd bitn-bits))))

(defthmd stk-0
  (equal (equal (stk) 0)
         (and (equal (inx)
                     (bits (sumshft-prime) 51 0))
              (equal (inx) 0)))
  :hints (("Goal"
           :use ((:instance bits-shift-up-2-alt
                            (x (* (sum) (expt 2 (+ -1 (lza)))))
                            (k 1)
                            (i 52))
                 (:instance integerp-*
                            (x (sum))
                            (y (expt 2 (+ -1 (lza))))))
           :in-theory (enable stk
                              sumshft-prime
                              sumshft
                              clzprime
                              bvecp))))

(defthm sum-upper-bound
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (< (sum) (expt 2 (- 77 (clzprime)))))
  :hints (("Goal" :use (clzprime-props-1
                        clzprime-props-2
                        (:instance expo-upper-bound
                                   (x (sum))))))
  :rule-classes :linear)

(defthm-nl sumshft-prime-upper-bound-1
  (implies (and (equal (overshft) 0)
                (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (< (* (sum) (expt 2 (lza)))
              (expt 2 77)))
  :hints (("Goal"
           :use sum-upper-bound
           :in-theory (enable clzprime)))
  :rule-classes :linear)

(defthm-nl sumshft-prime-upper-bound-2
  (implies (and (not (equal (overshft) 0))
                (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (< (* (sum) (expt 2 (lza)))
              (expt 2 78)))
  :hints (("Goal"
           :use sum-upper-bound
           :in-theory (enable clzprime bvecp)))
  :rule-classes :linear)

(encapsulate
  ()

  (local
   (defthm-nl++ s-tilde-sig&grd-rel-aux-1
     (implies (and (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp)))
              (and (<= (* (sig&grd) (expt 2 (- (omega) 1047)))
                       (* (sum) (expt 2 (- (sumexp) 1098))))
                   (< (sum)
                      (* (1+ (sig&grd)) (expt 2 (- 52 (clzprime)))))))
     :hints (("Goal"
              :use (sum-upper-bound
                    (:instance bits-plus-bits
                               (x (* (sum) (expt 2 (lza))))
                               (m 0)
                               (n 76)
                               (p 52))
                    (:instance bits-plus-bits
                               (x (* (sum) (expt 2 (lza))))
                               (m 0)
                               (n 77)
                               (p 53)))
              :in-theory (e/d (sig&grd
                               omega
                               clzprime
                               sumshft
                               bvecp)
                              (sum-upper-bound))))
     :rule-classes :linear))

  (defthm s-tilde-sig&grd-rel-1
    (implies (and (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp)))
             (<= (* (sig&grd) (expt 2 (- (omega) 1047)))
                 (abs (s-tilde))))
    :hints (("Goal"
             :use s-tilde-sum-rel
             :in-theory (disable s-tilde-sum-rel
                                 abs)))
    :rule-classes :linear)

  (defthmd s-tilde-sig&grd-stk-rel
    (implies (and (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp)))
             (equal (equal (stk) 0)
                    (equal (* (sig&grd) (expt 2 (- (omega) 1047)))
                           (abs (s-tilde)))))
    :hints (("Goal"
             :use (s-tilde-sum-inx-rel
                   (:instance bits-shift-up-2-alt
                              (x (* (sum) (expt 2 (+ -1 (lza)))))
                              (k 1)
                              (i 52))
                   (:instance integerp-*
                              (x (sum))
                              (y (expt 2 (+ -1 (lza)))))
                   (:instance bits-plus-bits
                              (x (* (sum) (expt 2 (lza))))
                              (m 0)
                              (n 76)
                              (p 52))
                   (:instance bits-plus-bits
                              (x (* (sum) (expt 2 (lza))))
                              (m 0)
                              (n 77)
                              (p 53)))
             :in-theory (e/d (stk-0
                              sig&grd
                              omega
                              clzprime
                              sumshft
                              sumshft-prime
                              bvecp)
                             (abs)))))

  (local
   (defthm s-tilde-sig&grd-rel-aux-2
     (implies (and (<= (clzprime) 52)
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp)))
              (<= (1+ (sum))
                  (* (1+ (sig&grd)) (expt 2 (- 52 (clzprime))))))
     :hints (("Goal" :in-theory (enable int+1<=)))
     :rule-classes :linear))

  (local
   (defthm-nl s-tilde-sig&grd-rel-aux-3
     (implies (and (<= (clzprime) 52)
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp)))
              (< (abs (s-tilde))
                 (* (1+ (sig&grd)) (expt 2 (- (omega) 1047)))))
     :hints (("Goal"
              :use (s-tilde-sum-rel
                    s-tilde-sig&grd-rel-aux-2)
              :in-theory (e/d (omega)
                              (s-tilde-sum-rel
                               s-tilde-sig&grd-rel-aux-2
                               abs))))
     :rule-classes :linear))

  (local
   (defthm s-tilde-sig&grd-rel-aux-4
     (implies (and (equal (stk) 1)
                   (numeric-a-b-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp)))
              (<= (clzprime) 52))
     :hints (("Goal"
              :cases ((< (expo (sum)) 24))
              :use (stk-0
                    clzprime-props-1
                    sum-lower-bound-non-severe-2
                    (:instance expo-monotone
                               (x (expt 2 24))
                               (y (sum))))
              :in-theory (e/d (sumexp-rewrite
                               sumshft-prime
                               clzprime-props-2
                               bits-shift-up-2-alt)
                              (sum-lower-bound-non-severe-2))))
     :rule-classes :linear))

  (defthm s-tilde-sig&grd-rel-2
    (implies (and (numeric-a-b-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp)))
             (< (abs (s-tilde))
                (* (1+ (sig&grd)) (expt 2 (- (omega) 1047)))))
    :hints (("Goal"
             :use (s-tilde-sig&grd-stk-rel
                   s-tilde-sig&grd-rel-aux-3)
             :in-theory (disable abs)))
    :rule-classes :linear)
  )

(defthm-nl s-tilde-normal-upper-bound
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (< (abs (s-tilde))
              (* 2 (lpn (sp)))))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-2
                 omega-upper-bound)
           :in-theory (e/d (sig&grd
                            sp)
                           (s-tilde-sig&grd-rel-2
                            omega-upper-bound
                            abs))))
  :rule-classes :linear)

(bvecthm bvecp25-sig&grd
  (bvecp (sig&grd) 25)
  :hints (("Goal" :in-theory (enable sig&grd))))

(local
 (defthm s-tilde-sig&grd-rel-3-aux-1
   (implies (and (equal (bitn (sig&grd) 24) 0)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde)) (spn (sp))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance bitn-plus-bits
                             (x (sig&grd))
                             (m 0)
                             (n 24)))
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-2
                             abs))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-3-aux-2
   (implies (and (equal (bitn (sig&grd) 24) 1)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (spn (sp)) (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound
                  (:instance bitn-expo-rel-1
                             (x (sig&grd))
                             (n 24))
                  (:instance expo-lower-bound
                             (x (sig&grd))))
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-3
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (spn (sp)) (abs (s-tilde)))
                  (equal (bitn (sig&grd) 24) 1))))

(local
 (defthm s-tilde-sig&grd-rel-4-aux-1
   (implies (and (< (sig&grd) 2)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde)) (spd (sp))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance expo-monotone
                             (x (sig&grd))
                             (y 2)))
            :in-theory (e/d (bitn-expo-rel-1
                             sp)
                            (s-tilde-sig&grd-rel-2))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-4-aux-2
   (implies (and (<= 2 (sig&grd))
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (spd (sp)) (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound)
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound
                             abs))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-4
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (spd (sp)) (abs (s-tilde)))
                  (<= 2 (sig&grd)))))

(local
 (defthm s-tilde-sig&grd-rel-5-aux-1
   (implies (and (< (sig&grd) 1)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde)) (/ (spd (sp)) 2)))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance expo-monotone
                             (x (sig&grd))
                             (y 1)))
            :in-theory (e/d (bitn-expo-rel-1
                             sp)
                            (s-tilde-sig&grd-rel-2))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-5-aux-2
   (implies (and (<= 1 (sig&grd))
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (/ (spd (sp)) 2) (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound)
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound
                             abs))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-5
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (/ (spd (sp)) 2) (abs (s-tilde)))
                  (<= 1 (sig&grd))))
  :hints (("Goal" :use (s-tilde-sig&grd-rel-5-aux-1
                        s-tilde-sig&grd-rel-5-aux-2))))

(local
 (defthm s-tilde-sig&grd-rel-6-aux-1
   (implies (and (< (sig&grd) 4)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde))
               (* 2 (spd (sp)))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance expo-monotone
                             (x (sig&grd))
                             (y 4)))
            :in-theory (e/d (bitn-expo-rel-1
                             sp)
                            (s-tilde-sig&grd-rel-2))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-6-aux-2
   (implies (and (<= 4 (sig&grd))
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (* 2 (spd (sp)))
                (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound)
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound
                             abs))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-6
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (* 2 (spd (sp))) (abs (s-tilde)))
                  (<= 4 (sig&grd)))))

(local
 (defthm s-tilde-sig&grd-rel-7-aux-1
   (implies (and (< (sig&grd) 8)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde))
               (* 4 (spd (sp)))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance expo-monotone
                             (x (sig&grd))
                             (y 8)))
            :in-theory (e/d (bitn-expo-rel-1
                             sp)
                            (s-tilde-sig&grd-rel-2))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-7-aux-2
   (implies (and (<= 8 (sig&grd))
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (* 4 (spd (sp)))
                (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound)
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound
                             abs))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-7
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (* 4 (spd (sp))) (abs (s-tilde)))
                  (<= 8 (sig&grd)))))

(local
 (defthm s-tilde-sig&grd-rel-8-aux-1
   (implies (and (< (sig&grd) 16)
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (< (abs (s-tilde))
               (* 8 (spd (sp)))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-2
                  (:instance expo-monotone
                             (x (sig&grd))
                             (y 16)))
            :in-theory (e/d (bitn-expo-rel-1
                             sp)
                            (s-tilde-sig&grd-rel-2))))
   :rule-classes :linear))

(local
 (defthm-nl s-tilde-sig&grd-rel-8-aux-2
   (implies (and (<= 16 (sig&grd))
                 (numeric-a-b-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp)))
            (<= (* 8 (spd (sp)))
                (abs (s-tilde))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  omega-lower-bound)
            :in-theory (e/d (sp)
                            (s-tilde-sig&grd-rel-1
                             omega-lower-bound
                             abs))))
   :rule-classes :linear))

(defthmd s-tilde-sig&grd-rel-8
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp)))
           (equal (<= (* 8 (spd (sp))) (abs (s-tilde)))
                  (<= 16 (sig&grd)))))

(defthmd s-tilde-=-s-2
  (implies (and (<= 1 (sig&grd))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (s-tilde) (s)))
  :hints (("Goal"
           :use (s-tilde-=-s-1
                 abs-s-tilde-lower-bound-1
                 abs-s-tilde-upper-bound-1
                 s-tilde-sig&grd-rel-5)
           :in-theory (e/d (s-s-tilde-rel-1)
                           (abs-s-tilde-lower-bound-1
                            abs-s-tilde-upper-bound-1
                            abs)))))

(defthm nonzero-s-s-tilde
  (implies (and (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0))
           (and (not (equal (s) 0))
                (not (equal (s-tilde) 0))))
  :hints (("Goal" :use (abs-s-tilde-rewrite-1
                        s-s-tilde-rel-1))))

(defthm s-s-tilde-unf
  (implies (and (equal (sig&grd) 0)
                (numeric-a-b-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (and (< 0 (abs (s)))
                (< 0 (abs (s-tilde)))
                (< (abs (s)) (/ (spd (sp)) 2))
                (< (abs (s-tilde)) (/ (spd (sp)) 2))))
  :hints (("Goal"
           :use (abs-s-tilde-lower-bound-1
                 s-tilde-=-s-1
                 s-s-tilde-rel-3
                 s-tilde-sig&grd-rel-5)
           :in-theory (e/d ()
                           (abs-s-tilde-lower-bound-1))))
  :rule-classes :linear)

