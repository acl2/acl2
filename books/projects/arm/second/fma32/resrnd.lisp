;; Cuong Chau <cuong.chau@arm.com>

;; July 2021

;; The events in this book are derived from the hand proofs developed by David
;; Russinoff <david.russinoff@arm.com>.

(in-package "RTL")

(include-book "sumshft")

(local (arith-5-for-rtl))

;; ======================================================================

(defund rmode-prime (mode sign)
  (declare (xargs :guard (and (symbolp mode)
                              (bitp sign))))
  (cond ((and (equal mode 'RUP)
              (equal sign 1))
         'RDN)
        ((and (equal mode 'RDN)
              (equal sign 1))
         'RUP)
        (t mode)))

(local
 (defthmd aux-1
   (implies (and (<= i x)
                 (< x (1+ i))
                 (integerp i))
            (equal (equal x i)
                   (integerp x)))))

(local
 (defthmd-nl rnd-ext-s-aux-1
   (implies (and (<= 1 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (equal (stk) 0)
                   (integerp (* (expt 2 (- 1047 (omega)))
                                (abs (s))))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  s-tilde-sig&grd-rel-2
                  (:instance aux-1
                             (x (* (expt 2 (- 1047 (omega)))
                                   (abs (s))))
                             (i (sig&grd))))
            :in-theory (e/d (s-tilde-sig&grd-stk-rel
                             s-tilde-=-s-2)
                            (s-tilde-sig&grd-rel-1
                             s-tilde-sig&grd-rel-2
                             abs))))))

(local
 (defthmd-nl rnd-ext-s-aux-2
   (implies (and (<= 1 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (fl (* (expt 2 (- 1047 (omega)))
                          (abs (s))))
                   (sig&grd)))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-1
                  s-tilde-sig&grd-rel-2)
            :in-theory (e/d (s-tilde-=-s-2)
                            (s-tilde-sig&grd-rel-1
                             s-tilde-sig&grd-rel-2
                             abs))))))

(local
 (defthm rtz-sig&grd-rewrite
   (equal (rtz (sig&grd) (expo (sig&grd)))
          (* 2 (bits (sig&grd) 24 1)))
   :hints (("Goal"
            :use (:instance bits-fl-diff
                            (x (sig&grd))
                            (i 25)
                            (j 1))
            :in-theory (enable rtz sgn sig)))))

(defthmd rndinc-rewrite
  (implies (and (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (rndinc)
                  (computeinc (rmode)
                              (ressign-1)
                              (resmant)
                              (grd)
                              (stk))))
  :hints (("Goal"
           :use pexp-bounds
           :in-theory (enable numeric-a-b-p
                              numeric-c-p
                              not-both-p&c-zeros-p
                              pnan
                              pinf
                              resmant-rewrite
                              rndinc))))

(local
 (defthm rnd-ext-s-aux-3
   (implies (<= 2 (sig&grd))
            (<= 1 (expo (sig&grd))))
   :hints (("Goal" :use (:instance expo-monotone
                                   (x 2)
                                   (y (sig&grd)))))
   :rule-classes :linear))

(local
 (defthm rnd-ext-s-aux-4
   (equal (expo (* 2 (bits (sig&grd) 24 1)))
          (expo (sig&grd)))
   :hints (("Goal"
            :cases ((equal (sig&grd) 0)
                    (equal (sig&grd) 1))
            :in-theory (enable expo-shft-preserved)))))

(local
 (defthm bitp-ressign-1-aux
   (implies (bitp x)
            (equal (integerp (* 1/2 x))
                   (equal x 0)))))

(bitthm bitp-ressign-1
        (bitp (ressign-1))
        :hints (("Goal" :in-theory (enable ressign-1
                                           signlarger
                                           togglesign
                                           gout
                                           gin
                                           pin
                                           computesum))))

(local
 (defthmd rnd-ext-s-aux-5
   (implies (and (<= 1 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (<= (expt 2 (expo (sig&grd)))
                (* (expt 2 (- 1047 (omega)))
                   (abs (s)))))
   :hints (("Goal"
            :use (rnd-ext-s-aux-2
                  (:instance expo-fl
                             (x (* (expt 2 (- 1047 (omega)))
                                   (abs (s))))))
            :in-theory (e/d (acl2::scatter-exponents-theory
                             expo-lower-bound)
                            (acl2::gather-exponents-theory
                             expo-fl))))
   :rule-classes :linear))

(local
 (defthmd rnd-ext-s-aux-6
   (implies (and (ext-mode-p
                  (rmode-prime (decode-fma-rmode (rmode))
                               (ressign-1)))
                 (<= 2 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (rnd-ext (abs (s))
                            (rmode-prime (decode-fma-rmode (rmode))
                                         (ressign-1))
                            (expo (sig&grd)))
                   (* (expt 2 (- (omega) 1046))
                      (+ (bits (sig&grd) 24 1) (rndinc)))))
   :hints (("Goal"
            :use (rnd-ext-s-aux-1
                  rnd-ext-s-aux-2
                  rnd-ext-s-aux-5
                  (:instance rnd-ext-shift
                             (x (* (expt 2 (- 1047 (omega)))
                                   (abs (s))))
                             (mode (rmode-prime (decode-fma-rmode (rmode))
                                                (ressign-1)))
                             (k (- (omega) 1047))
                             (n (expo (sig&grd)))))
            :in-theory (e/d (rmode-prime
                             decode-fma-rmode
                             roundup-ext-pos-thm
                             roundup-ext-pos
                             roundup-pos
                             resmant-sig&grd-rel
                             grd-sig&grd-rel
                             bitn-bits
                             rndinc-rewrite
                             computeinc)
                            (abs))))))

(local
 (defthm rnd-ext-s
   (implies (and (ext-mode-p (decode-fma-rmode (rmode)))
                 (<= 2 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (rnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (expo (sig&grd)))
                   (* (if (equal (ressign) 0) 1 -1)
                      (expt 2 (- (omega) 1046))
                      (+ (bits (sig&grd) 24 1) (rndinc)))))
   :hints (("Goal"
            :use (rnd-ext-s-aux-6
                  s-tilde-ressign-1-rel-non-severe)
            :in-theory (enable rmode-prime
                               rnd-ext-minus
                               flip-mode
                               ressign-rewrite
                               s-tilde-=-s-2)))))

(local
 (defthm rnd-ext-s-inst
   (implies (and (equal (bitn (sig&grd) 24) 1)
                 (equal (+ (bits (sig&grd) 23 1) (rndinc))
                        *2^23*)
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (<= 2 (sig&grd))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (equal (rnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (expo (sig&grd)))
                   (* (if (equal (ressign) 0) 1 -1)
                      (expt 2 (- (omega) 1022)))))
   :hints (("Goal"
            :use (:instance bitn-plus-bits
                            (x (sig&grd))
                            (m 1)
                            (n 24))))))

(bitthm bitp-ressign
  (bitp (ressign))
  :hints (("Goal" :in-theory (enable ressign))))

(defthm bitn-ressign
  (equal (bitn (ressign) 0)
         (ressign))
  :hints (("Goal" :in-theory (enable bvecp))))

(bvecthm bvecp23-resmant
  (bvecp (resmant) 23)
  :hints (("Goal"
           :in-theory (enable resmant computeinc))))

(bitthm bitp-rndinc
  (bitp (rndinc))
  :hints (("Goal" :in-theory (enable rndinc grd computeinc))))

(local
 (defthm aux-2
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (and (< (cat (resexp) 8 (resmant) 23)
                    (- *2^31* *2^23*))
                 (< (cat (1+ (resexp))
                         8
                         (+ (resmant) (rndinc))
                         23)
                    *2^31*)))
   :hints (("Goal"
            :use resexp-normal-bounds
            :in-theory (e/d (bvecp cat)
                            (resexp-normal-bounds))))
   :rule-classes :linear))

(local
 (defthm sgnf-resrnd
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (equal (sgnf (resrnd) (sp))
	           (ressign)))
   :hints (("Goal" :in-theory (enable sgnf resrnd res cat-+-1)))))

(local
 (defthm expf-resrnd
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (equal (expf (resrnd) (sp))
                   (if (< (+ (resmant) (rndinc))
                          *2^23*)
                       (resexp)
                     (1+ (resexp)))))
   :hints (("Goal"
            :use resexp-normal-bounds
            :in-theory (e/d (expf
                             resrnd
                             res
                             bvecp
                             cat-+-1
                             cat-+-2)
                            (resexp-normal-bounds))))))

(local
 (defthmd manf-resrnd-aux-1
   (implies (and (< (+ (resmant) (rndinc))
                    *2^23*)
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (equal (manf (resrnd) (sp))
                   (+ (resmant) (rndinc))))
   :hints (("Goal"
            :in-theory (e/d (manf
                             resrnd
                             res
                             bvecp
                             cat-+-1)
                            (cat-associative))))))

(local
 (defthmd manf-resrnd-aux-2
   (implies (and (<= *2^23*
                     (+ (resmant) (rndinc)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (equal (manf (resrnd) (sp))
                   (- (+ (resmant) (rndinc))
                      *2^23*)))
   :hints (("Goal"
            :use (resexp-normal-bounds
                  (:instance bitn-plus-bits
                             (x (+ (resmant) (rndinc)))
                             (m 0)
                             (n 23)))
            :in-theory (e/d (manf
                             resrnd
                             res
                             bvecp
                             bvecp-bitn-1
                             cat-+-1
                             cat-+-2)
                            (resexp-normal-bounds))))))

(defthm resmant+rndinc-upper-bound
  (<= (+ (resmant) (rndinc))
      *2^23*)
  :hints (("Goal" :in-theory (enable resmant
                                     rndinc
                                     grd
                                     cat
                                     computeinc)))
  :rule-classes :linear)

(local
 (defthm manf-resrnd
   (implies (and (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
	    (equal (manf (resrnd) (sp))
                   (if (< (+ (resmant) (rndinc))
                          *2^23*)
                       (+ (resmant) (rndinc))
                     0)))
   :hints (("Goal" :use (manf-resrnd-aux-1 manf-resrnd-aux-2)))))

(defthmd expo-sig&grd-=-24
  (implies (equal (bitn (sig&grd) 24) 1)
           (equal (expo (sig&grd)) 24))
  :hints (("Goal"
           :use (:instance expo-monotone
                           (x (sig&grd))
                           (y (1- (expt 2 25))))
           :in-theory (enable sig&grd))))

(local
 (defthm spd-<-spn-sp
   (< (spd (sp)) (spn (sp)))
   :hints (("Goal" :in-theory (enable sp)))
   :rule-classes :linear))

(local
 (defthmd s-tilde-=-s-3
   (implies (and (<= (spn (sp)) (abs (s)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (and (equal (bitn (sig&grd) 24) 1)
                 (equal (s-tilde) (s))))
   :hints (("Goal"
            :use (s-tilde-=-s-1
                  s-s-tilde-rel-3
                  abs-s-tilde-lower-bound-1
                  s-tilde-sig&grd-rel-3
                  s-tilde-sig&grd-rel-4)
            :in-theory (e/d (s-tilde-=-s-2)
                            (s-s-tilde-rel-3
                             abs-s-tilde-lower-bound-1
                             s-tilde-sig&grd-rel-4))))))

;; Normal rounding

(defthm resrnd-rnd-ext-s-rel-1
  (implies (and (<= (spn (sp)) (abs (s)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (rnd-ext (s)
                           (decode-fma-rmode (rmode))
                           24)
                  (ndecode (resrnd) (sp))))
  :hints (("Goal"
           :use (rnd-ext-s
                 rnd-ext-s-inst
                 s-tilde-sig&grd-rel-4
                 (:instance bitn-plus-bits
                            (x (sig&grd))
                            (m 1)
                            (n 24)))
           :in-theory (e/d (ndecode
                            s-tilde-=-s-3
                            expo-sig&grd-=-24
                            resexp-normal
                            resmant-sig&grd-rel)
                           (rnd-ext-s
                            rnd-ext-s-inst
                            s-tilde-sig&grd-rel-4
                            abs)))))

(bvecthm bvecp32-resrnd
  (bvecp (resrnd) 32)
  :hints (("Goal" :in-theory (enable resrnd))))

(defthm normp-resrnd-1
  (implies (and (<= (abs (rnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  24))
                    (lpn (sp)))
                (<= (spn (sp)) (abs (s)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (normp (resrnd) (sp)))
  :hints (("Goal" :in-theory (enable normp
                                     encodingp
                                     ndecode
                                     s-tilde-=-s-3
                                     lpn-sp))))

(defthmd resrnd-rnd-ext-s-rel-2
  (implies (and (<= (abs (rnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  24))
                    (lpn (sp)))
                (<= (spn (sp)) (abs (s)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (nencode (rnd-ext (s)
                                    (decode-fma-rmode (rmode))
                                    24)
                           (sp)))))

(local
 (def-gl-rule resrnd-rnd-ext-s-rel-3-aux-1
   :hyp (and (<= e 254)
             (bvecp e 8)
             (bvecp m 23))
   :concl (<= (* (expt 2 e)
                 (+ *2^23* m))
              (* (expt 2 150)
                 (lpn (sp))))
   :g-bindings (gl::auto-bindings
                (:nat e 8)
                (:nat m 23))
   :rule-classes :linear))

(local
 (defthm-nl resrnd-rnd-ext-s-rel-3-aux-2
   (implies (and (< x 254)
                 (integerp x))
            (< (expt 2 (+ -126 x))
               (lpn (sp))))
   :hints (("Goal" :in-theory (enable sp)))
   :rule-classes :linear))

(encapsulate
  ()

  (local
   (defthm resrnd-rnd-ext-s-rel-3-aux-3
     (implies (and (< (lpn (sp))
                      (abs (rnd-ext (s)
                                    (decode-fma-rmode (rmode))
                                    24)))
                   (<= (spn (sp)) (abs (s)))
                   (ext-mode-p (decode-fma-rmode (rmode)))
                   (numeric-a-b-p)
                   (numeric-c-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp))
                   (<= (sumexp) (+ 1149 (clzprime))))
              (and (equal (resexp) 254)
                   (equal (rndinc)
                          (- *2^23* (resmant)))))
     :hints (("Goal"
              :use (resexp-normal-bounds
                    (:instance resrnd-rnd-ext-s-rel-3-aux-1
                               (e (resexp))
                               (m (+ (resmant) (rndinc))))
                    (:instance resrnd-rnd-ext-s-rel-3-aux-2
                               (x (resexp))))
              :in-theory (e/d (ndecode bvecp)
                              (resexp-normal-bounds))))))

  (local
   (defthmd resrnd-rnd-ext-s-rel-3-aux-4
     (implies (and (< 0 (rndinc))
                   (ext-mode-p (decode-fma-rmode (rmode)))
                   (numeric-a-b-p)
                   (numeric-c-p)
                   (not-both-p&c-zeros-p)
                   (equal (severe) 0)
                   (<= 896 (sumexp))
                   (<= (sumexp) (+ 1149 (clzprime))))
              (or (and (equal (rmode) 0)
                       (equal (ressign) 0))
                  (and (equal (rmode) 1)
                       (equal (ressign) 1))
                  (equal (rmode) 3)
                  (equal (rmode) 4)
                  (equal (rmode) 5)))
     :hints (("Goal" :in-theory (enable rndinc-rewrite
                                        ressign-rewrite
                                        computeinc)))))

  (defthmd resrnd-rnd-ext-s-rel-3
    (implies (and (< (lpn (sp))
                     (abs (rnd-ext (s)
                                   (decode-fma-rmode (rmode))
                                   24)))
                  (<= (spn (sp)) (abs (s)))
                  (ext-mode-p (decode-fma-rmode (rmode)))
                  (numeric-a-b-p)
                  (numeric-c-p)
                  (not-both-p&c-zeros-p)
                  (equal (severe) 0)
                  (<= 896 (sumexp))
                  (<= (sumexp) (+ 1149 (clzprime))))
             (and (equal (resrnd)
                         (iencode (ressign) (sp)))
                  (or (and (equal (rmode) 0)
                           (equal (ressign) 0))
                      (and (equal (rmode) 1)
                           (equal (ressign) 1))
                      (equal (rmode) 3)
                      (equal (rmode) 4)
                      (equal (rmode) 5))))
    :hints (("Goal"
             :cases ((equal (ressign) 0))
             :use resrnd-rnd-ext-s-rel-3-aux-4
             :in-theory (e/d (resrnd
                              res
                              cat)
                             (resrnd-rnd-ext-s-rel-1
                              abs)))))
  )

;; Subnormal rounding

(local
 (defthmd drnd-ext-abs-s-1
   (implies
    (and (< 0 (abs (s)))
         (< (abs (s))
            (/ (spd (sp)) 2))
         (ext-mode-p
          (rmode-prime (decode-fma-rmode (rmode))
                       (ressign-1))))
    (equal (drnd-ext (abs (s))
                     (rmode-prime (decode-fma-rmode (rmode))
                                  (ressign-1))
                     (sp))
           (if (member (rmode-prime (decode-fma-rmode (rmode))
                                    (ressign-1))
                       '(rup rto))
               (spd (sp))
             0)))
   :hints (("Goal"
            :in-theory (e/d (drnd-ext-tiny-a
                             rmode-prime
                             decode-fma-rmode)
                            (abs))))))

(defthmd drnd-ext-s-1
  (implies (and (< (abs (s))
                   (/ (spd (sp)) 2))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (or (equal (severe) 0)
                    (equal (inx) 1)))
           (equal (drnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (sp))
                  (if (and (equal (ressign) 0)
                           (member (rmode) '(0 5)))
                      (spd (sp))
                    (if (and (equal (ressign) 1)
                             (member (rmode) '(1 5)))
                        (- (spd (sp)))
                      0))))
  :hints (("Goal"
           :use (drnd-ext-abs-s-1
                 nonzero-s-when-inx-is-1
                 nonzero-s-s-tilde
                 s-tilde-ressign-1-rel-severe
                 s-tilde-ressign-1-rel-non-severe)
           :in-theory (e/d (decode-fma-rmode
                            drnd-ext-minus
                            flip-mode
                            ressign-rewrite
                            s-s-tilde-rel-2)
                           (nonzero-s-when-inx-is-1
                            nonzero-s-s-tilde)))))

(local
 (defthmd drnd-ext-abs-s-2
   (implies
    (and (equal (/ (spd (sp)) 2)
                (abs (s)))
         (ext-mode-p
          (rmode-prime (decode-fma-rmode (rmode))
                       (ressign-1))))
    (equal (drnd-ext (abs (s))
                     (rmode-prime (decode-fma-rmode (rmode))
                                  (ressign-1))
                     (sp))
           (if (member (rmode-prime (decode-fma-rmode (rmode))
                                    (ressign-1))
                       '(rup rna rto))
               (spd (sp))
             0)))
   :hints (("Goal"
            :in-theory (e/d (drnd-ext-tiny-b
                             rmode-prime
                             decode-fma-rmode)
                            (abs))))))

(local
 (defthmd drnd-ext-s-2-aux-1
   (implies (and (equal (/ (spd (sp)) 2)
                        (abs (s)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (or (equal (severe) 0)
                     (equal (inx) 1)))
            (equal (drnd-ext (s)
                             (decode-fma-rmode (rmode))
                             (sp))
                   (cond
                    ((and (equal (ressign) 0)
                          (member (rmode) '(0 4 5)))
                     (spd (sp)))
                    ((and (equal (ressign) 1)
                          (member (rmode) '(1 4 5)))
                     (- (spd (sp))))
                    (t 0))))
   :hints (("Goal"
            :use (drnd-ext-abs-s-2
                  s-tilde-ressign-1-rel-severe
                  s-tilde-ressign-1-rel-non-severe)
            :in-theory (e/d (decode-fma-rmode
                             drnd-ext-minus
                             flip-mode
                             ressign-rewrite
                             s-s-tilde-rel-2)
                            ())))))

(local
 (defthmd drnd-ext-abs-s-3
   (implies
    (and (< (/ (spd (sp)) 2)
            (abs (s)))
         (< (abs (s))
            (spd (sp)))
         (ext-mode-p
          (rmode-prime (decode-fma-rmode (rmode))
                       (ressign-1))))
    (equal (drnd-ext (abs (s))
                     (rmode-prime (decode-fma-rmode (rmode))
                                  (ressign-1))
                     (sp))
           (if (member (rmode-prime (decode-fma-rmode (rmode))
                                    (ressign-1))
                       '(rtz rdn))
               0
             (spd (sp)))))
   :hints (("Goal"
            :in-theory (e/d (drnd-ext-tiny-c
                             rmode-prime
                             decode-fma-rmode)
                            (abs))))))

(local
 (defthmd drnd-ext-s-2-aux-2
   (implies (and (< (/ (spd (sp)) 2)
                    (abs (s)))
                 (< (abs (s))
                    (spd (sp)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (or (equal (severe) 0)
                     (equal (inx) 1)))
            (equal (drnd-ext (s)
                             (decode-fma-rmode (rmode))
                             (sp))
                   (cond
                    ((or (and (equal (ressign) 0)
                              (equal (rmode) 1))
                         (and (equal (ressign) 1)
                              (equal (rmode) 0))
                         (equal (rmode) 2))
                     0)
                    ((equal (ressign) 0)
                     (spd (sp)))
                    (t (- (spd (sp)))))))
   :hints (("Goal"
            :use (drnd-ext-abs-s-3
                  s-tilde-ressign-1-rel-severe
                  s-tilde-ressign-1-rel-non-severe)
            :in-theory (e/d (decode-fma-rmode
                             drnd-ext-minus
                             flip-mode
                             ressign-rewrite
                             s-s-tilde-rel-2)
                            ())))))

(defthmd drnd-ext-s-2
  (implies (and (<= (/ (spd (sp)) 2)
                    (abs (s)))
                (< (abs (s)) (spd (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (or (equal (severe) 0)
                    (equal (inx) 1)))
           (equal (drnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (sp))
                  (if (= (/ (spd (sp)) 2)
                         (abs (s)))
                      (cond
                       ((and (equal (ressign) 0)
                             (member (rmode) '(0 4 5)))
                        (spd (sp)))
                       ((and (equal (ressign) 1)
                             (member (rmode) '(1 4 5)))
                        (- (spd (sp))))
                       (t 0))
                    (cond
                     ((or (and (equal (ressign) 0)
                               (equal (rmode) 1))
                          (and (equal (ressign) 1)
                               (equal (rmode) 0))
                          (equal (rmode) 2))
                      0)
                     ((equal (ressign) 0)
                      (spd (sp)))
                     (t (- (spd (sp))))))))
  :hints (("Goal"
           :use (drnd-ext-s-2-aux-1 drnd-ext-s-2-aux-2)
           :in-theory (disable abs))))

(defthmd resrnd-drnd-ext-s-rel-1
  (implies (and (< (abs (s))
                   (/ (spd (sp)) 2))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (drnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (sp))
                  (ddecode (resrnd) (sp))))
  :hints (("Goal"
           :use s-tilde-sig&grd-rel-5
           :in-theory (e/d (drnd-ext-s-1
                            ddecode
                            ressign-rewrite
                            resmant-sig&grd-rel
                            grd-sig&grd-rel
                            rndinc-rewrite
                            s-tilde-sig&grd-stk-rel
                            s-tilde-=-s-2
                            computeinc
                            spd-sp)
                           (abs)))))

(defthmd resrnd-drnd-ext-s-rel-2
  (implies (and (<= (/ (spd (sp)) 2)
                    (abs (s)))
                (< (abs (s)) (spd (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (drnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (sp))
                  (ddecode (resrnd) (sp))))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-4
                 s-tilde-sig&grd-rel-5
                 s-s-tilde-unf)
           :in-theory (e/d (drnd-ext-s-2
                            ddecode
                            ressign-rewrite
                            resmant-sig&grd-rel
                            grd-sig&grd-rel
                            rndinc-rewrite
                            s-tilde-sig&grd-stk-rel
                            s-tilde-=-s-2
                            computeinc
                            spd-sp)
                           (s-s-tilde-unf
                            abs)))))

(local
 (defthm expo-sig&grd-lemma-1
   (<= (* (1+ (sig&grd)) (expt 2 (- (omega) 1047)))
       (expt 2 (+ (expo (sig&grd)) (omega) -1046)))
   :hints (("Goal"
            :in-theory (enable int+1<= expo-upper-bound)))
   :rule-classes :linear))

(local
 (defthm expo-sig&grd-lemma-2
   (<= (* (1+ (sig&grd)) (expt 2 -150))
       (expt 2 (- (expo (sig&grd)) 149)))
   :hints (("Goal"
            :in-theory (enable int+1<= expo-upper-bound)))
   :rule-classes :linear))

(defthmd expo-s-normal-rewrite
  (implies (and (<= (spn (sp)) (abs (s)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (expo (s))
                  (- (resexp) 127)))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-1
                 s-tilde-sig&grd-rel-2
                 s-tilde-sig&grd-rel-3
                 s-s-tilde-unf
                 expo-sig&grd-lemma-1
                 (:instance expo-unique
                            (x (s-tilde))
                            (n (- (resexp) 127)))
                 (:instance expo-monotone
                            (x (* (sig&grd) (expt 2 (- (omega) 1047))))
                            (y (s-tilde))))
           :in-theory (e/d (resexp-normal
                            expo-sig&grd-=-24
                            s-tilde-=-s-2
                            expo-lower-bound
                            spd-sp
                            spn-sp)
                           (s-tilde-sig&grd-rel-1
                            s-tilde-sig&grd-rel-2
                            s-s-tilde-unf
                            expo-sig&grd-lemma-1
                            acl2::simplify-products-gather-exponents-<)))))

(defthmd expo-s-denormal-rewrite
  (implies (and (< (abs (s)) (spn (sp)))
                (not (equal (sig&grd) 0))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (expo (s))
                  (- (expo (sig&grd)) 150)))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-1
                 s-tilde-sig&grd-rel-2
                 s-tilde-sig&grd-rel-3
                 (:instance expo-unique
                            (x (s-tilde))
                            (n (- (expo (sig&grd)) 150)))
                 (:instance expo-monotone
                            (x (* (sig&grd) (expt 2 (- (omega) 1047))))
                            (y (s-tilde))))
           :in-theory (e/d (s-tilde-=-s-2
                            expo-lower-bound)
                           (s-tilde-sig&grd-rel-1
                            s-tilde-sig&grd-rel-2)))))

(defthmd resrnd-drnd-ext-s-rel-3
  (implies (and (< (abs (drnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  (sp)))
                   (spn (sp)))
                (<= (spd (sp)) (abs (s)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (and (not (equal (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp))
                            0))
                (equal (drnd-ext (s)
                                 (decode-fma-rmode (rmode))
                                 (sp))
                       (ddecode (resrnd) (sp)))))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-3
                 s-tilde-sig&grd-rel-4
                 expo-s-denormal-rewrite
                 s-s-tilde-unf
                 s-tilde-ressign-1-rel-non-severe
                 (:instance bits-plus-bitn
                            (x (sig&grd))
                            (m 0)
                            (n 24))
                 (:instance bitn-plus-bits
                            (x (sig&grd))
                            (m 1)
                            (n 24)))
           :in-theory (e/d (drnd-ext
                            ddecode
                            s-tilde-=-s-2
                            ressign-rewrite
                            resmant-sig&grd-rel
                            spn-sp)
                           (s-s-tilde-unf
                            abs)))))

(local
 (defthm resrnd-drnd-ext-s-rel-4-aux
   (implies (and (equal (abs (drnd-ext (s)
                                       (decode-fma-rmode (rmode))
                                       (sp)))
                        (spn (sp)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (<= (spd (sp)) (abs (s))))
   :hints (("Goal" :use (drnd-ext-s-1 drnd-ext-s-2)))
   :rule-classes :linear))

(defthmd resrnd-drnd-ext-s-rel-4
  (implies (and (equal (abs (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp)))
                       (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (drnd-ext (s)
                            (decode-fma-rmode (rmode))
                            (sp))
                  (ndecode (resrnd) (sp))))
  :hints (("Goal"
           :use (s-tilde-sig&grd-rel-3
                 s-tilde-sig&grd-rel-4
                 expo-s-denormal-rewrite
                 s-s-tilde-unf
                 s-tilde-ressign-1-rel-non-severe
                 (:instance bitn-plus-bits
                            (x (sig&grd))
                            (m 1)
                            (n 24)))
           :in-theory (e/d (drnd-ext
                            ndecode
                            s-tilde-=-s-2
                            ressign-rewrite
                            resmant-sig&grd-rel
                            spn-sp)
                           (s-s-tilde-unf)))))

(defthmd resrnd-drnd-ext-s-rel-5
  (implies (and (equal (drnd-ext (s)
                                 (decode-fma-rmode (rmode))
                                 (sp))
                       0)
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (zencode (ressign) (sp))))
  :hints (("Goal"
           :use (resrnd
                 resrnd-drnd-ext-s-rel-1
                 resrnd-drnd-ext-s-rel-2
                 resrnd-drnd-ext-s-rel-3
                 s-tilde-sig&grd-rel-4
                 s-tilde-sig&grd-rel-5)
           :in-theory (e/d (ddecode
                            zencode
                            res
                            resmant-sig&grd-rel
                            s-tilde-=-s-2
                            computeinc)
                           (abs)))))

(defthm denormp-resrnd-1
  (implies (and (not (equal (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp))
                            0))
                (< (abs (drnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  (sp)))
                   (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (denormp (resrnd) (sp)))
  :hints (("Goal"
           :use (resrnd-drnd-ext-s-rel-1
                 resrnd-drnd-ext-s-rel-2
                 resrnd-drnd-ext-s-rel-3
                 s-tilde-sig&grd-rel-3
                 s-tilde-sig&grd-rel-5)
           :in-theory (e/d (denormp
                            encodingp
                            ddecode
                            s-tilde-=-s-2)
                           (abs)))))

(defthmd resrnd-drnd-ext-s-rel-6
  (implies (and (not (equal (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp))
                            0))
                (< (abs (drnd-ext (s)
                                  (decode-fma-rmode (rmode))
                                  (sp)))
                   (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (dencode (drnd-ext (s)
                                     (decode-fma-rmode (rmode))
                                     (sp))
                           (sp))))
  :hints (("Goal"
           :use (resrnd-drnd-ext-s-rel-1
                 resrnd-drnd-ext-s-rel-2
                 resrnd-drnd-ext-s-rel-3)
           :in-theory (disable abs))))

(defthm normp-resrnd-2
  (implies (and (equal (abs (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp)))
                       (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (normp (resrnd) (sp)))
  :hints (("Goal"
           :use (resrnd-drnd-ext-s-rel-4
                 s-tilde-sig&grd-rel-3)
           :in-theory (e/d (normp
                            encodingp
                            ndecode
                            spn-sp)
                           ()))))

(defthmd resrnd-drnd-ext-s-rel-7
  (implies (and (equal (abs (drnd-ext (s)
                                      (decode-fma-rmode (rmode))
                                      (sp)))
                       (spn (sp)))
                (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (equal (resrnd)
                  (nencode (drnd-ext (s)
                                     (decode-fma-rmode (rmode))
                                     (sp))
                           (sp))))
  :hints (("Goal"
           :in-theory (e/d (resrnd-drnd-ext-s-rel-4)
                           (abs)))))

(local
 (defthmd drnd-ext-s-bounds-aux
   (implies (and (<= (spd (sp)) (abs (s)))
                 (< (abs (s)) (spn (sp)))
                 (ext-mode-p (decode-fma-rmode (rmode)))
                 (numeric-a-b-p)
                 (numeric-c-p)
                 (not-both-p&c-zeros-p)
                 (equal (severe) 0)
                 (<= 896 (sumexp))
                 (<= (sumexp) (+ 1149 (clzprime))))
            (<= (abs (drnd-ext (s)
                               (decode-fma-rmode (rmode))
                               (sp)))
                (spn (sp))))
   :hints (("Goal"
            :use (s-tilde-sig&grd-rel-3
                  s-tilde-sig&grd-rel-4
                  expo-s-denormal-rewrite
                  s-s-tilde-unf
                  (:instance bitn-plus-bits
                             (x (sig&grd))
                             (m 1)
                             (n 24)))
            :in-theory (e/d (drnd-ext
                             resmant-sig&grd-rel
                             s-tilde-=-s-2
                             spd-sp
                             spn-sp)
                            (s-s-tilde-unf))))
   :rule-classes :linear))

(defthm drnd-ext-s-bounds
  (implies (and (< (abs (s)) (spn (sp)))
                (ext-mode-p (decode-fma-rmode (rmode)))
                (numeric-a-b-p)
                (numeric-c-p)
                (not-both-p&c-zeros-p)
                (equal (severe) 0)
                (<= 896 (sumexp))
                (<= (sumexp) (+ 1149 (clzprime))))
           (<= (abs (drnd-ext (s)
                              (decode-fma-rmode (rmode))
                              (sp)))
               (spn (sp))))
  :hints (("Goal"
           :use (drnd-ext-s-1
                 drnd-ext-s-2
                 drnd-ext-s-bounds-aux)
           :in-theory (e/d (spd-sp
                            spn-sp)
                           (abs))))
  :rule-classes :linear)

(defthm s-not-denormal
  (implies (and (< (lpn (sp))
                   (abs (rnd-ext (s)
                                 (decode-fma-rmode (rmode))
                                 24)))
                (ext-mode-p (decode-fma-rmode (rmode))))
           (<= (spn (sp)) (abs (s))))
  :hints (("Goal"
           :use ((:instance rnd-ext-monotone
                            (x (s))
                            (y (spn (sp)))
                            (mode (decode-fma-rmode (rmode)))
                            (n 24))
		 (:instance rnd-ext-monotone
                            (x (- (spn (sp))))
                            (y (s))
                            (mode (decode-fma-rmode (rmode)))
                            (n 24)))
           :in-theory (enable decode-fma-rmode
                              spn-sp
                              lpn-sp)))
  :rule-classes :linear)
