;; Cuong Chau <cuong.chau@arm.com>

;; April 2021

(in-package "RTL")

(include-book "quotient")

(local (arith-5-for-rtl))

;; ======================================================================

;; Formalize the rounding of |a/b| in the normal case:
;; rnd(|a/b|, p) = 2^(1 + si(expq, 13) - bias - p) *
;;                 (2^(p - 1) + qrnd[p-2:0])

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

(defund mode (rmode)
  (declare (xargs :guard (natp rmode)))
  (case rmode
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

(local
 (defundd z* ()
   (cond ((<= (si (expq-1) 13) 1)
          (* (expt 2 (+ (prec (f))
                        (si (expq-1) 13)))
             (/ (x) (d))))
         ((< (x) (d))
          (* (expt 2 (+ 2 (prec (f))))
             (/ (x) (d))))
         (t (* (expt 2 (1+ (prec (f))))
               (/ (x) (d)))))))

(local
 (defthm-nl expo-x/d
   (implies (not (specialp))
            (equal (expo (* (/ (d)) (x)))
                   (if (< (x) (d)) -1 0)))
   :hints (("Goal" :use ((:instance expo-unique
                                    (x (* (/ (d)) (x)))
                                    (n -1))
                         (:instance expo-unique
                                    (x (* (/ (d)) (x)))
                                    (n 0)))))))

(local
 (defthm expo-z*-1
   (implies (and (not (specialp))
                 (< (x) (d)))
            (equal (expo (* (/ (d)) (x) (expt 2 (+ 2 (prec (f))))))
                   (1+ (prec (f)))))
   :hints (("Goal" :use (:instance expo-shift
                                   (x (* (/ (d)) (x)))
                                   (n (+ 2 (prec (f)))))))))

(local
 (defthm expo-z*-2
   (implies (and (not (specialp))
                 (>= (x) (d)))
            (equal (expo (* (/ (d)) (x) (expt 2 (1+ (prec (f))))))
                   (1+ (prec (f)))))
   :hints (("Goal" :use (:instance expo-shift
                                   (x (* (/ (d)) (x)))
                                   (n (1+ (prec (f)))))))))

(local
 (defthm-nl aux-1
   (implies (and (not (specialp))
                 (integerp n))
            (< (expt 2 (1- n))
               (* (/ (d))
                  (x)
                  (expt 2 n))))
   :rule-classes :linear))

(local
 (defthm aux-2
   (implies (and (rationalp x)
                 (integerp i)
                 (posp j))
            (equal (bits (* 2 (fl x)) i j)
                   (bits (* 2 x) i j)))
   :hints (("Goal"
            :use ((:instance bits-shift-up-1
                             (x (fl x))
                             (k 1))
                  (:instance bits-shift-up-1
                             (k 1)))))))

(local
 (defthmd rtz-fl-z*
   (implies (and (or (> (si (expq-1) 13) 1)
                     (and (equal (si (expq-1) 13) 1)
                          (>= (x) (d))))
                 (not (specialp)))
            (equal (rtz (fl (z*)) (prec (f)))
                   (* 4 (bits (qtrunc) (1+ (prec (f))) 2))))
   :hints (("Goal" :in-theory (enable z* qtrunc-rewrite-gen bits-rtz-alt)))))

(bitthm bitp-sign
  (bitp (sign))
  :hints (("Goal" :in-theory (e/d (sign signa signb analyze)
                                  (log=
                                   acl2::default-logxor-1
                                   acl2::default-logxor-2)))))

(local
 (defthm common-mode-p-rmode-prime-rmode
   (common-mode-p (rmode-prime (mode (rmode)) (sign)))
   :hints (("Goal" :in-theory (enable rmode-prime mode)))))

(local
 (defthm expo-shift-insts
   (implies (and (rationalp x)
                 (not (equal x 0)))
            (and (equal (expo (* 2 x))
                        (1+ (expo x)))
                 (equal (expo (* *2^12* x))
                        (+ 12 (expo x)))
                 (equal (expo (* *2^13* x))
                        (+ 13 (expo x)))
                 (equal (expo (* *2^25* x))
                        (+ 25 (expo x)))
                 (equal (expo (* *2^26* x))
                        (+ 26 (expo x)))
                 (equal (expo (* *2^54* x))
                        (+ 54 (expo x)))
                 (equal (expo (* *2^55* x))
                        (+ 55 (expo x)))))
   :hints (("Goal" :use ((:instance expo-shift (n 1))
                         (:instance expo-shift (n 12))
                         (:instance expo-shift (n 13))
                         (:instance expo-shift (n 25))
                         (:instance expo-shift (n 26))
                         (:instance expo-shift (n 54))
                         (:instance expo-shift (n 55)))))))

(local
 (defthmd lsb-rewrite
   (implies (not (specialp))
            (equal (lsb) (bitn (z*) 2)))
   :hints (("Goal" :in-theory (enable lsb z* qtrunc-rewrite-gen bitn-def)))))

(local
 (defthmd grd-rewrite
   (implies (not (specialp))
            (equal (grd) (bitn (z*) 1)))
   :hints (("Goal" :in-theory (enable grd z* qtrunc-rewrite-gen bitn-def)))))

(local
 (defthmd-nl aux-3
   (implies (and (integerp x)
                 (bvecp y 56)
                 (<= *2^55* x)
                 (< x y))
            (and (implies (and (equal (bits x 2 0) 0)
                               (equal (bits y 2 0) 0))
                          (< (bits (* *2^55* (/ y) x)
                                   54 2)
                             (1- *2^53*)))
                 (implies (and (equal (bits x 31 0) 0)
                               (equal (bits y 31 0) 0))
                          (< (bits (* *2^26* (/ y) x)
                                   25 2)
                             (1- *2^24*)))
                 (implies (and (equal (bits x 44 0) 0)
                               (equal (bits y 44 0) 0))
                          (< (bits (* *2^13* (/ y) x)
                                   12 2)
                             (1- *2^11*)))))
   :hints (("Goal" :in-theory (enable bits)))
   :rule-classes :linear))

(local
 (defthmd-nl aux-4
   (implies (and (bvecp x 56)
                 (integerp y)
                 (< *2^55* y)
                 (>= x y))
            (and (implies (and (equal (bits x 2 0) 0)
                               (equal (bits y 2 0) 0))
                          (< (bits (* *2^54* (/ y) x)
                                   54 2)
                             (1- *2^53*)))
                 (implies (and (equal (bits x 31 0) 0)
                               (equal (bits y 31 0) 0))
                          (< (bits (* *2^25* (/ y) x)
                                   25 2)
                             (1- *2^24*)))
                 (implies (and (equal (bits x 44 0) 0)
                               (equal (bits y 44 0) 0))
                          (< (bits (* *2^12* (/ y) x)
                                   12 2)
                             (1- *2^11*)))))
   :hints (("Goal" :in-theory (enable bits)))
   :rule-classes :linear))

(local
 (defthm aux-5
   (implies (and (not (specialp))
                 (< (x) (d)))
            (and (implies (equal (fnum) 3)
                          (< (bits (* *2^55* (/ (d)) (x))
                                   54 2)
                             (1- *2^53*)))
                 (implies (equal (fnum) 2)
                          (< (bits (* *2^26* (/ (d)) (x))
                                   25 2)
                             (1- *2^24*)))
                 (implies (equal (fnum) 1)
                          (< (bits (* *2^13* (/ (d)) (x))
                                   12 2)
                             (1- *2^11*)))))
   :hints (("Goal"
            :use (x57-rewrite
                  d57-rewrite
                  (:instance aux-3
                             (x (x57))
                             (y (d57))))
            :in-theory (enable bits-x57-0 bits-d57-0 f)))
   :rule-classes :linear))

(local
 (defthm aux-6
   (implies (and (not (specialp))
                 (not (equal (d) 1))
                 (>= (x) (d)))
            (and (implies (equal (fnum) 3)
                          (< (bits (* *2^54* (/ (d)) (x))
                                   54 2)
                             (1- *2^53*)))
                 (implies (equal (fnum) 2)
                          (< (bits (* *2^25* (/ (d)) (x))
                                   25 2)
                             (1- *2^24*)))
                 (implies (equal (fnum) 1)
                          (< (bits (* *2^12* (/ (d)) (x))
                                   12 2)
                             (1- *2^11*)))))
   :hints (("Goal"
            :use (x57-rewrite
                  d57-rewrite
                  (:instance aux-4
                             (x (x57))
                             (y (d57))))
            :in-theory (enable bits-x57-0 bits-d57-0 f)))
   :rule-classes :linear))

(local
 (def-gl-rule aux-7-dp
   :hyp (and (bvecp x 55)
             (< (bits x 54 2) (1- *2^53*)))
   :concl (equal (bits (1+ (bits x 54 2))
                       52 0)
                 (1+ (bits x 54 2)))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 55))))

(local
 (def-gl-rule aux-7-sp
   :hyp (and (bvecp x 55)
             (< (bits x 25 2) (1- *2^24*)))
   :concl (equal (bits (1+ (bits x 54 2))
                       23 0)
                 (1+ (bits x 25 2)))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 55))))

(local
 (def-gl-rule aux-7-hp
   :hyp (and (bvecp x 55)
             (< (bits x 12 2) (1- *2^11*)))
   :concl (equal (bits (1+ (bits x 54 2))
                       10 0)
                 (1+ (bits x 12 2)))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 55))))

(local
 (defthm aux-7-dp-inst-1
   (implies (and (not (specialp))
                 (equal (fnum) 3)
                 (< (x) (d)))
            (equal (bits (1+ (bits (* *2^55* (/ (d)) (x))
                                   54 2))
                         52 0)
                   (1+ (bits (* *2^55* (/ (d)) (x))
                             54 2))))
   :hints (("Goal"
            :use (:instance aux-7-dp
                            (x (* 2 (fl (* *2^54* (/ (d)) (x))))))
            :in-theory (enable bvecp)))))

(local
 (defthm aux-7-dp-inst-2
   (implies (and (not (specialp))
                 (equal (fnum) 3)
                 (not (equal (d) 1))
                 (<= (d) (x)))
            (equal (bits (1+ (bits (* *2^54* (/ (d)) (x))
                                   54 2))
                         52 0)
                   (1+ (bits (* *2^54* (/ (d)) (x))
                             54 2))))
   :hints (("Goal"
            :use (:instance aux-7-dp
                            (x (fl (* *2^54* (/ (d)) (x)))))
            :in-theory (enable bvecp)))))

(local
 (defthm-nl aux-7-sp-inst-1
   (implies (and (not (specialp))
                 (equal (fnum) 2)
                 (< (x) (d)))
            (equal (bits (1+ (bits (* *2^26* (/ (d)) (x))
                                   54 2))
                         23 0)
                   (1+ (bits (* *2^26* (/ (d)) (x))
                             25 2))))
   :hints (("Goal"
            :use (:instance aux-7-sp
                            (x (fl (* *2^26* (/ (d)) (x)))))
            :in-theory (enable bvecp)))))

(local
 (defthm-nl aux-7-sp-inst-2
   (implies (and (not (specialp))
                 (equal (fnum) 2)
                 (not (equal (d) 1))
                 (<= (d) (x)))
            (equal (bits (1+ (bits (* *2^25* (/ (d)) (x))
                                   54 2))
                         23 0)
                   (1+ (bits (* *2^25* (/ (d)) (x))
                             25 2))))
   :hints (("Goal"
            :use (:instance aux-7-sp
                            (x (fl (* *2^25* (/ (d)) (x)))))
            :in-theory (enable bvecp)))))

(local
 (defthm-nl aux-7-hp-inst-1
   (implies (and (not (specialp))
                 (equal (fnum) 1)
                 (< (x) (d)))
            (equal (bits (1+ (bits (* *2^13* (/ (d)) (x))
                                   54 2))
                         10 0)
                   (1+ (bits (* *2^13* (/ (d)) (x))
                             12 2))))
   :hints (("Goal"
            :use (:instance aux-7-hp
                            (x (* 2 (fl (* *2^12* (/ (d)) (x))))))
            :in-theory (enable bvecp)))))

(local
 (defthm-nl aux-7-hp-inst-2
   (implies (and (not (specialp))
                 (equal (fnum) 1)
                 (not (equal (d) 1))
                 (<= (d) (x)))
            (equal (bits (1+ (bits (* *2^12* (/ (d)) (x))
                                   54 2))
                         10 0)
                   (1+ (bits (* *2^12* (/ (d)) (x))
                             12 2))))
   :hints (("Goal"
            :use (:instance aux-7-hp
                            (x (fl (* *2^12* (/ (d)) (x)))))
            :in-theory (enable bvecp)))))

(local
 (defthm aux-8
   (equal (equal (bits x 1 0) 0)
          (and (equal (bitn x 1) 0)
               (equal (bitn x 0) 0)))
   :hints (("Goal" :use (:instance bitn-plus-bits
                                   (m 0)
                                   (n 1))))))

(local
 (defthm aux-9
   (and (implies (integerp (* *2^26* x))
                 (equal (bits (* *2^55* x)
                              28 0)
                        0))
        (implies (integerp (* *2^25* x))
                 (equal (bits (* *2^54* x)
                              28 0)
                        0))
        (implies (integerp (* *2^13* x))
                 (equal (bits (* *2^55* x)
                              41 0)
                        0))
        (implies (integerp (* *2^12* x))
                 (equal (bits (* *2^54* x)
                              41 0)
                        0)))
   :hints (("Goal"
            :use ((:instance bits-shift-up-2
                             (x (* *2^26* x))
                             (i -1)
                             (k 29))
                  (:instance bits-shift-up-2
                             (x (* *2^25* x))
                             (i -1)
                             (k 29))
                  (:instance bits-shift-up-2
                             (x (* *2^13* x))
                             (i -1)
                             (k 42))
                  (:instance bits-shift-up-2
                             (x (* *2^12* x))
                             (i -1)
                             (k 42)))))))

(local
 (defthm aux-10-a
   (implies (and (rationalp x)
                 (equal (bits (* *2^55* x)
                              28 0)
                        0))
            (equal (integerp (* *2^27* x))
                   (integerp (* *2^26* x))))
   :hints (("Goal"
            :use (:instance bits-shift-up-2
                            (x (* *2^27* x))
                            (i 0)
                            (k 28))
            :in-theory (e/d (bitn-0-vs-int-/2)
                            (acl2::prefer-positive-addends-<))))))

(local
 (defthm aux-10-b
   (implies (and (rationalp x)
                 (equal (bits (* *2^54* x)
                              28 0)
                        0))
            (equal (integerp (* *2^27* x))
                   (integerp (* *2^25* x))))
   :hints (("Goal"
            :use ((:instance bits-shift-up-2
                             (x (* *2^27* x))
                             (i 1)
                             (k 27))
                  (:instance bits-shift-up-2
                             (x (* *2^26* x))
                             (i 0)
                             (k 28)))
            :in-theory (e/d (bitn-0-vs-int-/2)
                            (acl2::prefer-positive-addends-<))))))

(local
 (defthmd aux-11
   (implies (and (acl2-numberp x)
                 (not (integerp (/ x 2)))
                 (equal (bitn x 0) 0))
            (not (integerp x)))
   :hints (("Goal" :use bitn-integerp-of-fl-rel))))

(local
 (defthm aux-11-inst
   (and (implies (and (not (integerp (* *2^54* x)))
                      (equal (bitn (* *2^55* x) 0)
                             0))
                 (not (integerp (* *2^55* x))))
        (implies (and (not (integerp (* *2^12* x)))
                      (equal (bitn (* *2^13* x) 0)
                             0))
                 (not (integerp (* *2^13* x)))))
   :hints (("Goal" :use ((:instance aux-11
                                    (x (* *2^55* x)))
                         (:instance aux-11
                                    (x (* *2^13* x))))))))

(local
 (defthm expo-x
   (implies (not (specialp))
            (equal (expo (x)) 0))
   :hints (("Goal" :use (:instance expo-unique
                                   (x (x))
                                   (n 0))))))

(local
 (defthmd aux-12
   (implies (not (specialp))
            (and (equal (bitn (* (expt 2 (1+ (prec (f))))
                                 (x))
                              1)
                        0)
                 (equal (bitn (* (expt 2 (1+ (prec (f))))
                                 (x))
                              0)
                        0)))
   :hints (("Goal"
            :use (natp-2^prec-1*x
                  (:instance bitn-shift-up
                             (x (* (expt 2 (1- (prec (f))))
                                   (x)))
                             (k 2)
                             (n -1))
                  (:instance bitn-shift-up
                             (x (* (expt 2 (1- (prec (f))))
                                   (x)))
                             (k 2)
                             (n -2)))))))

(local
 (defthmd rnd-z*-aux-1
   (implies (and (equal (d) 1)
                 (or (> (si (expq-1) 13) 1)
                     (and (equal (si (expq-1) 13) 1)
                          (>= (x) (d))))
                 (not (specialp)))
            (equal (rnd (z*)
                        (rmode-prime (mode (rmode)) (sign))
                        (prec (f)))
                   (* 4 (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (rtz-fl-z*
                  natp-2^prec-1*x
                  aux-12)
            :in-theory (e/d (rmode-prime
                             mode
                             roundup-pos-thm-2
                             z*
                             qrnd
                             f
                             n
                             c
                             qtrunc-rewrite-gen
                             lsb-rewrite
                             grd-rewrite
                             stk-rewrite-gen-3)
                            (acl2::default-expt-2
                             acl2::default-plus-2
                             rnd-non-pos
                             rtz-negative
                             acl2::|(< x (/ y)) with (< 0 y)|
                             acl2::|(<= (/ x) y) with (< 0 x)|
                             acl2::not-integerp-4a
                             acl2::not-integerp-4d
                             acl2::not-integerp-3a
                             acl2::not-integerp-3d
                             acl2::not-integerp-2a
                             acl2::not-integerp-2d
                             acl2::not-integerp-1d
                             acl2::default-times-1
                             acl2::default-times-2
                             acl2::default-less-than-1
                             acl2::default-less-than-2
                             acl2::simplify-products-gather-exponents-<
                             acl2::prefer-positive-addends-<
                             bits-tail-gen))))))

(local
 (defthmd-nl rnd-z*-aux-2
   (implies (and (not (equal (d) 1))
                 (or (> (si (expq-1) 13) 1)
                     (and (equal (si (expq-1) 13) 1)
                          (>= (x) (d))))
                 (not (specialp)))
            (equal (rnd (z*)
                        (rmode-prime (mode (rmode)) (sign))
                        (prec (f)))
                   (* 4 (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use rtz-fl-z*
            :in-theory (e/d (rmode-prime
                             mode
                             roundup-pos-thm-2
                             z*
                             qrnd
                             f
                             n
                             c
                             qtrunc-rewrite-gen
                             lsb-rewrite
                             grd-rewrite
                             stk-rewrite-gen-2
                             stk-rewrite-gen-3)
                            (acl2::default-expt-2
                             acl2::default-plus-2
                             rnd-non-pos
                             rtz-negative
                             acl2::|(< x (/ y)) with (< 0 y)|
                             acl2::|(<= (/ x) y) with (< 0 x)|
                             acl2::not-integerp-4a
                             acl2::not-integerp-4d
                             acl2::not-integerp-3a
                             acl2::not-integerp-3d
                             acl2::not-integerp-2a
                             acl2::not-integerp-2d
                             acl2::not-integerp-1d
                             acl2::default-times-1
                             acl2::default-times-2
                             acl2::default-less-than-1
                             acl2::default-less-than-2
                             acl2::simplify-products-gather-exponents-<
                             acl2::prefer-positive-addends-<
                             bits-tail-gen))))))

(local
 (defthmd rnd-z*
   (implies (and (or (> (si (expq-1) 13) 1)
                     (and (equal (si (expq-1) 13) 1)
                          (>= (x) (d))))
                 (not (specialp)))
            (equal (rnd (z*)
                        (rmode-prime (mode (rmode)) (sign))
                        (prec (f)))
                   (* 4 (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal" :use (rnd-z*-aux-1
                         rnd-z*-aux-2)))))

(bitthm bitp-inx
  (bitp (inx)))

(local
 (defthmd inx-exactp-x/d-rel
   (implies (and (or (> (si (expq-1) 13) 1)
                     (and (equal (si (expq-1) 13) 1)
                          (>= (x) (d))))
                 (not (specialp)))
            (equal (inx)
                   (if (exactp (/ (x) (d)) (prec (f)))
                       0
                     1)))
   :hints (("Goal"
            :use (qtrunc-rewrite-gen
                  (:instance bitn-shift-up
                             (x (* (expt 2 (prec (f)))
                                   (/ (x) (d))))
                             (k 1)
                             (n 0))
                  (:instance bitn-shift-up
                             (x (* (expt 2 (1+ (prec (f))))
                                   (/ (x) (d))))
                             (k 1)
                             (n 0)))
            :in-theory (e/d (inx
                             exactp2
                             f
                             n
                             c
                             z*
                             grd-rewrite
                             stk-rewrite-gen-2
                             stk-rewrite-gen-3
                             bitn-0-vs-int-/2)
                            (acl2::default-expt-2
                             acl2::default-plus-2))))))

(local
 (defthmd quotient-expq-1
   (implies (not (specialp))
            (equal (abs (/ (a) (b)))
                   (* (expt 2 (- (si (expq-1) 13) (bias (f))))
                      (/ (x) (d)))))
   :hints (("Goal" :in-theory (e/d (quotient-formula
                                    x
                                    d
                                    siga-rewrite
                                    sigb-rewrite)
                                   (abs))))))

(bvecthm bvecp13-expq
  (bvecp (expq) 13)
  :hints (("Goal" :in-theory (enable fdivlane-segment-result-expand
                                     expq-segment))))

(local
 (defthmd si13-expq-rewrite
   (implies (not (specialp))
            (equal (si (expq) 13)
                   (if (and (< 0 (si (expq-1) 13))
                            (< (x) (d)))
                       (1- (si (expq-1) 13))
                     (si (expq-1) 13))))
   :hints (("Goal"
            :use (:instance si-bits
                            (x (1- (si (expq-1) 13)))
                            (n 13))
            :in-theory (enable fdivlane-segment-result-expand
                               expq-segment)))))

(local
 (defthmd rnd-abs-a/b-to-qrnd-aux-1
   (implies (and (<= 1 (si (expq) 13))
                 (not (specialp)))
            (equal (rnd (abs (/ (a) (b)))
                        (rmode-prime (mode (rmode)) (sign))
                        (prec (f)))
                   (* (expt 2 (+ 1
                                 (si (expq) 13)
                                 (- (bias (f)))
                                 (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (rnd-z*
                  (:instance rnd-shift
                             (x (z*))
                             (mode (rmode-prime (mode (rmode)) (sign)))
                             (k (+ -1
                                   (si (expq) 13)
                                   (- (bias (f)))
                                   (- (prec (f)))))
                             (n (prec (f)))))
            :in-theory (e/d (si13-expq-rewrite z* quotient-expq-1)
                            (abs))))))

(local
 (defthm-nl++ rnd-abs-a/b-to-qrnd-aux-2
   (implies (and (<= 1 (si (expq) 13))
                 (not (specialp)))
            (<= (expt 2 (1- (prec (f))))
                (bits (qrnd) (1- (prec (f))) 0)))
   :hints (("Goal"
            :use (rnd-abs-a/b-to-qrnd-aux-1
                  quotient-expq-1
                  (:instance rnd-exactp-d
                             (x (abs (/ (a) (b))))
                             (a (expt 2 (- (si (expq) 13) (bias (f)))))
                             (mode (rmode-prime (mode (rmode)) (sign)))
                             (n (prec (f)))))
            :in-theory (e/d (si13-expq-rewrite exactp2)
                            (abs))))
   :rule-classes :linear))

(defthmd rnd-abs-a/b-to-qrnd
  (implies (and (<= 1 (si (expq) 13))
                (not (specialp)))
           (equal (rnd (abs (/ (a) (b)))
                       (rmode-prime (mode (rmode)) (sign))
                       (prec (f)))
                  (* (expt 2 (+ 1
                                (si (expq) 13)
                                (- (bias (f)))
                                (- (prec (f)))))
                     (+ (expt 2 (1- (prec (f))))
                        (bits (qrnd) (- (prec (f)) 2) 0)))))
  :hints (("Goal"
           :use (:instance bitn-plus-bits
                           (x (qrnd))
                           (m 0)
                           (n (1- (prec (f)))))
           :in-theory (e/d (rnd-abs-a/b-to-qrnd-aux-1) (abs)))))

(defthmd inx-exact-a/b-rel
  (implies (and (<= 1 (si (expq) 13))
                (not (specialp)))
           (equal (inx)
                  (if (equal (rnd (abs (/ (a) (b)))
                                  (rmode-prime (mode (rmode)) (sign))
                                  (prec (f)))
                             (abs (/ (a) (b))))
                      0
                    1)))
  :hints (("Goal"
           :use (inx-exactp-x/d-rel
                 (:instance exactp-shift
                            (x (/ (x) (d)))
                            (k (- (si (expq-1) 13) (bias (f))))
                            (n (prec (f)))))
           :in-theory (e/d (si13-expq-rewrite
                            rnd-exactp-b-alt
                            quotient-expq-1)
                           (abs)))))

;; ======================================================================

;; Formalize the rounding of |a/b| in the denormal case:
;; drnd(|a/b|, f) = 2^(2 - bias - p) * qrnd[p-1:0]

(local
 (defthm expo-abs-a/b
   (implies (not (specialp))
            (equal (expo (abs (/ (a) (b))))
                   (if (< (x) (d))
                       (1- (- (si (expq-1) 13) (bias (f))))
                     (- (si (expq-1) 13) (bias (f))))))
   :hints (("Goal"
            :use (:instance expo-shift
                            (x (/ (x) (d)))
                            (n (- (si (expq-1) 13) (bias (f)))))
            :in-theory (e/d (quotient-expq-1) (abs))))))

(defthmd-nl rnd-abs-a/b-denormal-upper-bound
  (implies (and (< (si (expq) 13) 1)
                (not (specialp)))
           (<= (rnd (abs (/ (a) (b)))
                    (rmode-prime (mode (rmode)) (sign))
                    (prec (f)))
               (expt 2 (1+ (- (si (expq) 13) (bias (f)))))))
  :hints (("Goal"
           :use (quotient-expq-1
                 (:instance rnd-exactp-c
                            (x (abs (/ (a) (b))))
                            (a (expt 2 (1+ (- (si (expq) 13) (bias (f))))))
                            (mode (rmode-prime (mode (rmode)) (sign)))
                            (n (prec (f)))))
           :in-theory (e/d (si13-expq-rewrite exactp2)
                           (abs))))
  :rule-classes :linear)

(defthmd-nl expo-rnd-abs-a/b
  (implies (and (<= 1 (si (expq) 13))
                (not (specialp)))
           (equal (expo (rnd (abs (/ (a) (b)))
                             (rmode-prime (mode (rmode)) (sign))
                             (prec (f))))
                  (- (si (expq) 13) (bias (f)))))
  :hints (("Goal"
           :expand (abs (rnd (abs (* (a) (/ (b))))
                             (rmode-prime (mode (rmode)) (sign))
                             (prec (f))))
           :use (rnd-abs-a/b-to-qrnd
                 (:instance expo-rnd
                            (x (abs (* (a) (/ (b)))))
                            (mode (rmode-prime (mode (rmode)) (sign)))
                            (n (prec (f)))))
           :in-theory (e/d (si13-expq-rewrite)
                           (abs)))))

(local
 (defthmd-nl si13-expq-1-denormal
   (implies (not (specialp))
            (equal (< (abs (/ (a) (b)))
                      (spn (f)))
                   (<= (si (expq-1) 13)
                       (if (< (x) (d)) 1 0))))
   :hints (("Goal"
            :use (quotient-expq-1
                  (:instance expo<=
                             (x (abs (/ (a) (b))))
                             (n (- (bias (f))))))
            :in-theory (e/d (spn f) (abs))))))

(defthmd si13-expq-denormal
  (implies (not (specialp))
           (equal (< (abs (/ (a) (b)))
                     (spn (f)))
                  (<= (si (expq) 13) 0)))
  :hints (("Goal" :in-theory (e/d (si13-expq-rewrite si13-expq-1-denormal)
                                  (abs)))))

;; Case 1: si(expq-1, 13) > (x < d ? 2 : 1) - p

(local
 (defthm expo-z*-3
   (implies (and (not (specialp))
                 (integerp n))
            (equal (expo (* (/ (d))
                            (x)
                            (expt 2 (+ n (si (expq-1) 13)))))
                   (if (< (x) (d))
                       (+ -1 n (si (expq-1) 13))
                     (+ n (si (expq-1) 13)))))
   :hints (("Goal" :use (:instance expo-shift
                                   (x (* (/ (d)) (x)))
                                   (n (+ n (si (expq-1) 13))))))))

(local
 (defthmd rtz-fl-z*-denormal-1
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13) 1)
                 (< (x) (d))
                 (< (- 2 (prec (f)))
                    (si (expq-1) 13)))
            (equal (rtz (fl (z*))
                        (+ -2 (si (expq-1) 13) (prec (f))))
                   (* 4 (bits (qtrunc)
                              (+ -1 (si (expq-1) 13) (prec (f)))
                              2))))
   :hints (("Goal" :in-theory (enable z* qtrunc-rewrite-gen bits-rtz-alt)))))

(local
 (defthmd rtz-fl-z*-denormal-2
   (implies (and (not (specialp))
                 (< (si (expq-1) 13) 1)
                 (<= (d) (x))
                 (< (- 1 (prec (f)))
                    (si (expq-1) 13)))
            (equal (rtz (fl (z*))
                        (+ -1 (si (expq-1) 13) (prec (f))))
                   (* 4 (bits (qtrunc)
                              (+ (si (expq-1) 13) (prec (f)))
                              2))))
   :hints (("Goal" :in-theory (enable z* qtrunc-rewrite-gen bits-rtz-alt)))))

(local
 (defthm-nl aux-13
   (implies (and (not (specialp))
                 (integerp n))
            (< (expt 2 (- n 2))
               (* (/ (d))
                  (x)
                  (expt 2 n))))
   :rule-classes :linear))

(local
 (defthm aux-14-a
   (implies (< (x) (d))
            (equal (bits (* (/ (d)) (x)) n 0)
                   0))
   :hints (("Goal" :in-theory (enable bits fl)))))

(local
 (defthm aux-14-b
   (implies (and (not (specialp))
                 (<= (d) (x)))
            (equal (bits (* (/ (d)) (x)) n 1)
                   0))
   :hints (("Goal" :in-theory (enable bits fl)))))

(local
 (def-gl-rule aux-15
   :hyp (and (bvecp x 54)
             (natp n)
             (<= n 52)
             (< x (expt 2 (+ n 2))))
   :concl (equal (bits (1+ (bits x 54 2))
                       n 0)
                 (1+ (bits x (+ n 2) 2)))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 54)
                (:nat n 6))))

(local
 (defthm-nl aux-15-inst
   (implies (and (not (specialp))
                 (equal p (prec (f)))
                 (equal p-1 (- p 1))
                 (< (- (if (< (x) (d)) 2 1)
                       p)
                    (si (expq-1) 13))
                 (<= (si (expq-1) 13)
                     (if (< (x) (d)) 1 0)))
            (equal (bits (1+ (bits (* (/ (d))
                                      (x)
                                      (expt 2 (+ p (si (expq-1) 13))))
                                   54 2))
                         p-1 0)
                   (1+ (bits (* (/ (d))
                                (x)
                                (expt 2 (+ p (si (expq-1) 13))))
                             (1+ p) 2))))
   :hints (("Goal"
            :use (:instance aux-15
                            (x (fl (* (/ (d))
                                      (x)
                                      (expt 2 (+ p (si (expq-1) 13))))))
                            (n p-1))
            :in-theory (enable f bvecp)))))

(local
 (defthm aux-16
   (implies (integerp (* (/ (d))
                         (x)
                         (expt 2 (+ (prec (f)) (si (expq-1) 13)))))
            (equal (bits (* *2^54* (/ (d)) (x))
                         (- (si (expq-1) 13))
                         0)
                   0))
   :hints (("Goal"
            :use (:instance bits-shift-up-2
                            (x (* (/ (d))
                                  (x)
                                  (expt 2 (+ (prec (f)) (si (expq-1) 13)))))
                            (i (- (prec (f)) 54))
                            (k (- (- 54 (prec (f)))
                                  (si (expq-1) 13))))))))

(local
 (defthm aux-17
   (implies (and (equal a (expt 2 (1- (n))))
                 (integerp (* (/ (d))
                              (x)
                              (expt 2 (+ (prec (f)) (si (expq-1) 13)))))
                 (<= (si (expq-1) 13) 1))
            (integerp (* a (/ (d)) (x))))
   :hints (("Goal"
            :use (:instance integerp-*
                            (x (* (/ (d))
                                  (x)
                                  (expt 2 (+ (prec (f)) (si (expq-1) 13)))))
                            (y (expt 2 (- (- (n) (1+ (prec (f))))
                                          (si (expq-1) 13)))))
            :in-theory (enable f n c)))))

(local
 (defthm bits-tail-int-rel-inst
   (implies (and (integerp (* (/ (d))
                              (x)
                              (expt 2 (+ 53 (si (expq-1) 13)))))
                 (equal n (- 52 (prec (f)))))
            (equal (equal (bits (* (/ (d))
                                   (x)
                                   (expt 2 (+ 53 (si (expq-1) 13))))
                                n 0)
                          0)
                   (integerp (* (/ (d))
                                (x)
                                (expt 2 (+ (prec (f)) (si (expq-1) 13)))))))
   :hints (("Goal" :in-theory (enable bits-tail-int-rel)))))

(local
 (defthm aux-18
   (implies (and (integerp (* *2^54* (/ (d)) (x)))
                 (equal (bits (* *2^54* (/ (d)) (x))
                              (- (si (expq-1) 13))
                              0)
                        0))
            (integerp (* (/ (d))
                         (x)
                         (expt 2 (+ 53 (si (expq-1) 13))))))
   :hints (("Goal" :in-theory (enable bits-tail-int-rel)))
   :rule-classes :type-prescription))

(local
 (defthmd rnd-z*-denormal-1
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13) 1)
                 (< (x) (d))
                 (< (- 2 (prec (f)))
                    (si (expq-1) 13)))
            (equal (rnd (z*)
                        (rmode-prime (mode (rmode)) (sign))
                        (+ -2 (si (expq-1) 13) (prec (f))))
                   (* 4 (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (rtz-fl-z*-denormal-1
                  (:instance bits-plus-bits
                             (x (* (expt 2 (+ (prec (f))
                                              (si (expq-1) 13)))
                                   (/ (x) (d))))
                             (m 2)
                             (n (1+ (prec (f))))
                             (p (+ (prec (f)) (si (expq-1) 13))))
                  (:instance bits-shift-up-1
                             (x (/ (x) (d)))
                             (i (1+ (prec (f))))
                             (j (+ (prec (f)) (si (expq-1) 13)))
                             (k (+ (prec (f)) (si (expq-1) 13)))))
            :in-theory (e/d (rmode-prime
                             mode
                             roundup-pos-thm-2
                             z*
                             qrnd
                             f
                             n
                             c
                             qtrunc-rewrite-gen
                             lsb-rewrite
                             grd-rewrite
                             stk-rewrite-gen-1)
                            (acl2::not-integerp-4a
                             acl2::expt-type-prescription-nonpositive-base-odd-exponent
                             acl2::expt-type-prescription-nonpositive-base-even-exponent
                             acl2::expt-type-prescription-negative-base-odd-exponent
                             acl2::expt-type-prescription-negative-base-even-exponent
                             acl2::expt-type-prescription-integerp-base-a
                             acl2::expt-type-prescription-integerp-base-b
                             acl2::default-times-2
                             rnd-non-pos
                             rtz-negative
                             acl2::default-expt-2
                             acl2::default-minus
                             acl2::default-plus-1
                             acl2::default-plus-2
                             bits-tail-gen))))))

(local
 (defthmd rnd-z*-denormal-2
   (implies (and (not (specialp))
                 (< (si (expq-1) 13) 1)
                 (<= (d) (x))
                 (< (- 1 (prec (f)))
                    (si (expq-1) 13)))
            (equal (rnd (z*)
                        (rmode-prime (mode (rmode)) (sign))
                        (+ -1 (si (expq-1) 13) (prec (f))))
                   (* 4 (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (rtz-fl-z*-denormal-2
                  (:instance bits-plus-bits
                             (x (* (expt 2 (+ (prec (f))
                                              (si (expq-1) 13)))
                                   (/ (x) (d))))
                             (m 2)
                             (n (1+ (prec (f))))
                             (p (+ 1 (prec (f)) (si (expq-1) 13))))
                  (:instance bits-shift-up-1
                             (x (/ (x) (d)))
                             (i (1+ (prec (f))))
                             (j (+ 1 (prec (f)) (si (expq-1) 13)))
                             (k (+ (prec (f)) (si (expq-1) 13)))))
            :in-theory (e/d (rmode-prime
                             mode
                             roundup-pos-thm-2
                             z*
                             qrnd
                             f
                             n
                             c
                             qtrunc-rewrite-gen
                             lsb-rewrite
                             grd-rewrite
                             stk-rewrite-gen-1)
                            (acl2::not-integerp-4a
                             acl2::expt-type-prescription-nonpositive-base-odd-exponent
                             acl2::expt-type-prescription-nonpositive-base-even-exponent
                             acl2::expt-type-prescription-negative-base-odd-exponent
                             acl2::expt-type-prescription-negative-base-even-exponent
                             acl2::expt-type-prescription-integerp-base-a
                             acl2::expt-type-prescription-integerp-base-b
                             acl2::default-times-2
                             rnd-non-pos
                             rtz-negative
                             acl2::default-expt-2
                             acl2::default-minus
                             acl2::default-plus-1
                             acl2::default-plus-2
                             bits-tail-gen))))))

(local
 (defthmd drnd-non-tiny-abs-a/b-to-qrnd
   (implies (and (not (specialp))
                 (< (abs (/ (a) (b)))
                    (spn (f)))
                 (< (- (if (< (x) (d)) 2 1)
                       (prec (f)))
                    (si (expq-1) 13)))
            (equal (drnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (f))
                   (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (quotient-expq-1
                  rnd-z*-denormal-1
                  rnd-z*-denormal-2
                  (:instance rnd-shift
                             (x (z*))
                             (mode (rmode-prime (mode (rmode)) (sign)))
                             (k (+ (- (bias (f))) (- (prec (f)))))
                             (n (+ (if (< (x) (d)) -2 -1)
                                   (si (expq-1) 13)
                                   (prec (f))))))
            :in-theory (e/d (drnd
                             z*
                             si13-expq-1-denormal)
                            (abs))))))

(local
 (defthmd inx-exact-a/b-non-tiny-rel
   (implies (and (not (specialp))
                 (< (abs (/ (a) (b)))
                    (spn (f)))
                 (< (- (if (< (x) (d)) 2 1)
                       (prec (f)))
                    (si (expq-1) 13)))
            (equal (inx)
                   (if (equal (drnd (abs (/ (a) (b)))
                                    (rmode-prime (mode (rmode)) (sign))
                                    (f))
                              (abs (/ (a) (b))))
                       0
                     1)))
   :hints (("Goal"
            :use (quotient-expq-1
                  si13-expq-1-denormal
                  (:instance integerp-*
                             (x (/ (z*) 4))
                             (y 2))
                  (:instance integerp-*
                             (x (/ (z*) 2))
                             (y 2))
                  (:instance integerp-*
                             (x (z*))
                             (y (expt 2 (- 53 (prec (f))))))
                  (:instance bitn-shift-up
                             (x (* (/ (d))
                                   (x)
                                   (expt 2 (+ (1- (prec (f)))
                                              (si (expq-1) 13)))))
                             (k 1)
                             (n 0))
                  (:instance drnd-exactp-c
                             (x (abs (/ (a) (b))))
                             (mode (rmode-prime (mode (rmode)) (sign)))
                             (f (f))))
            :in-theory (e/d (inx
                             exactp2
                             f
                             n
                             c
                             z*
                             grd-rewrite
                             stk-rewrite-gen-1
                             bitn-0-vs-int-/2)
                            (acl2::not-integerp-1a
                             acl2::not-integerp-1b
                             acl2::not-integerp-2a
                             acl2::not-integerp-2b
                             acl2::not-integerp-3a
                             acl2::not-integerp-3b
                             acl2::not-integerp-4a
                             acl2::not-integerp-4b
                             acl2::expt-type-prescription-nonpositive-base-odd-exponent
                             acl2::expt-type-prescription-nonpositive-base-even-exponent
                             acl2::expt-type-prescription-negative-base-odd-exponent
                             acl2::expt-type-prescription-negative-base-even-exponent
                             acl2::default-times-2
                             acl2::default-expt-2
                             bits-tail-gen
                             exactp-abs
                             abs))))))

;; Case 2: si(expq-1, 13) <= (x < d ? 2 : 1) - p

;; Consider three subcases according to three lemmas DRND-TINY-A,
;; DRND-TINY-B-ALT, and DRND-TINY-C

(local
 (defthmd-nl aux-19
   (implies (and (not (specialp))
                 (integerp n))
            (< (* (/ (d))
                  (x)
                  (expt 2 n))
               (expt 2 (+ (if (< (x) (d)) 0 1)
                          n))))
   :rule-classes :linear))

(local
 (defthmd lsb-tiny-=-0
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1) (prec (f)))))
            (equal (lsb) 0))
   :hints (("Goal"
            :use ((:instance fl-unique
                             (x (* (/ (d))
                                   (x)
                                   (expt 2 (+ (- (prec (f)) 2)
                                              (si (expq-1) 13)))))
                             (n 0))
                  (:instance aux-19
                             (n (+ -2
                                   (si (expq-1) 13)
                                   (prec (f))))))
            :in-theory (e/d (lsb-rewrite
                             z*
                             bitn-def)
                            (acl2::simplify-products-gather-exponents-<))))))

(local
 (defthmd aux-20
   (implies (and (rationalp x)
                 (<= 0 x)
                 (< x 1))
            (equal (bits x n 0) 0))
   :hints (("Goal" :in-theory (enable bits)))))

(local
 (defthmd bits-qtrunc-tiny
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1) (prec (f)))))
            (equal (bits (qtrunc) n 2)
                   0))
   :hints (("Goal"
            :cases ((integerp n))
            :use ((:instance bits-shift-up-1
                             (x (* (/ (d))
                                   (x)
                                   (expt 2 (+ -2 (prec (f)) (si (expq-1) 13)))))
                             (i n)
                             (j 2)
                             (k 2))
                  (:instance aux-19
                             (n (+ -2
                                   (si (expq-1) 13)
                                   (prec (f))))))
            :in-theory (e/d (qtrunc-rewrite-gen
                             aux-20)
                            (acl2::simplify-products-gather-exponents-<))))))

(local
 (defthmd aux-21
   (implies (and (< 0 x)
                 (< x 1))
            (not (integerp x)))))

(local
 (defthmd-nl aux-22
   (implies (and (not (specialp))
                 (integerp n)
                 (integerp (* (/ (d))
                              (x)
                              (expt 2 n))))
            (< (if (< (x) (d)) 0 -1)
               n))
   :hints (("Goal" :use (:instance aux-21
                                   (x (* (/ (d))
                                         (x)
                                         (expt 2 n))))))))

(local
 (defthmd inx-tiny-=-1
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1) (prec (f)))))
            (equal (inx) 1))
   :hints (("Goal"
            :use ((:instance bitn-shift-up
                             (x (* (/ (d))
                                   (x)
                                   (expt 2 (+ (1- (prec (f)))
                                              (si (expq-1) 13)))))
                             (k 1)
                             (n 0))
                  (:instance aux-22
                             (n (+ -2
                                   (si (expq-1) 13)
                                   (prec (f))))))
            :in-theory (e/d (inx
                             grd-rewrite
                             stk-rewrite-gen-1
                             n
                             c
                             z*
                             bitn-0-vs-int-/2)
                            (acl2::not-integerp-4a
                             bits-tail-gen))))))

;; Subcase 1: |a/b| < spd/2

(local
 (defthmd-nl si13-expq-1-tiny-1
   (implies (and (not (specialp))
                 (< (abs (/ (a) (b)))
                    (/ (spd (f)) 2)))
            (and (implies (< (x) (d))
                          (<= (si (expq-1) 13)
                              (- 1 (prec (f)))))
                 (implies (<= (d) (x))
                          (<= (si (expq-1) 13)
                              (- (prec (f)))))))
   :hints (("Goal"
            :use (quotient-expq-1
                  (:instance expo<=
                             (x (abs (/ (a) (b))))
                             (n (+ (- (bias (f))) (- (prec (f)))))))
            :in-theory (e/d (spd f) (abs))))
   :rule-classes :linear))

(defthm abs-a/b-pos
  (implies (not (specialp))
           (< 0 (abs (/ (a) (b)))))
  :rule-classes :linear)

(local
 (defthmd grd-too-tiny-=-0
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 1 0) (prec (f)))))
            (equal (grd) 0))
   :hints (("Goal"
            :use ((:instance fl-unique
                             (x (* (/ (d))
                                   (x)
                                   (expt 2 (+ (- (prec (f)) 1)
                                              (si (expq-1) 13)))))
                             (n 0))
                  (:instance aux-19
                             (n (+ -1
                                   (si (expq-1) 13)
                                   (prec (f))))))
            :in-theory (e/d (grd-rewrite
                             z*
                             bitn-def)
                            (acl2::simplify-products-gather-exponents-<))))))

(local
 (defthmd drnd-tiny-abs-a/b-to-qrnd-1
   (implies (and (not (specialp))
                 (< (abs (/ (a) (b)))
                    (/ (spd (f)) 2)))
            (equal (drnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (f))
                   (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (si13-expq-1-tiny-1
                  inx-tiny-=-1)
            :in-theory (e/d (drnd-tiny-a
                             rmode-prime
                             mode
                             qrnd
                             bits-qtrunc-tiny
                             grd-too-tiny-=-0
                             inx
                             spd
                             f)
                            (abs))))))

;; Subcase 2: |a/b| = spd/2

(local
 (defthmd-nl si13-expq-1-tiny-2
   (implies (and (not (specialp))
                 (equal (abs (/ (a) (b)))
                        (/ (spd (f)) 2)))
            (and (equal (si (expq-1) 13)
                        (- 1 (prec (f))))
                 (equal (x) (d))))
   :hints (("Goal"
            :use ((:instance expt-lemma-4a
                             (x (* 2 (/ (x) (d))))
                             (y 1)
                             (r 2)
                             (i (+ -1 (si (expq-1) 13) (- (bias (f)))))
                             (j (+ 1 (- (bias (f))) (- (prec (f))))))
                  (:instance expt-lemma-4a
                             (x (/ (x) (d)))
                             (y 1)
                             (r 2)
                             (i (- (si (expq-1) 13) (bias (f))))
                             (j (+ 1 (- (bias (f))) (- (prec (f)))))))
            :in-theory (e/d (quotient-expq-1 spd f)
                            (acl2::default-expt-2
                             abs))))))

(local
 (defthmd-nl grd-non-too-tiny-=-1
   (implies (and (not (specialp))
                 (equal (si (expq-1) 13)
                        (- (if (< (x) (d)) 2 1) (prec (f)))))
            (equal (grd) 1))
   :hints (("Goal"
            :use (:instance fl-unique
                            (x (* (if (< (x) (d)) 2 1)
                                  (/ (d))
                                  (x)))
                            (n 1))
            :in-theory (e/d (grd-rewrite
                             z*
                             bitn-def)
                            (acl2::simplify-products-gather-exponents-<))))))

(local
 (defthmd stk-of-spd/2-=-0
   (implies (and (not (specialp))
                 (equal (si (expq-1) 13)
                        (- 1 (prec (f))))
                 (equal (x) (d)))
            (equal (stk) 0))
   :hints (("Goal" :in-theory (e/d (stk-rewrite-gen-1 z* f)
                                   ())))))

(local
 (defthmd drnd-tiny-abs-a/b-to-qrnd-2
   (implies (and (not (specialp))
                 (equal (abs (/ (a) (b)))
                        (/ (spd (f)) 2)))
            (equal (drnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (f))
                   (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use si13-expq-1-tiny-2
            :in-theory (e/d (drnd-tiny-b-alt
                             rmode-prime
                             mode
                             qrnd
                             bits-qtrunc-tiny
                             lsb-tiny-=-0
                             grd-non-too-tiny-=-1
                             stk-of-spd/2-=-0
                             spd
                             f)
                            (abs))))))

;; Subcase 3: spd/2 < |a/b| < spd

(local
 (defthmd-nl si13-expq-1-tiny-3
   (implies (and (not (specialp))
                 (< (/ (spd (f)) 2)
                    (abs (/ (a) (b))))
                 (< (abs (/ (a) (b)))
                    (spd (f))))
            (and (equal (si (expq-1) 13)
                        (- (if (< (x) (d)) 2 1) (prec (f))))
                 (not (integerp (/ (x) (d))))))
   :hints (("Goal"
            :use (quotient-expq-1
                  (:instance expo>=
                             (x (abs (/ (a) (b))))
                             (n (+ 1 (- (bias (f))) (- (prec (f))))))
                  (:instance expo<=
                             (x (abs (/ (a) (b))))
                             (n (+ 1 (- (bias (f))) (- (prec (f)))))))
            :in-theory (e/d (spd f) (abs))))))

(local
 (defthmd aux-23
   (implies (and (< 1 x)
                 (< x 2))
            (not (integerp x)))))

(local
 (defthmd-nl stk-non-too-tiny-=-1
   (implies (and (not (specialp))
                 (equal (si (expq-1) 13)
                        (- (if (< (x) (d)) 2 1) (prec (f))))
                 (not (integerp (/ (x) (d)))))
            (equal (stk) 1))
   :hints (("Goal"
            :use (:instance aux-23
                            (x (* 2 (/ (d)) (x))))
            :in-theory (e/d (stk-rewrite-gen-1 z* n c bitn-def)
                            ())))))

(local
 (defthmd drnd-tiny-abs-a/b-to-qrnd-3
   (implies (and (not (specialp))
                 (< (/ (spd (f)) 2)
                    (abs (/ (a) (b))))
                 (< (abs (/ (a) (b)))
                    (spd (f))))
            (equal (drnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (f))
                   (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use si13-expq-1-tiny-3
            :in-theory (e/d (drnd-tiny-c
                             rmode-prime
                             mode
                             qrnd
                             bits-qtrunc-tiny
                             grd-non-too-tiny-=-1
                             stk-non-too-tiny-=-1
                             spd
                             f)
                            (abs))))))

;; Combine three tiny subcases

(local
 (defthm-nl si13-expq-1-tiny
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1)
                        (prec (f)))))
            (< (abs (/ (a) (b)))
               (spd (f))))
   :hints (("Goal" :in-theory (e/d (quotient-expq-1 spd f) (abs))))
   :rule-classes :linear))

(local
 (defthmd drnd-tiny-abs-a/b-to-qrnd
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1)
                        (prec (f)))))
            (equal (drnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (f))
                   (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                      (bits (qrnd) (1- (prec (f))) 0))))
   :hints (("Goal"
            :use (drnd-tiny-abs-a/b-to-qrnd-1
                  drnd-tiny-abs-a/b-to-qrnd-2
                  drnd-tiny-abs-a/b-to-qrnd-3)
            :in-theory (e/d ()
                            (abs))))))

(local
 (defthmd drnd-tiny-abs-a/b-inexact
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1)
                        (prec (f)))))
            (not (equal (drnd (abs (/ (a) (b)))
                              (rmode-prime (mode (rmode)) (sign))
                              (f))
                        (abs (/ (a) (b))))))
   :hints (("Goal"
            :use (drnd-tiny-abs-a/b-to-qrnd
                  si13-expq-1-tiny)
            :in-theory (e/d (spd f) (abs))))))

(local
 (defthmd inx-exact-a/b-tiny-rel
   (implies (and (not (specialp))
                 (<= (si (expq-1) 13)
                     (- (if (< (x) (d)) 2 1)
                        (prec (f)))))
            (equal (inx)
                   (if (equal (drnd (abs (/ (a) (b)))
                                    (rmode-prime (mode (rmode)) (sign))
                                    (f))
                              (abs (/ (a) (b))))
                       0
                     1)))
   :hints (("Goal" :use (inx-tiny-=-1
                         drnd-tiny-abs-a/b-inexact)))))

;; Combine two denormal cases

(defthmd drnd-abs-a/b-to-qrnd
  (implies (and (not (specialp))
                (< (abs (/ (a) (b)))
                   (spn (f))))
           (equal (drnd (abs (/ (a) (b)))
                        (rmode-prime (mode (rmode)) (sign))
                        (f))
                  (* (expt 2 (+ 2 (- (bias (f))) (- (prec (f)))))
                     (bits (qrnd) (1- (prec (f))) 0))))
  :hints (("Goal" :use (drnd-non-tiny-abs-a/b-to-qrnd
                        drnd-tiny-abs-a/b-to-qrnd))))

(defthmd inx-exact-a/b-denormal-rel
  (implies (and (not (specialp))
                (< (abs (/ (a) (b)))
                   (spn (f))))
           (equal (inx)
                  (if (equal (drnd (abs (/ (a) (b)))
                                   (rmode-prime (mode (rmode)) (sign))
                                   (f))
                             (abs (/ (a) (b))))
                      0
                    1)))
  :hints (("Goal" :use (inx-exact-a/b-non-tiny-rel
                        inx-exact-a/b-tiny-rel))))
