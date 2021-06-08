;; Cuong Chau <ckc8687@gmail.com>

;; June 2021

(in-package "RTL")

(include-book "arith-utils")
(include-book "fp-constants")

(local (arith-5-for-rtl))

(in-theory (e/d (bits-si
                 bits-upper-bound
                 bvecp-bitn-1
                 expo-fl
                 expo-lpn
                 expo-shift
                 expo-ndecode
                 (:linear sig-lower-bound)
                 (:linear sig-upper-bound)
                 nrepp-lpn
                 nrepp-spn
                 positive-lpn
                 rup-lower-bound
                 rdn-upper-bound
                 rtz-upper-pos
                 raz-lower-pos
                 roundup-pos)
                (rnd-positive
                 rnd-negative)))

;; ======================================================================

(defun induct-on-index (i)
  (if (zp i)
      i
    (induct-on-index (1- i))))

(defthmd-nl bits-not-exceed
  (implies (and (rationalp x)
                (<= 0 x)
                (natp j))
           (<= (bits x i j) x))
  :hints (("Goal" :in-theory (enable bits)))
  :rule-classes :linear)

(defthmd bits-shift-up-1-alt
  (implies (and (integerp k)
                (integerp i)
                (integerp j))
           (and (equal (bits (* (expt 2 k) x) i j)
                       (bits x (- i k) (- j k)))
                (equal (bits (* x (expt 2 k)) i j)
                       (bits x (- i k) (- j k)))))
  :hints (("Goal" :use bits-shift-up-1)))

(defthmd bits-shift-up-2-alt
  (implies (and (integerp x)
                (natp k)
                (integerp i))
           (and (equal (bits (* (expt 2 k) x) i 0)
                       (* (expt 2 k)
                          (bits x (- i k) 0)))
                (equal (bits (* x (expt 2 k)) i 0)
                       (* (expt 2 k)
                          (bits x (- i k) 0)))))
  :hints (("Goal" :use (:instance bits-shift-up-2 (i (- i k))))))

(defthmd bits-tail-int-rel
  (implies (and (integerp x)
                (acl2-numberp n))
           (equal (equal (bits x n 0) 0)
                  (integerp (* (expt 2 (- -1 n)) x))))
  :hints (("Goal" :in-theory (enable bits))))

(defthmd bitn-bitp
  (implies (bitp x)
           (equal (bitn x 0) x)))

(defthmd bitn-shift-up-alt
  (implies (and (integerp n)
                (integerp k))
           (equal (bitn (* x (expt 2 k)) n)
                  (bitn x (- n k))))
  :hints (("Goal" :use (:instance bitn-shift-up
                                  (n (- n k))))))

(defthmd bitn-0-vs-int-/2
  (implies (integerp x)
           (equal (equal (bitn x 0) 0)
                  (integerp (/ x 2))))
  :hints (("Goal" :in-theory (enable bitn-def))))

(defthmd bitn-0-vs-int-/4
  (implies (integerp x)
           (equal (and (equal (bitn x 1) 0)
                       (equal (bitn x 0) 0))
                  (integerp (/ x 4))))
  :hints (("Goal" :in-theory (enable bitn-def))))

(defthm expo-shift-alt
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* x (expt 2 n)))
                  (+ n (expo x))))
  :hints (("Goal" :use expo-shift)))

(defthmd-nl bits-tail-sub-1
  (implies (and (<= (expt 2 (1+ n)) x)
                (< x (expt 2 (+ 2 n)))
                (integerp x)
                (integerp n))
           (equal (bits x n 0)
                  (- x (expt 2 (1+ n)))))
  :hints (("Goal" :in-theory (enable bits-mod))))

(defthmd-nl bits-tail-sub-2
  (implies (and (<= (expt 2 (+ 2 n)) x)
                (< x (+ (expt 2 (+ 2 n))
                        (expt 2 (1+ n))))
                (integerp x)
                (integerp n))
           (equal (bits x n 0)
                  (- x (expt 2 (+ 2 n)))))
  :hints (("Goal" :in-theory (enable bits-mod))))

(defthmd fp-abs-rewrite
  (implies (rationalp x)
           (equal (abs x)
                  (* (sig x) (expt 2 (expo x)))))
  :hints (("Goal" :use fp-abs)))

;; SI

(defthmd-nl si-bounds
  (implies (and (bvecp r n)
                (posp n))
           (and (<= (- (expt 2 (1- n)))
                    (si r n))
                (< (si r n)
                   (expt 2 (1- n)))))
  :hints (("Goal" :in-theory (enable si bvecp)))
  :rule-classes :linear)

(defthm si-equality-preserved
  (implies (acl2-numberp n)
           (equal (equal (si x n) (si y n))
                  (equal x y)))
  :hints (("Goal"
           :use ((:instance bitn-plus-mult
                            (k -1)
                            (m n)
                            (n (1- n)))
                 (:instance bitn-plus-mult
                            (x y)
                            (k -1)
                            (m n)
                            (n (1- n))))
           :in-theory (e/d (si bitn bits) (bits-n-n-rewrite)))))

(defthmd bitn-0-si
  (implies (posp n)
           (equal (bitn (si r n) 0)
                  (bitn r 0)))
  :hints (("Goal" :in-theory (enable bitn-def si fl))))

;; CAT

(defthmd cat-for-gl
  (equal (cat x m y n)
         (if (and (natp m) (natp n))
             (logior (ash (bits x (1- m) 0) n)
                     (bits y (1- n) 0))
           0))
  :hints (("Goal" :use binary-cat-for-gl)))

(defthm cat-lower-bound
  (implies (and (natp m)
                (natp n))
           (<= (* (expt 2 n) (bits x (1- m) 0))
               (cat x m y n)))
  :hints (("Goal" :in-theory (enable cat)))
  :rule-classes :linear)

(defthm-nl cat-upper-bound
  (< (cat x m y n)
     (expt 2 (+ m n)))
  :hints (("Goal" :in-theory (enable cat)))
  :rule-classes :linear)

(defthmd pos-cat
  (implies (and (or (and (posp x)
                         (< x (expt 2 m)))
                    (and (posp y)
                         (< y (expt 2 n))))
                (natp m)
                (natp n))
           (< 0 (cat x m y n)))
  :hints (("Goal" :in-theory (enable bvecp cat)))
  :rule-classes :linear)

(defthm cat-equal-elim
  (implies (and (bvecp x1 m)
                (bvecp x2 m)
                (natp n))
           (equal (equal (cat x1 m y n) (cat x2 m y n))
                  (equal x1 x2)))
  :hints (("Goal" :in-theory (enable cat bvecp))))

(defthmd cat-+-1
  (implies (and (< (+ y z) (expt 2 n))
                (natp m)
                (natp y)
                (natp z))
           (and (equal (+ z (cat x m y n))
                       (cat x m (+ y z) n))
                (equal (+ (cat x m y n) z)
                       (cat x m (+ y z) n))))
  :hints (("Goal" :in-theory (enable bvecp cat))))

(defthmd-nl++ cat-+-2
  (implies (and (<= (expt 2 n) (+ y z))
                (< x (1- (expt 2 m)))
                (< y (expt 2 n))
                (< z (expt 2 n))
                (natp x)
                (integerp y)
                (integerp z))
           (and (equal (+ z (cat x m y n))
                       (cat (1+ x) m (+ y z) n))
                (equal (+ (cat x m y n) z)
                       (cat (1+ x) m (+ y z) n))))
  :hints (("Goal"
           :use (:instance bitn-plus-bits
                           (x (+ y z))
                           (m 0))
           :in-theory (enable cat
                              bvecp))))

;; EXPO

(defthm expo-int
  (implies (integerp x)
           (<= 0 (expo x)))
  :hints (("Goal"
           :cases ((equal x 0))
           :use (:instance expo-monotone
                           (x 1)
                           (y x))))
  :rule-classes :linear)

(defthm expo-abs
  (implies (rationalp x)
           (equal (expo (abs x)) (expo x))))

(defthmd bits-expo-rel
  (implies (natp x)
           (equal (bits x (expo x) 0)
                  x))
  :hints (("Goal" :in-theory (enable bits expo-upper-bound))))

(defthmd bitn-expo-rel-1
  (implies (and (< (expo x) n)
                (natp x)
                (integerp n))
           (equal (bitn x n) 0))
  :hints (("Goal"
           :use (expo-upper-bound
                 (:instance bitn-plus-bits
                            (m 0))))))

(defthmd bitn-expo-rel-2
  (implies (and (equal n (expo x))
                (natp x)
                (< 0 n))
           (equal (bitn x n) 1))
  :hints (("Goal"
           :use (expo-lower-bound
                 expo-upper-bound
                 (:instance bitn-plus-bits
                            (m 0)))
           :in-theory (enable bvecp))))

(defthmd bitn-expo-rel-3
  (implies (posp x)
           (equal (bitn x (expo x)) 1))
  :hints (("Goal"
           :use (expo-upper-bound
                 (:instance bitn-expo-rel-2
                            (n (expo x)))))))

(defthmd bitn-expo-rel-4
  (implies (and (bvecp x (1+ n))
                (equal (bitn x n) 1)
                (acl2-numberp n))
           (equal (expo x) n))
  :hints (("Goal"
           :use expo<=
           :in-theory (enable bvecp))))

(defthmd bitn-minus-preserved
  (implies (and (<= (expt 2 (1+ m)) x)
                (integerp x)
                (integerp m))
           (equal (bitn (- x (bits x m 0))
                        (expo x))
                  (bitn x (expo x))))
  :hints (("Goal"
           :use ((:instance expo-monotone
                            (x (expt 2 (1+ m)))
                            (y x))
                 (:instance bits-plus-bits
                            (m 0)
                            (p (1+ m))
                            (n (expo x)))
                 (:instance bitn-shift-up-alt
                            (x (bits x (expo x) (1+ m)))
                            (k (1+ m))
                            (n (expo x))))
           :in-theory (enable expo-upper-bound
                              bitn-bits
                              bvecp))))

(defthm expo-minus-preserved
  (implies (and (<= (expt 2 (1+ m)) x)
                (integerp x)
                (integerp m))
           (equal (expo (- x (bits x m 0)))
                  (expo x)))
  :hints (("Goal"
           :use (bitn-minus-preserved
                 (:instance expo-monotone
                            (x (- x (bits x m 0)))
                            (y x)))
           :in-theory (enable bitn-expo-rel-1
                              bitn-expo-rel-3))))

(defthmd expo-shft-preserved
  (implies (and (equal k (expt 2 m))
                (<= k x)
                (< x (expt 2 (1+ n)))
                (integerp x)
                (natp m)
                (integerp n))
           (equal (expo (* k (bits x n m)))
                  (expo x)))
  :hints (("Goal"
           :use (expo-upper-bound
                 (:instance expo-minus-preserved
                            (m (1- m)))
                 (:instance bits-plus-bits
                            (p m)
                            (m 0)))
           :in-theory (e/d (bvecp)
                           (expo-minus-preserved)))))

;; FL

(defthmd fl-<-int
  (implies (and (< x y)
                (rationalp x)
                (integerp y))
           (<= (fl x) (1- y)))
  :rule-classes :linear)

(defthmd-nl++ fl-/-ints-expand
  (implies (and (integerp x)
                (posp y))
           (equal (fl (/ x y))
                  (if (integerp (/ x y))
                      (/ x y)
                    (if (integerp (/ (1+ x) y))
                        (1- (/ (1+ x) y))
                      (fl (/ (1+ x) y))))))
  :hints (("Goal" :use (:instance fl-def
                                  (x (/ x y))))))

(defthmd bits-to-mod-fl
  (implies (and (integerp i) (integerp j))
           (equal (bits x i j)
                  (mod (fl (/ x (expt 2 j)))
                       (expt 2 (- (1+ i) j)))))
  :hints (("Goal" :use (:instance bits-mod-fl
                                  (i (1+ i))))))

(defthm bits-fl
  (implies (and (rationalp x)
                (integerp i)
                (natp j))
           (equal (bits (fl x) i j)
                  (bits x i j)))
  :hints (("Goal" :in-theory (enable bits-to-mod-fl))))

(defthm bitn-fl
  (implies (and (rationalp x)
                (natp n))
           (equal (bitn (fl x) n)
                  (bitn x n)))
  :hints (("Goal" :in-theory (enable bitn-def))))

(defthmd bitn-integerp-of-fl-rel
  (implies (acl2-numberp x)
           (equal (integerp (* 1/2 (fl x)))
                  (equal (bitn x 0) 0)))
  :hints (("Goal" :in-theory (enable bitn-def))))

(defthmd mod-to-fl
  (implies (case-split (acl2-numberp x))
           (equal (mod x y)
                  (- x (* y (fl (/ x y))))))
  :hints (("Goal" :use mod-def)))

(defthmd cg-to-fl
  (implies (rationalp x)
           (equal (cg x)
                  (if (integerp x) (fl x) (1+ (fl x)))))
  :hints (("Goal" :use fl-cg)))

;; MOD

(defthmd mod-bits-rel-plus
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (+ x y) (expt 2 n))
                  (mod (+ (bits x (1- n) 0)
                          (bits y (1- n) 0))
                       (expt 2 n))))
  :hints (("Goal" :in-theory (enable mod-to-fl bits-mod))))

(defthmd mod-bits-rel-minus
  (implies (and (integerp x)
                (integerp y))
           (equal (mod (- x y) (expt 2 n))
                  (mod (- (bits x (1- n) 0)
                          (bits y (1- n) 0))
                       (expt 2 n))))
  :hints (("Goal" :in-theory (enable mod-to-fl bits-mod))))

;; SETBITN

(defthm setbitn-1-lower-bound
  (implies (and (< n w)
                (integerp w)
                (natp n))
           (<= (expt 2 n) (setbitn x w n 1)))
  :hints (("Goal"
           :use (:instance expt-lemma-7
                           (x (bits x (1- n) 0)))
           :in-theory (enable cat bvecp)))
  :rule-classes :linear)

(defthm setbitn-1-upper-bound
  (implies (and (<= (expo x) n)
                (natp x)
                (acl2-numberp n))
           (< (setbitn x w n 1) (expt 2 (1+ n))))
  :hints (("Goal"
           :use (expo-upper-bound
                 (:instance bits-plus-bits
                            (p (1+ n))
                            (m 0)
                            (n (1- w))))
           :in-theory (enable cat bvecp)))
:rule-classes :linear)

(defthm expo-setbitn-1-rewrite-1
  (implies (and (<= (expo x) n)
                (< n w)
                (natp x)
                (integerp w)
                (natp n))
           (equal (expo (setbitn x w n 1))
                  n))
  :hints (("Goal"
           :use (:instance expo-unique
                           (x (setbitn x w n 1)))
           :in-theory (disable setbitn))))

(defthm x-<=-setbitn-1
  (implies (and (bvecp x w)
                (natp n)
                (< n w))
           (<= x (setbitn x w n 1)))
  :hints (("Goal"
           :cases ((equal (bitn x n) 0))
           :use ((:instance expt-lemma-7
                            (x (bits x (+ -1 n) 0)))
                 (:instance bits-tail
                            (x (+ (expt 2 n)
                                  (bits x (+ -1 n) 0)))
                            (i n))
                 (:instance bits-tail
                            (i (1- w)))
                 (:instance bits-tail
                            (i n))
                 (:instance bits-plus-bits
                            (p (1+ n))
                            (m 0)
                            (n (1- w)))
                 (:instance bitn-plus-bits
                            (m 0)))
           :in-theory (e/d (bvecp cat)
                           (bits-tail))))
  :rule-classes :linear)

(defthm expo-setbitn-1-lower-bound
  (implies (and (bvecp x w)
                (natp n)
                (< n w))
           (<= (expo x)
               (expo (setbitn x w n 1))))
  :hints (("Goal"
           :use (:instance expo-monotone
                           (y (setbitn x w n 1)))
           :in-theory (disable setbitn)))
  :rule-classes :linear)

(defthmd bits-of-non-int-idxes
  (implies (or (not (integerp m))
               (not (integerp n)))
           (equal (bits x n m) 0))
  :hints (("Goal" :in-theory (enable bits))))

(defthmd bits-shrinked-upper-idx
  (implies (and (bvecp x k)
                (integerp n)
                (<= (1- k) n))
           (equal (bits x n m)
                  (bits x (1- k) m)))
  :hints (("Goal"
           :in-theory (enable bits-of-non-int-idxes bvecp)
           :use ((:instance bits-plus-bits
                            (p k))
                 (:instance bits-plus-bits
                            (p m)
                            (m k))
                 (:instance bits-plus-bits
                            (p k)
                            (m 0))))))

(defthmd setbitn-1-rewrite
  (implies (and (<= n (expo x))
                (< n w)
                (bvecp x w)
                (integerp w)
                (natp n))
           (equal (setbitn x w n 1)
                  (+ (expt 2 n)
                     (bits x (1- n) 0)
                     (* (expt 2 (1+ n))
                        (bits x (expo x) (1+ n))))))
  :hints (("Goal"
           :use ((:instance expt-lemma-7
                            (x (bits x (1- n) 0)))
                 (:instance bits-shrinked-upper-idx
                            (k (1+ (expo x)))
                            (m (1+ n))
                            (n (1- w)))
                 (:instance bits-shrinked-upper-idx
                            (k w)
                            (m (1+ n))
                            (n (expo x))))
           :in-theory (enable expo-upper-bound bvecp cat))))

(defthm expo-setbitn-1-rewrite-2
  (implies (and (<= n (expo x))
                (< n w)
                (bvecp x w)
                (integerp w)
                (natp n))
           (equal (expo (setbitn x w n 1))
                  (expo x)))
  :hints (("Goal"
           :use (expo-setbitn-1-lower-bound
                 (:instance expo-unique
                            (x (setbitn x w n 1))
                            (n (expo x)))
                 (:instance expt-lemma-7
                            (x (bits x (1- n) 0)))
                 (:instance expt-lemma-8
                            (x (bits x (expo x) (1+ n)))
                            (y (+ (expt 2 n)
                                  (bits x (1- n) 0)))
                            (n1 (- (expo x) n))
                            (n2 (1+ n))))
           :in-theory (e/d (setbitn-1-rewrite
                            expo-lower-bound
                            bvecp)
                           (setbitn
                            expo-setbitn-1-lower-bound)))))

;; ======================================================================

(defthm natp-expw
  (implies (formatp f)
           (natp (expw f)))
  :hints (("Goal" :in-theory (enable formatp expw)))
  :rule-classes :type-prescription)

(defthm expw-lower-bound
  (implies (formatp f)
           (<= 2 (expw f)))
  :hints (("Goal" :in-theory (enable formatp expw)))
  :rule-classes :linear)

(defthm posp-bias
  (implies (formatp f)
           (posp (bias f)))
  :hints (("Goal" :in-theory (enable formatp bias expw)))
  :rule-classes :type-prescription)

(defthm natp-prec
  (implies (formatp f)
           (natp (prec f)))
  :hints (("Goal" :in-theory (enable formatp prec)))
  :rule-classes :type-prescription)

(defthm prec-lower-bound
  (implies (formatp f)
           (<= 2 (prec f)))
  :hints (("Goal" :in-theory (enable formatp prec)))
  :rule-classes :linear)

(defthm posp-sigw
  (implies (formatp f)
           (posp (sigw f)))
  :hints (("Goal" :in-theory (enable formatp sigw prec)))
  :rule-classes :type-prescription)

(defthm sgnf-upper-bound
  (<= (sgnf x f) 1)
  :hints (("Goal" :in-theory (enable sgnf)))
  :rule-classes :linear)

(defthm expf-upper-bound
  (implies (formatp f)
           (< (expf x f)
              (expt 2 (expw f))))
  :hints (("Goal" :in-theory (enable expf)))
  :rule-classes :linear)

(defthm manf-upper-bound
  (implies (formatp f)
           (< (manf x f)
              (expt 2 (1- (prec f)))))
  :hints (("Goal" :in-theory (enable manf)))
  :rule-classes :linear)

(defthm sigf-=-manf
  (implies (not (explicitp f))
           (equal (sigf x f)
                  (manf x f)))
  :hints (("Goal" :in-theory (enable sigf manf sigw))))

(defthmd zerp-is-unique-format
  (implies (zerp x f)
           (and (not (snanp x f))
                (not (qnanp x f))
                (not (nanp x f))
                (not (infp x f))
                (not (normp x f))
                (not (denormp x f))))
  :hints (("Goal" :in-theory (enable snanp qnanp nanp infp zerp normp denormp
                                     encodingp expw formatp))))

(defthmd denormp-is-unique-format
  (implies (denormp x f)
           (and (not (snanp x f))
                (not (qnanp x f))
                (not (nanp x f))
                (not (infp x f))
                (not (zerp x f))
                (not (normp x f))))
  :hints (("Goal" :in-theory (enable snanp qnanp nanp infp zerp normp denormp
                                     encodingp expw formatp))))

(defthmd zerp-decode-rel
  (implies (encodingp x f)
           (equal (zerp x f)
                  (equal (decode x f) 0)))
  :hints (("Goal" :in-theory (enable zerp decode ddecode))))

;; BF

(defthm formatp-bf
  (formatp (bf))
  :hints (("Goal" :in-theory (enable bf))))

(defthm expw-bf
  (equal (expw (bf)) *expw-bf*)
  :hints (("Goal" :in-theory (enable bf))))

(defthm prec-bf
  (equal (prec (bf)) *prec-bf*)
  :hints (("Goal" :in-theory (enable bf))))

(defthm sigw-bf
  (equal (sigw (bf)) *sigw-bf*)
  :hints (("Goal" :in-theory (enable bf))))

(defthm bias-bf
  (equal (bias (bf)) *bias-bf*)
  :hints (("Goal" :in-theory (enable bf))))

(defthm not-explicitp-bf
  (not (explicitp (bf)))
  :hints (("Goal" :in-theory (enable bf))))

(defthm indef-bf
  (equal (indef (bf)) #x7FC0)
  :hints (("Goal" :in-theory (enable bf))))

(defthm zencode-bf
  (and (equal (zencode 0 (bf)) 0)
       (equal (zencode 1 (bf)) #x8000))
  :hints (("Goal" :in-theory (enable bf))))

(defthmd zencode-ddecode-bf
  (implies (and (bvecp x *bfw*)
                (equal (expf x (bf)) 0)
                (equal (ddecode x (bf)) 0))
           (equal (zencode (sgnf x (bf)) (bf))
                  x))
  :hints (("Goal"
           :use ((:instance bitn-plus-bits
                            (m 0)
                            (n (1- *bfw*)))
                 (:instance bits-plus-bits
                            (m 0)
                            (n (- *bfw* 2))
                            (p *sigw-bf*)))
           :in-theory (enable ddecode
                              zencode
                              sgnf
                              expf
                              manf))))

(defthmd zerp-decode-rel-bf
  (implies (bvecp x *bfw*)
           (equal (zerp x (bf))
                  (equal (decode x (bf)) 0)))
  :hints (("Goal" :in-theory (enable zerp
                                     decode
                                     ddecode
                                     encodingp))))

(defthmd spd-bf
  (equal (spd (bf))
         (expt 2 -133))
  :hints (("Goal" :in-theory (enable bf))))

(defthmd spn-bf
  (equal (spn (bf))
         (expt 2 -126))
  :hints (("Goal" :in-theory (enable bf))))

(defthmd lpn-bf
  (equal (lpn (bf))
         (* (1- (expt 2 8))
            (expt 2 120)))
  :hints (("Goal" :in-theory (enable bf))))

;; HP

(defthm expw-hp
  (equal (expw (hp)) *expw-hp*)
  :hints (("Goal" :in-theory (enable hp))))

(defthm prec-hp
  (equal (prec (hp)) *prec-hp*)
  :hints (("Goal" :in-theory (enable hp))))

(defthm sigw-hp
  (equal (sigw (hp)) *sigw-hp*)
  :hints (("Goal" :in-theory (enable hp))))

(defthm bias-hp
  (equal (bias (hp)) *bias-hp*)
  :hints (("Goal" :in-theory (enable hp))))

(defthm not-explicitp-hp
  (not (explicitp (hp)))
  :hints (("Goal" :in-theory (enable hp))))

(defthm indef-hp
  (equal (indef (hp)) #x7E00)
  :hints (("Goal" :in-theory (enable hp))))

(defthm zencode-hp
  (and (equal (zencode 0 (hp)) 0)
       (equal (zencode 1 (hp)) #x8000))
  :hints (("Goal" :in-theory (enable hp))))

(defthmd zencode-ddecode-hp
  (implies (and (bvecp x *hpw*)
                (equal (expf x (hp)) 0)
                (equal (ddecode x (hp)) 0))
           (equal (zencode (sgnf x (hp)) (hp))
                  x))
  :hints (("Goal"
           :use ((:instance bitn-plus-bits
                            (m 0)
                            (n (1- *hpw*)))
                 (:instance bits-plus-bits
                            (m 0)
                            (n (- *hpw* 2))
                            (p *sigw-hp*)))
           :in-theory (enable ddecode
                              zencode
                              sgnf
                              expf
                              manf))))

(defthmd zerp-decode-rel-hp
  (implies (bvecp x *hpw*)
           (equal (zerp x (hp))
                  (equal (decode x (hp)) 0)))
  :hints (("Goal" :in-theory (enable zerp
                                     decode
                                     ddecode
                                     encodingp))))

(defthmd spd-hp
  (equal (spd (hp))
         (expt 2 -24))
  :hints (("Goal" :in-theory (enable hp))))

(defthmd spn-hp
  (equal (spn (hp))
         (expt 2 -14))
  :hints (("Goal" :in-theory (enable hp))))

(defthmd lpn-hp
  (equal (lpn (hp))
         (* (1- (expt 2 11))
            (expt 2 5)))
  :hints (("Goal" :in-theory (enable hp))))

(defthm sp-!=-hp
  (not (equal (sp) (hp)))
  :hints (("Goal" :in-theory (enable sp hp))))

(defthm dp-!=-hp
  (not (equal (dp) (hp)))
  :hints (("Goal" :in-theory (enable dp hp))))

;; SP

(defthm expw-sp
  (equal (expw (sp)) *expw-sp*)
  :hints (("Goal" :in-theory (enable sp))))

(defthm prec-sp
  (equal (prec (sp)) *prec-sp*)
  :hints (("Goal" :in-theory (enable sp))))

(defthm sigw-sp
  (equal (sigw (sp)) *sigw-sp*)
  :hints (("Goal" :in-theory (enable sp))))

(defthm bias-sp
  (equal (bias (sp)) *bias-sp*)
  :hints (("Goal" :in-theory (enable sp))))

(defthm not-explicitp-sp
  (not (explicitp (sp)))
  :hints (("Goal" :in-theory (enable sp))))

(defthm indef-sp
  (equal (indef (sp)) #x7FC00000)
  :hints (("Goal" :in-theory (enable sp))))

(defthm zencode-sp
  (and (equal (zencode 0 (sp)) 0)
       (equal (zencode 1 (sp)) #x80000000))
  :hints (("Goal" :in-theory (enable sp))))

(defthmd zencode-ddecode-sp
  (implies (and (bvecp x *spw*)
                (equal (expf x (sp)) 0)
                (equal (ddecode x (sp)) 0))
           (equal (zencode (sgnf x (sp)) (sp))
                  x))
  :hints (("Goal"
           :use ((:instance bitn-plus-bits
                            (m 0)
                            (n (1- *spw*)))
                 (:instance bits-plus-bits
                            (m 0)
                            (n (- *spw* 2))
                            (p *sigw-sp*)))
           :in-theory (enable ddecode
                              zencode
                              sgnf
                              expf
                              manf))))

(defthmd zerp-decode-rel-sp
  (implies (bvecp x *spw*)
           (equal (zerp x (sp))
                  (equal (decode x (sp)) 0)))
  :hints (("Goal" :in-theory (enable zerp
                                     decode
                                     ddecode
                                     encodingp))))

(defthmd spd-sp
  (equal (spd (sp))
         (expt 2 -149))
  :hints (("Goal" :in-theory (enable sp))))

(defthmd spn-sp
  (equal (spn (sp))
         (expt 2 -126))
  :hints (("Goal" :in-theory (enable sp))))

(defthmd lpn-sp
  (equal (lpn (sp))
         (* (1- (expt 2 24))
            (expt 2 104)))
  :hints (("Goal" :in-theory (enable sp))))

;; DP

(defthm expw-dp
  (equal (expw (dp)) *expw-dp*)
  :hints (("Goal" :in-theory (enable dp))))

(defthm prec-dp
  (equal (prec (dp)) *prec-dp*)
  :hints (("Goal" :in-theory (enable dp))))

(defthm sigw-dp
  (equal (sigw (dp)) *sigw-dp*)
  :hints (("Goal" :in-theory (enable dp))))

(defthm bias-dp
  (equal (bias (dp)) *bias-dp*)
  :hints (("Goal" :in-theory (enable dp))))

(defthm not-explicitp-dp
  (not (explicitp (dp)))
  :hints (("Goal" :in-theory (enable dp))))

(defthm indef-dp
  (equal (indef (dp)) #x7FF8000000000000)
  :hints (("Goal" :in-theory (enable dp))))

(defthm zencode-dp
  (and (equal (zencode 0 (dp)) 0)
       (equal (zencode 1 (dp)) #x8000000000000000))
  :hints (("Goal" :in-theory (enable dp))))

(defthmd zencode-ddecode-dp
  (implies (and (bvecp x *dpw*)
                (equal (expf x (dp)) 0)
                (equal (ddecode x (dp)) 0))
           (equal (zencode (sgnf x (dp)) (dp))
                  x))
  :hints (("Goal"
           :use ((:instance bitn-plus-bits
                            (m 0)
                            (n (1- *dpw*)))
                 (:instance bits-plus-bits
                            (m 0)
                            (n (- *dpw* 2))
                            (p *sigw-dp*)))
           :in-theory (enable ddecode
                              zencode
                              sgnf
                              expf
                              manf))))

(defthmd zerp-decode-rel-dp
  (implies (bvecp x *dpw*)
           (equal (zerp x (dp))
                  (equal (decode x (dp)) 0)))
  :hints (("Goal" :in-theory (enable zerp
                                     decode
                                     ddecode
                                     encodingp))))

(defthmd spd-dp
  (equal (spd (dp))
         (expt 2 -1074))
  :hints (("Goal" :in-theory (enable dp))))

(defthmd spn-dp
  (equal (spn (dp))
         (expt 2 -1022))
  :hints (("Goal" :in-theory (enable dp))))

(defthmd lpn-dp
  (equal (lpn (dp))
         (* (1- (expt 2 53))
            (expt 2 971)))
  :hints (("Goal" :in-theory (enable dp))))

;; ======================================================================

(defthm expo-spn
  (implies (formatp f)
           (equal (expo (spn f))
                  (- 1 (bias f))))
  :hints (("Goal" :in-theory (enable spn))))

(defthm smallest-spn-linear
  (implies (nrepp x f)
           (<= (spn f) (abs x)))
  :hints (("Goal" :use smallest-spn))
  :rule-classes :linear)

(defthm smallest-spn-instance
  (implies (normp x f)
           (<= (spn f)
               (abs (ndecode x f))))
  :hints (("Goal"
           :use (:instance smallest-spn
                           (x (ndecode x f)))))
  :rule-classes :linear)

(defthm largest-lpn-linear
  (implies (nrepp x f)
           (<= (abs x) (lpn f)))
  :hints (("Goal"
           :in-theory (enable nrepp lpn exactp-2**n)
           :use ((:instance expo>=
                            (x (abs x))
                            (n (- (expt 2 (expw f))
                                  (1+ (bias f)))))
                 (:instance fp-2
                            (x (expt 2 (- (expt 2 (expw f))
                                          (1+ (bias f)))))
                            (y (abs x))
                            (n (prec f))))))
  :rule-classes :linear)

(defthm largest-lpn-linear-1
  (implies (nrepp x f)
           (<= (- (lpn f)) x))
  :hints (("Goal" :use largest-lpn-linear))
  :rule-classes :linear)

(defthm largest-lpn-linear-2
  (implies (nrepp x f)
           (<= x (lpn f)))
  :hints (("Goal" :use largest-lpn-linear))
  :rule-classes :linear)

(defthm largest-lpn-instance
  (implies (normp x f)
           (<= (abs (ndecode x f))
               (lpn f)))
  :hints (("Goal"
           :use nrepp-ndecode
           :in-theory (disable abs nrepp-ndecode)))
  :rule-classes :linear)

(defthm largest-lpn-instance-1
  (implies (normp x f)
           (<= (- (lpn f))
               (ndecode x f)))
  :hints (("Goal" :use largest-lpn-instance))
  :rule-classes :linear)

(defthm largest-lpn-instance-2
  (implies (normp x f)
           (<= (ndecode x f)
               (lpn f)))
  :hints (("Goal" :use largest-lpn-instance))
  :rule-classes :linear)

(defthm nrepp-decode
  (implies (normp x f)
           (nrepp (decode x f) f))
  :hints (("Goal" :in-theory (enable normp decode))))

(defthm nencode-decode
  (implies (normp x f)
           (equal (nencode (decode x f) f)
                  x))
  :hints (("Goal" :in-theory (enable normp decode))))

(defthm decode-nencode
  (implies (nrepp x f)
           (equal (decode (nencode x f) f)
                  x))
  :hints (("Goal"
           :use normp-nencode
           :in-theory (e/d (decode normp)
                           (normp-nencode)))))

(defthm nrepp-minus
  (equal (nrepp (- x) f) (nrepp x f))
  :hints (("Goal" :in-theory (enable nrepp))))

;; ======================================================================

;; Rounding lemmas

(defthmd exactp-larger-idx
  (implies (and (exactp x m)
                (<= m n)
                (integerp m)
                (integerp n))
           (exactp x n))
  :hints (("Goal"
           :use (:instance
                 integerp-*
                 (x (* x
                       (expt 2 (+ -1 m (- (expo x))))))
                 (y (expt 2 (- n m))))
           :in-theory (enable exactp sig))))

(defthmd rtz-exact
  (implies (and (exactp x n)
                (rationalp x)
                (posp n))
           (equal (rtz x n) x))
  :hints (("Goal" :use rtz-exactp-b)))

(defthmd bits-rtz-alt
  (implies (and (>= x 0)
                (posp k))
           (equal (rtz x k)
                  (* (expt 2 (- (1+ (expo x)) k))
                     (bits x
                           (expo x)
                           (- (1+ (expo x)) k)))))
  :hints (("Goal" :use (:instance bits-rtz
                                  (n (1+ (expo x)))))))

(defthm-nl rna-neg-bits
  (implies (and (< n 0)
                (integerp n))
           (equal (rna x n) 0))
  :hints (("Goal"
           :use (expo-upper-bound
                 (:instance fl-unique
                            (x (abs
                                (* x (expt 2 (+ -1 n (- (expo x)))))))
                            (n 0)))
           :in-theory (enable rna sig))))

(defthm-nl rna-0-bit-1
  (implies (and (<= (* 4 (spd (sp)))
                    (abs x))
                (< (abs x)
                   (* 8 (spd (sp))))
                (rationalp x))
           (equal (rna x 0)
                  (* (if (< x 0) -1 1)
                     (ddecode #x8 (sp)))))
  :hints (("Goal"
           :use (expo-lower-bound
                 (:instance expo-monotone
                            (x (* 4 (spd (sp))))
                            (y x))
                 (:instance expo-monotone
                            (y (* 8 (spd (sp)))))
                 (:instance fl-unique
                            (x (abs
                                (* x (expt 2 (+ -1 (- (expo x)))))))
                            (n 0)))
           :in-theory (enable rna sgn sig sp))))

(defthm-nl rna-0-bit-2
  (implies (and (<= (* 2 (spd (sp)))
                    (abs x))
                (< (abs x)
                   (* 4 (spd (sp))))
                (rationalp x))
           (equal (rna x 0)
                  (* (if (< x 0) -1 1)
                     (ddecode #x4 (sp)))))
  :hints (("Goal"
           :use (expo-lower-bound
                 (:instance expo-monotone
                            (x (* 2 (spd (sp))))
                            (y x))
                 (:instance expo-monotone
                            (y (* 4 (spd (sp)))))
                 (:instance fl-unique
                            (x (abs
                                (* x (expt 2 (+ -1 (- (expo x)))))))
                            (n 0)))
           :in-theory (enable rna sgn sig sp))))

(defthmd rto-exact
  (implies (and (exactp x n)
                (rationalp x)
                (posp n))
           (equal (rto x n) x))
  :hints (("Goal" :in-theory (enable rto-exactp-b))))

(defthm rto-norm
  (implies (and (normp x f)
                (equal n (prec f)))
           (equal (rto (ndecode x f) n)
                  (ndecode x f)))
  :hints (("Goal"
           :use nrepp-ndecode
           :in-theory (e/d (rto-exact
                            nrepp)
                           (nrepp-ndecode)))))

(encapsulate
  ()

  (local
   (defthm rto-non-pos-aux
     (implies (and (or (not (rationalp x))
                       (not (integerp n))
                       (< n 0))
                   (<= x 0)
                   (acl2-numberp (rto x n)))
              (<= (rto x n) 0))
     :hints (("Goal" :in-theory (enable rto rtz sgn)))
     :rule-classes :linear))

  (defthm rto-non-pos
    (implies (<= x 0)
             (<= (rto x n) 0))
    :hints (("Goal" :use (:instance rto-monotone
                                    (y 0))))
    :rule-classes :linear)

  (local
   (defthm rto-non-neg-aux
     (implies (and (or (not (rationalp x))
                       (not (integerp n))
                       (< n 0))
                   (<= 0 x)
                   (acl2-numberp (rto x n)))
              (<= 0 (rto x n)))
     :hints (("Goal" :in-theory (enable rto rtz sgn)))
     :rule-classes :linear))

  (defthm rto-non-neg
    (implies (<= 0 x)
             (<= 0 (rto x n)))
    :hints (("Goal" :use (:instance rto-monotone
                                    (x 0)
                                    (y x))))
    :rule-classes :linear))

(defthm rnd-positive-linear
  (implies (and (< 0 x)
                (rationalp x)
                (posp n)
                (common-mode-p mode))
           (< 0 (rnd x mode n)))
  :rule-classes :linear)

(defthm rnd-negative-linear
  (implies (and (< x 0)
                (rationalp x)
                (posp n)
                (common-mode-p mode))
           (< (rnd x mode n) 0))
  :rule-classes :linear)

(defthm rtz-lower-neg
  (implies (and (< x 0)
                (rationalp x)
                (integerp n))
           (<= x (rtz x n)))
  :hints (("Goal" :use rtz-upper-bound))
  :rule-classes :linear)

(defthm raz-upper-neg
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n)))
           (<= (raz x n) x))
  :hints (("Goal" :use raz-lower-bound))
  :rule-classes :linear)

(defthmd rnd-exactp-b-alt
  (implies (and (rationalp x)
                (common-mode-p mode)
                (posp n))
           (equal (equal (rnd x mode n) x)
                  (exactp x n)))
  :hints (("Goal" :in-theory (enable rnd-exactp-b))))

(defthmd rnd-exact
  (implies (and (exactp x n)
                (rationalp x)
                (common-mode-p mode)
                (posp n))
           (equal (rnd x mode n) x))
  :hints (("Goal" :in-theory (enable rnd-exactp-b))))

(defthmd rnd-shift-alt
  (implies (and (rationalp x)
                (integerp n)
                (common-mode-p mode)
                (integerp k))
           (and (equal (rnd (* x (expt 2 k)) mode n)
                       (* (rnd x mode n) (expt 2 k)))
                (equal (rnd (* (expt 2 k) x) mode n)
                       (* (rnd x mode n) (expt 2 k)))))
  :hints (("Goal" :use rnd-shift)))

(defthmd rnd-pow2
  (implies (and (integerp n)
                (common-mode-p mode)
                (integerp k))
           (equal (rnd (expt 2 k) mode n)
                  (* (rnd 1 mode n) (expt 2 k))))
  :hints (("Goal" :use (:instance rnd-shift (x 1)))))

(defthm rnd-lpn
  (implies (and (formatp f)
                (common-mode-p mode))
           (equal (rnd (lpn f) mode (prec f))
                  (lpn f)))
  :hints (("Goal"
           :use nrepp-lpn
           :in-theory (e/d (rnd-exact nrepp) (nrepp-lpn)))))

(defthm nrepp-rnd
  (implies (and (formatp f)
                (rationalp x)
                (common-mode-p mode)
                (<= (spn f) (abs x))
                (<= (abs x) (lpn f)))
           (nrepp (rnd x mode (prec f)) f))
  :hints (("Goal"
           :use ((:instance expo-rnd
                            (n (prec f)))
                 (:instance rnd-monotone
                            (y (lpn f))
                            (n (prec f)))
                 (:instance rnd-monotone
                            (x (- (lpn f)))
                            (y x)
                            (n (prec f)))
                 (:instance expo-minus
                            (x (rnd x mode (prec f))))
                 (:instance expo-monotone
                            (x (expt 2 (1+ (expo x))))
                            (y (lpn f)))
                 (:instance expo-monotone
                            (x (spn f))
                            (y x))
                 (:instance expo-monotone
                            (y (lpn f))))
           :in-theory (enable nrepp rnd-minus))))

(defthmd drnd-tiny-b-alt
  (implies (and (formatp f)
                (common-mode-p mode)
                (equal x (/ (spd f) 2)))
           (equal (drnd x mode f)
                  (if (member mode '(raz rup rna))
                      (spd f)
                    0)))
  :hints (("Goal" :use drnd-tiny-b)))

;; ======================================================================

;; Extend the rounding to the RTO mode

(defn ext-mode-p (mode)
  (or (common-mode-p mode)
      (equal mode 'rto)))

(defund flip-mode-ext (m)
  (declare (xargs :guard (ext-mode-p m)))
  (case m
    (rup 'rdn)
    (rdn 'rup)
    (t m)))

(defthm flip-mode-ext-=-flip-mode
  (equal (flip-mode-ext m)
         (flip-mode m))
  :hints (("Goal" :in-theory (enable flip-mode-ext
                                     flip-mode))))

(defun rnd-ext (x mode n)
  (declare (xargs :guard (and (real/rationalp x)
                              (ext-mode-p mode)
                              (integerp n))))
  (if (equal mode 'rto)
      (rto x n)
    (rnd x mode n)))

(defthm rna-neg-bits-alt
  (implies (and (< n 0)
                (integerp n))
           (equal (rnd-ext x 'rna n) 0))
  :hints (("Goal" :in-theory (enable rnd))))

(defthmd rnd-ext-shift
  (implies (and (rationalp x)
                (posp n)
                (ext-mode-p mode)
                (integerp k))
           (and (equal (rnd-ext (* x (expt 2 k)) mode n)
                       (* (rnd-ext x mode n) (expt 2 k)))
                (equal (rnd-ext (* (expt 2 k) x) mode n)
                       (* (rnd-ext x mode n) (expt 2 k)))))
  :hints (("Goal" :use (rnd-shift rto-shift))))

(defthmd rnd-ext-minus
  (equal (rnd-ext (- x) mode n)
         (- (rnd-ext x (flip-mode mode) n)))
  :hints (("Goal"
           :use (rnd-minus rto-minus)
           :in-theory (enable flip-mode))))

(defthmd rnd-ext-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (ext-mode-p mode)
                (integerp n)
                (> n 0))
           (<= (rnd-ext x mode n) (rnd-ext y mode n)))
  :hints (("Goal" :use (rnd-monotone rto-monotone)))
  :rule-classes :linear)

(defthm rnd-ext-non-pos
  (implies (<= x 0)
           (<= (rnd-ext x mode n) 0))
  :rule-classes :linear)

(defthm rnd-ext-non-neg
  (implies (<= 0 x)
           (<= 0 (rnd-ext x mode n)))
  :rule-classes :linear)

(defthm rnd-ext-positive
  (implies (and (< 0 x)
                (rationalp x)
                (posp n)
                (ext-mode-p mode))
           (< 0 (rnd-ext x mode n)))
  :hints (("Goal" :in-theory (enable rnd-ext ext-mode-p)))
  :rule-classes :linear)

(defthm rnd-ext-negative
  (implies (and (< x 0)
                (rationalp x)
                (posp n)
                (ext-mode-p mode))
           (< (rnd-ext x mode n) 0))
  :hints (("Goal" :in-theory (enable rnd-ext ext-mode-p)))
  :rule-classes :linear)

(defthm rnd-ext-exactp-c
  (implies (and (rationalp x)
                (ext-mode-p mode)
                (integerp n)
                (> n 0)
                (rationalp a)
                (exactp a n)
                (>= a x))
           (>= a (rnd-ext x mode n)))
  :hints (("Goal"
           :use rnd-exactp-c
           :in-theory (enable rto-exact rto-monotone)))
  :rule-classes nil)

(defthm rnd-ext-exactp-d
  (implies (and (rationalp x)
                (ext-mode-p mode)
                (integerp n)
                (> n 0)
                (rationalp a)
                (exactp a n)
                (<= a x))
           (<= a (rnd-ext x mode n)))
  :hints (("Goal"
           :use rnd-exactp-d
           :in-theory (enable rto-exact rto-monotone)))
  :rule-classes nil)

(defthmd rnd-ext-exact
  (implies (and (exactp x n)
                (rationalp x)
                (ext-mode-p mode)
                (posp n))
           (equal (rnd-ext x mode n) x))
  :hints (("Goal" :in-theory (enable rnd-ext rnd-exact rto-exact))))

(defun roundup-ext-pos (x e sticky mode n)
  (declare (xargs :guard (and (integerp x)
                              (integerp e)
                              (integerp sticky)
                              (ext-mode-p mode)
                              (integerp n))))
  (case mode
    (rto (and (= (bitn x (- (1+ e) n))
                 0)
              (or (not (= (bits x (- e n) 0)
                          0))
                  (= sticky 1))))
    (otherwise (roundup-pos x e sticky mode n))))

(local
 (defthmd fl-to-rtz
   (implies (and (rationalp z)
                 (> z 0))
            (equal (fl z) (rtz z (1+ (expo z)))))
   :hints (("Goal"
            :in-theory (e/d (rtz sgn) ())
            :use ((:instance fp-rep
                             (x z)))))))

(local
 (defthmd roundup-ext-pos-thm-aux
   (implies (and (rationalp z)
                 (<= 0 z)
                 (integerp n))
            (equal (rtz z n)
                   (if (equal (bitn z (- (1+ (expo z)) n))
                              0)
                       (rtz z (1- n))
                     (+ (rtz z (1- n))
                        (expt 2 (- (1+ (expo z)) n))))))
   :hints (("Goal"
            :use (:instance
                  mod-def
                  (x (fl (* z
                            (expt 2 (+ -1 n (- (expo z)))))))
                  (y 2))
            :in-theory (enable rtz
                               sgn
                               sig
                               bitn-def)))))

(defthmd roundup-ext-pos-thm
  (implies
   (and (ext-mode-p mode)
        (rationalp z)
        (not (zp n))
        (<= (expt 2 n) z))
   (let ((x (fl z))
         (sticky (if (integerp z) 0 1)))
     (equal (rnd-ext z mode n)
            (if (roundup-ext-pos x (expo x) sticky mode n)
                (fp+ (rtz x n) n)
              (rtz x n)))))
  :hints (("Goal"
           :use (roundup-ext-pos-thm-aux
                 (:instance bitn-shift-down
                            (x z)
                            (k 0)
                            (i (- (1+ (expo z)) n)))
                 (:instance exactp-larger-idx
                            (x z)
                            (m (1- n)))
                 (:instance expo-monotone
                            (x (expt 2 n))
                            (y z)))
           :in-theory (enable rtz-exact
                              rto
                              fl-to-rtz
                              sgn
                              roundup-pos-thm-1
                              roundup-pos-thm-2))))

;; Subnormal rounding

(defund drnd-ext (x mode f)
  (declare (xargs :guard (and (real/rationalp x)
                              (ext-mode-p mode)
                              (formatp f))))
  (rnd-ext x
           mode
           (+ (prec f) (expo x) (- (expo (spn f))))))

(defthmd drnd-ext-to-drnd
  (implies (not (equal mode 'rto))
           (equal (drnd-ext x mode f)
                  (drnd x mode f)))
  :hints (("Goal" :in-theory (enable drnd-ext drnd))))

(encapsulate
  ()

  (local
   (defthmd-nl drnd-ext-rewrite-aux-1
     (implies (and (formatp f)
                   (rationalp x)
                   (<= (abs x) (spn f)))
              (equal (exactp x
                             (+ -1
                                (expo x)
                                (prec f)
                                (- (expo (spn f)))))
                     (exactp (+ x (* (sgn x) (spn f)))
                             (+ -1 (prec f)))))
     :hints (("Goal"
              :use (:instance expo-unique
                              (x (+ x (* (sgn x) (spn f))))
                              (n (expo (spn f))))
              :in-theory (e/d (sgn spn exactp2)
                              (acl2::prefer-positive-addends-equal))))))

  (local
   (defthm-nl drnd-ext-rewrite-aux-2
     (implies (and (formatp f)
                   (rationalp x)
                   (<= (abs x) (spn f)))
              (equal (rtz x
                          (+ -2
                             (bias f)
                             (expo x)
                             (prec f)))
                     (- (rtz (+ x (* (sgn x) (spn f)))
                             (+ -1 (prec f)))
                        (* (sgn x) (spn f)))))
     :hints (("Goal"
              :use ((:instance plus-rtz
                               (x (spn f))
                               (y (* (sgn x) x))
                               (k (+ -1
                                     (expo x)
                                     (prec f)
                                     (- (expo (spn f))))))
                    (:instance expo-unique
                               (x (+ (spn f) (* (sgn x) x)))
                               (n (expo (spn f))))
                    (:instance rtz-minus
                               (x (- (spn f) x))
                               (n (1- (prec f))))
                    (:instance rtz-minus
                               (n (+ -1
                                     (expo x)
                                     (prec f)
                                     (- (expo (spn f)))))))
              :in-theory (e/d (rtz-exact sgn spn exactp2)
                              (acl2::prefer-positive-addends-equal))))))

  (local
   (defthm-nl drnd-ext-rewrite-aux-3
     (implies (and (equal mode 'rto)
                   (formatp f)
                   (rationalp x)
                   (<= (abs x) (spn f)))
              (equal (drnd-ext x mode f)
                     (- (rnd-ext (+ x (* (sgn x) (spn f)))
                                 mode
                                 (prec f))
                        (* (sgn x) (spn f)))))
     :hints (("Goal"
              :use (drnd-ext-rewrite-aux-1
                    (:instance expo-unique
                               (x (+ x (* (sgn x) (spn f))))
                               (n (expo (spn f)))))
              :in-theory (enable drnd-ext
                                 rto
                                 sgn
                                 spn
                                 exactp2)))))

  (defthmd drnd-ext-rewrite
    (implies (and (formatp f)
                  (rationalp x)
                  (<= (abs x) (spn f))
                  (ext-mode-p mode))
             (equal (drnd-ext x mode f)
                    (- (rnd-ext (+ x (* (sgn x) (spn f)))
                                mode
                                (prec f))
                       (* (sgn x) (spn f)))))
    :hints (("Goal"
             :use drnd-ext-to-drnd
             :in-theory (enable drnd-rewrite))))
  )

(defthmd drnd-ext-minus
  (equal (drnd-ext (- x) mode f)
         (- (drnd-ext x (flip-mode mode) f)))
  :hints (("Goal"
           :cases ((rationalp x))
           :use (:instance rnd-ext-minus
                           (n (+ (prec f)
                                 (expo (- x))
                                 (- (expo (spn f))))))
           :in-theory (enable drnd-ext expo))))

(local
 (defthm-nl++ drnd-ext-tiny-a-aux
   (implies (and (formatp f)
                 (rationalp x)
                 (< 0 x)
                 (< x (expt 2 (+ 1 (- (bias f)) (- (prec f))))))
            (not (exactp x (+ -2 (bias f) (expo x) (prec f)))))
   :hints (("Goal" :in-theory (enable exactp2)))))

(local
 (defthm-nl++ drnd-ext-tiny-aux
   (implies (and (formatp f)
                 (rationalp x)
                 (< 0 x)
                 (< x (expt 2 (+ 2 (- (bias f)) (- (prec f))))))
            (not (exactp x (+ -2 (bias f) (expo x) (prec f)))))
   :hints (("Goal" :in-theory (enable exactp2)))))

(defthmd drnd-ext-tiny-a
  (implies (and (formatp f)
                (ext-mode-p mode)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd f) 2)))
           (equal (drnd-ext x mode f)
                  (if (member mode '(raz rup rto))
                      (spd f)
                    0)))
  :hints (("Goal"
           :use (drnd-tiny-a
                 (:instance
                  expo-monotone
                  (y (expt 2 (+ 1 (- (bias f)) (- (prec f)))))))
           :in-theory (enable drnd-ext drnd rto spd spn))))

(defthmd drnd-ext-tiny-b
  (implies (and (formatp f)
                (ext-mode-p mode)
                (equal x (/ (spd f) 2)))
           (equal (drnd-ext x mode f)
                  (if (member mode '(raz rup rna rto))
                      (spd f)
                    0)))
  :hints (("Goal"
           :use drnd-tiny-b-alt
           :in-theory (enable drnd-ext drnd rto spd spn exactp2))))

(defthmd drnd-ext-tiny-c
  (implies (and (formatp f)
                (ext-mode-p mode)
                (rationalp x)
                (< (/ (spd f) 2) x)
                (< x (spd f)))
           (equal (drnd-ext x mode f)
                  (if (member mode '(rtz rdn))
                      0
                    (spd f))))
  :hints (("Goal"
           :use (drnd-tiny-c
                 (:instance
                  expo-monotone
                  (y (expt 2 (+ 2 (- (bias f)) (- (prec f)))))))
           :in-theory (enable drnd-ext drnd rto sgn spd spn))))

(in-theory (disable ext-mode-p rnd-ext))
