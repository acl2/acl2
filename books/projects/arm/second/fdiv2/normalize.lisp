;; Cuong Chau <cuong.chau@arm.com>

;; January 2021

;; This book analyzes function NORMALIZE.

(in-package "RTL")

(include-book "special")

(local (arith-5-for-rtl))

(local
 (in-theory (disable acl2::reduce-multiplicative-constant-<
                     acl2::integerp-<-constant
                     acl2::|(< x (/ y)) with (< 0 y)|
                     neg-bitn-0
                     acl2::simplify-products-gather-exponents-<)))

;; ======================================================================

(defundd a () (decode (opaw) (f)))

(defundd b () (decode (opbw) (f)))

(defthm nonzero-a
  (implies (not (specialp))
           (not (equal (a) 0)))
  :hints (("Goal" :in-theory (enable specialp
                                     a
                                     opaw
                                     fmtw
                                     decode
                                     ddecode
                                     ndecode
                                     expf
                                     manf
                                     f
                                     classa
                                     analyze))))

(defthm nonzero-b
  (implies (not (specialp))
           (not (equal (b) 0)))
  :hints (("Goal" :in-theory (enable specialp
                                     b
                                     opbw
                                     fmtw
                                     decode
                                     ddecode
                                     ndecode
                                     expf
                                     manf
                                     f
                                     classb
                                     analyze))))

(bvecthm bvecp-expa
  (bvecp (expa) (expw (f)))
  :hints (("Goal" :in-theory (enable expa f analyze))))

(defthm expa-upper-bounds
  (and (implies (equal (fnum) 1)
                (< (expa) *2^5*))
       (implies (equal (fnum) 2)
                (< (expa) *2^8*))
       (implies (equal (fnum) 3)
                (< (expa) *2^11*)))
  :hints (("Goal"
           :use bvecp-expa
           :in-theory (enable f)))
  :rule-classes :linear)

(bvecthm bvecp-expb
  (bvecp (expb) (expw (f)))
  :hints (("Goal" :in-theory (enable expb f analyze))))

(defthm expb-upper-bounds
  (and (implies (equal (fnum) 1)
                (< (expb) *2^5*))
       (implies (equal (fnum) 2)
                (< (expb) *2^8*))
       (implies (equal (fnum) 3)
                (< (expb) *2^11*)))
  :hints (("Goal"
           :use bvecp-expb
           :in-theory (enable f)))
  :rule-classes :linear)

(bvecthm bvecp-mana
  (bvecp (mana) (sigw (f)))
  :hints (("Goal" :in-theory (enable mana f analyze))))

(defthm mana-upper-bounds
  (and (implies (equal (fnum) 1)
                (< (mana) *2^10*))
       (implies (equal (fnum) 2)
                (< (mana) *2^23*))
       (implies (equal (fnum) 3)
                (< (mana) *2^52*)))
  :hints (("Goal"
           :use bvecp-mana
           :in-theory (enable f)))
  :rule-classes :linear)

(bvecthm bvecp-manb
  (bvecp (manb) (sigw (f)))
  :hints (("Goal" :in-theory (enable manb f analyze))))

(defthm manb-upper-bounds
  (and (implies (equal (fnum) 1)
                (< (manb) *2^10*))
       (implies (equal (fnum) 2)
                (< (manb) *2^23*))
       (implies (equal (fnum) 3)
                (< (manb) *2^52*)))
  :hints (("Goal"
           :use bvecp-manb
           :in-theory (enable f)))
  :rule-classes :linear)

(bvecthm bvecp53-siga
  (bvecp (siga) 53)
  :hints (("Goal" :in-theory (enable siga normalize))))

(bvecthm bvecp53-sigb
  (bvecp (sigb) 53)
  :hints (("Goal" :in-theory (enable sigb normalize))))

(defthm natp-expashft
  (natp (expashft))
  :hints (("Goal" :in-theory (enable expashft)))
  :rule-classes :type-prescription)

(defthm natp-expbshft
  (natp (expbshft))
  :hints (("Goal" :in-theory (enable expbshft)))
  :rule-classes :type-prescription)

(bvecthm bvecp13-expq-1
  (bvecp (expq-1) 13)
  :hints (("Goal" :in-theory (enable expq-1 normalize))))

(defthm bs-rewrite
  (equal (bs) (bias (f)))
  :hints (("Goal" :in-theory (enable bs f))))

(defthm natp-bias
  (natp (bias (f)))
  :hints (("Goal" :in-theory (enable f)))
  :rule-classes :type-prescription)

(local
 (def-gl-rule clz53-expo
   :hyp (and (bvecp x 53) (not (equal x 0)))
   :concl (equal (clz53 x) (- 52 (expo x)))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 53))))

(local
 (defthm aux-1
   (implies (and (rationalp x)
                 (not (equal x 0)))
            (and (equal (expo (* *2^29* x))
                        (+ 29 (expo x)))
                 (equal (expo (* *2^42* x))
                        (+ 42 (expo x)))))
   :hints (("Goal"
            :use ((:instance expo-shift
                             (n 29))
                  (:instance expo-shift
                             (n 42)))
            :in-theory (disable expo-shift)))))

(local
 (defthm aux-2-hp
   (implies (and (< (abs x) *2^10*)
                 (rationalp x))
            (<= (expo x) 10))
   :hints (("Goal" :use (:instance expo-monotone
                                   (y *2^10*))))
   :rule-classes :linear))

(local
 (defthm aux-2-sp
   (implies (and (< (abs x) *2^23*)
                 (rationalp x))
            (<= (expo x) 23))
   :hints (("Goal" :use (:instance expo-monotone
                                   (y *2^23*))))
   :rule-classes :linear))

(local
 (defthm aux-2-dp
   (implies (and (< (abs x) *2^52*)
                 (rationalp x))
            (<= (expo x) 52))
   :hints (("Goal" :use (:instance expo-monotone
                                   (y *2^52*))))
   :rule-classes :linear))

(local
 (defthm-nl aux-3
   (implies (bvecp x 52)
            (equal (bits (* x (expt 2 (+ 52 (- (expo x)))))
                         52 0)
                   (* x (expt 2 (+ 52 (- (expo x)))))))
   :hints (("Goal"
            :use (aux-2-dp
                  expo-upper-bound)
            :in-theory (enable bvecp)))))

(defthmd spec-fields
  (and (equal (signa) (sgnf (opaw) (f)))
       (equal (expa) (expf (opaw) (f)))
       (equal (mana) (manf (opaw) (f)))
       (equal (signb) (sgnf (opbw) (f)))
       (equal (expb) (expf (opbw) (f)))
       (equal (manb) (manf (opbw) (f))))
  :hints (("Goal"
           :in-theory (enable sgnf
                              expf
                              manf
                              opaw
                              opbw
                              fmtw
                              f
                              signa
                              signb
                              expa
                              expb
                              mana
                              manb
                              si
                              bitn-bits
                              analyze))))

;; a

(local
 (defthmd abs-a-rewrite
   (implies (not (specialp))
            (equal (abs (a))
                   (* (expt 2 (+ (si (expashft) 13) (- (bias (f))) -52))
                      (siga))))
   :hints (("Goal"
            :in-theory (e/d (specialp
                             a
                             expashft
                             siga
                             siga-1
                             f
                             opaw
                             fmtw
                             expa
                             expf
                             mana
                             manf
                             classa
                             decode
                             ddecode
                             ndecode
                             clz53-expo
                             cat
                             si
                             bvecp
                             analyze
                             normalize)
                            (acl2::|(expt x (if a b c))|
                             acl2::default-expt-2
                             acl2::default-plus-1
                             acl2::default-plus-2
                             acl2::default-times-1
                             acl2::default-times-2))))))

(local
 (defthmd si-expashft-aux-1
   (implies (and (not (specialp))
                 (equal x (opaw))
                 (equal f (f))
                 (equal (expf x f) 0))
            (denormp x f))
   :hints (("Goal" :in-theory (enable specialp
                                      denormp
                                      opaw
                                      fmtw
                                      f
                                      classa
                                      expf
                                      manf
                                      encodingp
                                      analyze)))))

(local
 (defthmd si-expashft-aux-2
   (implies (and (not (specialp))
                 (equal x (opaw))
                 (equal f (f))
                 (not (equal (expf x f) 0)))
            (normp x f))
   :hints (("Goal" :in-theory (enable specialp
                                      normp
                                      opaw
                                      fmtw
                                      f
                                      classa
                                      expf
                                      manf
                                      encodingp
                                      analyze)))))

(local
 (defthmd si-expashft
   (implies (not (specialp))
	    (equal (si (expashft) 13)
	           (+ (expo (a)) (bias (f)))))
   :hints (("Goal"
            :in-theory (enable specialp
                               expashft
                               a
                               si
                               f
                               opaw
                               fmtw
                               expa
                               mana
                               classa
                               siga-1
                               decode
                               expf
                               manf
                               clz53-expo
                               si-expashft-aux-1
                               si-expashft-aux-2
                               cat
                               bvecp
                               analyze
                               normalize)))))

(defthmd siga-rewrite
  (implies (not (specialp))
	   (equal (siga) (* *2^52* (sig (a)))))
  :hints (("Goal"
           :use abs-a-rewrite
           :in-theory (e/d (si-expashft
                            fp-abs-rewrite)
                           (abs)))))

;; b

(local
 (defthmd abs-b-rewrite
   (implies (not (specialp))
            (equal (abs (b))
                   (* (expt 2 (+ (si (expbshft) 13) (- (bias (f))) -52))
                      (sigb))))
   :hints (("Goal"
            :in-theory (e/d (specialp
                             b
                             expbshft
                             sigb
                             sigb-1
                             f
                             opbw
                             fmtw
                             expb
                             expf
                             manb
                             manf
                             classb
                             decode
                             ddecode
                             ndecode
                             clz53-expo
                             cat
                             si
                             bvecp
                             analyze
                             normalize)
                            (acl2::|(expt x (if a b c))|
                             acl2::default-expt-2
                             acl2::default-plus-1
                             acl2::default-plus-2
                             acl2::default-times-1
                             acl2::default-times-2))))))

(local
 (defthmd si-expbshft-aux-1
   (implies (and (not (specialp))
                 (equal x (opbw))
                 (equal f (f))
                 (equal (expf x f) 0))
            (denormp x f))
   :hints (("Goal" :in-theory (enable specialp
                                      denormp
                                      opbw
                                      fmtw
                                      f
                                      classb
                                      expf
                                      manf
                                      encodingp
                                      analyze)))))

(local
 (defthmd si-expbshft-aux-2
   (implies (and (not (specialp))
                 (equal x (opbw))
                 (equal f (f))
                 (not (equal (expf x f) 0)))
            (normp x f))
   :hints (("Goal" :in-theory (enable specialp
                                      normp
                                      opbw
                                      fmtw
                                      f
                                      classb
                                      expf
                                      manf
                                      encodingp
                                      analyze)))))

(local
 (defthmd si-expbshft
   (implies (not (specialp))
	    (equal (si (expbshft) 13)
	           (+ (expo (b)) (bias (f)))))
   :hints (("Goal"
            :in-theory (enable specialp
                               expbshft
                               b
                               si
                               f
                               opbw
                               fmtw
                               expb
                               manb
                               classb
                               sigb-1
                               decode
                               expf
                               manf
                               clz53-expo
                               si-expbshft-aux-1
                               si-expbshft-aux-2
                               cat
                               bvecp
                               analyze
                               normalize)))))

(defthmd sigb-rewrite
  (implies (not (specialp))
	   (equal (sigb) (* *2^52* (sig (b)))))
  :hints (("Goal"
           :use abs-b-rewrite
           :in-theory (e/d (si-expbshft
                            fp-abs-rewrite)
                           (abs)))))

;; |a/b|

(local
 (defthmd si-expq-1-rewrite
   (equal (si (expq-1) 13)
          (+ (si (expashft) 13)
             (- (si (expbshft) 13))
             (bias (f))))
   :hints (("Goal" :in-theory (enable expq-1
                                      expashft
                                      expbshft
                                      f
                                      si
                                      siga-1
                                      sigb-1
                                      normalize
                                      bvecp)))))

(local
 (defthm si-expashft-bounds
   (implies (not (specialp))
            (and (<= -51 (si (expashft) 13))
                 (< (si (expashft) 13) *2^11*)))
   :hints (("Goal" :in-theory (e/d (specialp
                                    expashft
                                    si
                                    siga-1
                                    expa
                                    mana
                                    classa
                                    cat
                                    bvecp
                                    clz53-expo
                                    analyze)
                                   (acl2::default-less-than-1))))
   :rule-classes :linear))

(local
 (defthm si-expbshft-bounds
   (implies (not (specialp))
            (and (<= -51 (si (expbshft) 13))
                 (< (si (expbshft) 13) *2^11*)))
   :hints (("Goal" :in-theory (e/d (specialp
                                    expbshft
                                    si
                                    sigb-1
                                    expb
                                    manb
                                    classb
                                    cat
                                    bvecp
                                    clz53-expo
                                    analyze)
                                   (acl2::default-less-than-1))))
   :rule-classes :linear))

(defthm si-expq-1-bounds
  (implies (not (specialp))
	   (and (<= -2083 (si (expq-1) 13))
	        (<= (si (expq-1) 13) 3121)))
  :hints (("Goal" :in-theory (enable si-expq-1-rewrite f)))
  :rule-classes :linear)

(local
 (defthm aux-4
   (implies (and (rationalp x)
                 (rationalp y))
            (equal (abs (/ x y))
                   (/ (abs x) (abs y))))))

(defthmd quotient-formula
  (implies (not (specialp))
           (equal (abs (/ (a) (b)))
	          (* (expt 2 (- (si (expq-1) 13) (bias (f))))
		     (/ (siga) (sigb)))))
  :hints (("Goal"
           :in-theory (e/d (abs-a-rewrite
                            abs-b-rewrite
                            si-expq-1-rewrite)
                           (abs)))))

