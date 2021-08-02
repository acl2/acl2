;; Cuong Chau <cuong.chau@arm.com>

;; March 2021

(in-package "RTL")

(include-book "induct")

(local (arith-5-for-rtl))
(local (include-book "ihs/logops-lemmas" :dir :system))

;; ======================================================================

;; Prove si(rfinal, 57) = 2^55 * rmd(n),
;; and rplusdis0 = rmd(n) == -d ? 1 : 0

(local
 (def-gl-rule si-rfinal-rewrite-aux
   :hyp (and (bvecp x 57)
             (bvecp y 57)
             (< (abs (+ (si x 57) (si y 57)))
                *2^56*))
   :concl (equal (si (bits (+ x y) 56 0) 57)
                 (+ (si x 57) (si y 57)))
   :g-bindings (gl::auto-bindings
                (:mix (:nat x 57) (:nat y 57)))))

(defthmd si-rfinal-rewrite
  (implies (not (specialp))
           (equal (si (rfinal) 57)
                  (* *2^55* (rmd (n)))))
  :hints (("Goal"
           :use ((:instance rmd-rewrite (j (n)))
                 (:instance rmd-bounds (j (n))))
           :in-theory (enable rfinal rsf-rewrite rcf-rewrite))))

(local
 (def-gl-rule rplusdis0-rewrite-aux
   :hyp (and (bvecp x 57)
             (bvecp y 57)
             (bvecp z 56))
   :concl (b* ((s (logxor (logxor x y) z))
               (c (bits (ash (logior (logior (logand x y)
                                             (logand x z))
                                     (logand y z))
                             1)
                        56 0)))
            (equal (equal (logxor s c)
                          (bits (ash (logior s c) 1)
                                56 0))
                   (equal (si (bits (+ x y) 56 0) 57)
                          (- z))))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:mix (:nat x 57)
                      (:nat y 57)
                      (:seq (:nat z 56) (:skip 1))))))

(defthmd rplusdis0-rewrite
  (implies (not (specialp))
           (equal (rplusdis0)
                  (if (equal (rmd (n)) (- (d)))
                      1 0)))
  :hints (("Goal"
           :use (si-rfinal-rewrite
                 (:instance rplusdis0-rewrite-aux
                           (x (rsf))
                           (y (rcf))
                           (z (d57))))
           :in-theory (enable rnonzero
                              rplusdis0
                              rplusdxor
                              rplusdor
                              rfinal
                              rplusds
                              rplusdc
                              rsf-rewrite
                              rcf-rewrite
                              d57-rewrite))))

;; ======================================================================

;; Prove quot(j) = 2^54 * quotient(j),
;; and quotm1(j) = quot(j) - 2^(55 - j)

(bvecthm bvecp55-quot
  (bvecp (quot j) 55)
  :hints (("Goal"
           :expand (quot j)
           :in-theory (enable nextquot))))

(bvecthm bvecp55-quotm1
  (bvecp (quotm1 j) 55)
  :hints (("Goal"
           :expand (quotm1 j)
           :in-theory (enable nextquot))))

(local
 (defthmd aux-1
   (implies (and (equal (bits x (- 55 j) 0) 0)
                 (integerp j))
            (equal (bits x (- 54 j) 0) 0))
   :hints (("Goal" :use (:instance bitn-plus-bits
                                   (m 0)
                                   (n (- 55 j)))))))

(defthmd bits-quot&quotm1-0
  (implies (posp j)
           (and (equal (bits (quot j) (- 54 j) 0) 0)
                (equal (bits (quotm1 j) (- 54 j) 0) 0)))
  :hints (("Goal"
           :induct (induct-on-index j)
           :in-theory (e/d (quot
                            quotm1
                            nextquot
                            cat
                            aux-1)
                           (bits-tail-gen
                            bits-neg-indices
                            acl2::default-plus-1
                            acl2::default-plus-2
                            bits-bits)))
          ("Subgoal *1/2"
           :use ((:instance bits-shift-up-2
                            (x (1+ (* 2 (bits (quot (1- j))
                                              54
                                              (- 56 j)))))
                            (i -1)
                            (k (- 55 j)))
                 (:instance bits-shift-up-2
                            (x (1+ (* 2 (bits (quotm1 (1- j))
                                              54
                                              (- 56 j)))))
                            (i -1)
                            (k (- 55 j)))
                 (:instance bits-shift-up-2
                            (x (bits (quot (1- j))
                                     54
                                     (- 56 j)))
                            (i -2)
                            (k (- 56 j)))
                 (:instance bits-shift-up-2
                            (x (bits (quotm1 (1- j))
                                     54
                                     (- 56 j)))
                            (i -2)
                            (k (- 56 j)))))))

(local
 (defthm quot&quotm1-rewrite-aux
   (implies (and (bitp i)
                 (natp j)
                 (< 1 j)
                 (<= j (n)))
            (and (equal (cat (bits (quot (+ -1 j)) 54 (+ 56 (- j)))
                             (+ -1 j)
                             (cat i 1
                                  (quot (+ -1 j))
                                  (+ 55 (- j)))
                             (+ 56 (- j)))
                        (+ (quot (+ -1 j))
                           (* i (expt 2 (+ 55 (- j))))))
                 (equal (cat (bits (quotm1 (+ -1 j)) 54 (+ 56 (- j)))
                             (+ -1 j)
                             (cat i 1
                                  (quotm1 (+ -1 j))
                                  (+ 55 (- j)))
                             (+ 56 (- j)))
                        (+ (quotm1 (+ -1 j))
                           (* i (expt 2 (+ 55 (- j))))))))
   :hints (("Goal"
            :use ((:instance bits-quot&quotm1-0
                             (j (1- j)))
                  (:instance bits-plus-bits
                             (x (quot (+ -1 j)))
                             (m 0)
                             (n 54)
                             (p (+ 56 (- j))))
                  (:instance bits-plus-bits
                             (x (quotm1 (+ -1 j)))
                             (m 0)
                             (n 54)
                             (p (+ 56 (- j)))))
            :in-theory (enable cat aux-1 bvecp)))))

(defthmd quot&quotm1-rewrite
  (implies (and (posp j)
                (<= j (n)))
           (and (equal (quot j)
                       (* *2^54* (quotient j)))
                (equal (quotm1 j)
                       (- (quot j) (expt 2 (- 55 j))))))
  :hints (("Goal"
           :expand ((quotient 1)
                    (q 1))
           :in-theory (e/d (quot
                            quotm1
                            quotient
                            nextquot
                            bvecp)
                           (bvecp-bitn-1
                            bvecp-bitn-0
                            bits-tail-gen
                            bits-neg-indices
                            acl2::default-plus-1
                            acl2::default-plus-2
                            acl2::|(* (if a b c) x)|
                            acl2::|(+ x (if a b c))|
                            acl2::zp-open)))))

;; ======================================================================

;; Connect qtrunc and stk with x/d and p

(defundd divpow2 ()
  (equal (manb) 0))

(defthmd d-1
  (implies (and (not (specialp))
                (divpow2))
           (equal (d) 1))
  :hints (("Goal" :in-theory (e/d (specialp
                                   divpow2
                                   d
                                   b
                                   f
                                   b-class
                                   zerp
                                   opbz
                                   opbw
                                   fmtw
                                   manb
                                   decode
                                   ddecode
                                   ndecode
                                   normp
                                   denormp
                                   encodingp
                                   sig
                                   expf
                                   manf
                                   analyze)
                                  (expo-int
                                   acl2::integerp-minus-x
                                   acl2::|(< y (+ (- c) x))|
                                   acl2::prefer-positive-addends-<
                                   acl2::|(< (+ (- c) x) y)|
                                   acl2::|(+ x (if a b c))|
                                   acl2::|(+ (if a b c) x)|
                                   acl2::member-of-cons)))))

(local
 (encapsulate
   ()

   (local
    (defthmd-nl qtrunc-rewrite-gen-1-aux-1
      (implies (and (<= (si (expq-1) 13) 0)
                    (not (specialp))
                    (divpow2))
               (equal (qtrunc)
	              (fl (* (expt 2 (+ (prec (f))
                                        (si (expq-1) 13)))
                             (/ (x) (d))))))
      :hints (("Goal"
               :use (natp-2^prec-1*x
                     (:instance fl-unique
                                (x (* (sig (a))
                                      (expt 2 (+ -2 (si (expq-1) 13)))))
                                (n 0)))
               :in-theory (e/d (divpow2
                                qtrunc
                                fdivlane-segment-result-expand
                                qtrunc-segment
                                qtrunc-2
                                f
                                x
                                d-1
                                siga-rewrite
                                shft
                                mod-to-fl
                                bits-to-mod-fl)
                               (acl2::default-expt-2
                                acl2::default-plus-2))))))

   (local
    (defthmd qtrunc-rewrite-gen-1-aux-2
      (implies (and (> (si (expq-1) 13) 0)
                    (not (specialp))
                    (divpow2))
               (equal (qtrunc)
	              (* (expt 2 (1+ (prec (f))))
                         (/ (x) (d)))))
      :hints (("Goal"
               :use natp-2^prec-1*x
               :in-theory (enable divpow2
                                  qtrunc
                                  fdivlane-segment-result-expand
                                  qtrunc-segment
                                  qtrunc-2
                                  f
                                  x
                                  d-1
                                  siga-rewrite
                                  bvecp)))))

   (defthmd qtrunc-rewrite-gen-1
     (implies (and (not (specialp))
                   (divpow2))
              (equal (qtrunc)
                     (if (<= (si (expq-1) 13) 0)
                         (fl (* (expt 2 (+ (prec (f))
                                           (si (expq-1) 13)))
                                (/ (x) (d))))
                       (* (expt 2 (1+ (prec (f))))
                          (/ (x) (d))))))
     :hints (("Goal" :use (qtrunc-rewrite-gen-1-aux-1
                           qtrunc-rewrite-gen-1-aux-2))))))

(bvecthm bvecp55-qtrunc
  (bvecp (qtrunc) 55)
  :hints (("Goal" :in-theory (enable qtrunc
                                     fdivlane-segment-result-expand
                                     qtrunc-segment
                                     qtrunc-2))))

(local
 (defthmd stk-rewrite-gen-1-1
   (implies (and (<= (si (expq-1) 13) 0)
                 (not (specialp))
                 (divpow2))
	    (equal (stk)
                   (if (and (< -54 (si (expq-1) 13))
                            (equal (bits (* *2^54*
                                            (/ (x) (d)))
                                         (- (si (expq-1) 13))
                                         0)
                                   0)
                            (equal (bits (* (expt 2 (+ 53 (si (expq-1) 13)))
                                            (/ (x) (d)))
                                         (- 52 (prec (f)))
                                         0)
                                   0)
                            (equal (bitn (* (expt 2 (+ (prec (f))
                                                       (si (expq-1) 13)))
                                            (/ (x) (d)))
                                         0)
                                   0))
                       0 1)))
   :hints (("Goal"
            :use (natp-2^prec-1*x
                  (:instance bitn-shift-up
                             (x (bits (* (sig (a))
                                         (expt 2 (+ 53 (si (expq-1) 13))))
                                      54 0))
                             (k (- (prec (f)) 53))
                             (n (- 53 (prec (f)))))
                  (:instance bitn-shift-up
                             (x (* (sig (a))
                                   (expt 2 (+ (prec (f)) (si (expq-1) 13)))))
                             (k (- 53 (prec (f))))
                             (n 0))
                  (:instance bits-mod
                             (x  (* *2^54*
                                    (/ (x) (d))))
                             (i (- (si (expq-1) 13)))))
            :in-theory (e/d (divpow2
                             stk
                             fdivlane-segment-result-expand
                             qtrunc-segment
                             stk-segment
                             qtrunc
                             qtrunc-2
                             x
                             d-1
                             siga-rewrite
                             shft
                             f
                             bitn-bits
                             bvecp)
                            (acl2::default-expt-2
                             acl2::default-plus-2
                             acl2::logand-with-mask
                             bits-tail-gen))))))

(local
 (defthmd stk-rewrite-gen-1-2
   (implies (and (> (si (expq-1) 13) 0)
                 (not (specialp))
                 (divpow2))
	    (equal (stk) 0))
   :hints (("Goal"
            :use (natp-2^prec-1*x
                  (:instance bits-shift-up-2
                             (x (* (expt 2 (1- (prec (f)))) (x)))
                             (i -3)
                             (k (- 55 (prec (f))))))
            :in-theory (enable divpow2
                               stk
                               fdivlane-segment-result-expand
                               qtrunc-segment
                               stk-segment
                               qtrunc-rewrite-gen-1
                               qtrunc-2
                               x
                               d-1
                               siga-rewrite
                               f
                               bitn-0-vs-int-/2
                               bvecp)))))

(local (in-theory (disable quotient)))

(defthmd quotf-to-x/d
  (implies (not (specialp))
           (equal (quotf)
                  (- (* *2^54*
                        (/ (x) (d)))
                     (* (expt 2 (- 55 (n)))
                        (/ (rmd (n)) (d))))))
  :hints (("Goal" :in-theory (enable quotf-rewrite
                                     quot&quotm1-rewrite
                                     rmd))))

(defthmd quotm1f-to-x/d
  (implies (not (specialp))
           (equal (quotm1f)
                  (- (* *2^54*
                        (/ (x) (d)))
                     (* (expt 2 (- 55 (n)))
                        (1+ (/ (rmd (n)) (d)))))))
  :hints (("Goal" :in-theory (enable quotm1f-rewrite
                                     quot&quotm1-rewrite
                                     rmd))))

(local
 (defthmd aux-2
   (implies (and (integerp (- x y))
                 (rationalp x)
                 (<= -1 y)
                 (< y 1))
            (equal (- x y)
                   (if (<= 0 y)
                       (fl x)
                     (1+ (fl x)))))
   :hints (("Goal" :use ((:instance fl-unique
                                    (n (- x y)))
                         (:instance fl-unique
                                    (n (1- (- x y)))))))))

(local
 (defthm quotf&quotm1f-to-fl-x/d-aux
   (integerp (* (expt 2 (1- (n)))
                (quotient (n))))
   :hints (("Goal"
            :use ((:instance quot&quotm1-rewrite
                             (j (n)))
                  (:instance bits-quot&quotm1-0
                             (j (n)))
                  (:instance bits-plus-bits
                             (x (quot (n)))
                             (m 0)
                             (n 54)
                             (p (- 55 (n)))))))
   :rule-classes :type-prescription))

(local
 (defthmd-nl quotf&quotm1f-to-fl-x/d
   (implies (not (specialp))
            (and (equal (quotf)
                        (if (<= 0 (rmd (n)))
                            (* (expt 2 (- 55 (n)))
                               (fl (* (expt 2 (1- (n)))
                                      (/ (x) (d)))))
                          (* (expt 2 (- 55 (n)))
                             (1+ (fl (* (expt 2 (1- (n)))
                                        (/ (x) (d))))))))
                 (equal (quotm1f)
                        (if (<= 0 (rmd (n)))
                            (* (expt 2 (- 55 (n)))
                               (1- (fl (* (expt 2 (1- (n)))
                                          (/ (x) (d))))))
                          (* (expt 2 (- 55 (n)))
                             (fl (* (expt 2 (1- (n)))
                                    (/ (x) (d)))))))))
   :hints (("Goal"
            :use (quotf&quotm1f-to-fl-x/d-aux
                  (:instance rmd-bounds
                             (j (n)))
                  (:instance quot&quotm1-rewrite
                             (j (n)))
                  (:instance aux-2
                             (x (1- (* (expt 2 (1- (n)))
                                       (/ (x) (d)))))
                             (y (/ (rmd (n)) (d)))))
            :in-theory (e/d (quotf-rewrite
                             quotm1f-rewrite
                             rmd)
                            (rmd-bounds
                             acl2::prefer-positive-addends-<))))))

(local
 (defthmd qtrunc-2-rewrite
   (implies (and (not (specialp))
                 (not (divpow2)))
            (equal (qtrunc-2)
                   (* (expt 2 (- 55 (n)))
                      (fl (* (expt 2 (1- (n)))
                             (/ (x) (d)))))))
   :hints (("Goal"
            :use quotf&quotm1f-to-fl-x/d
            :in-theory (enable divpow2
                               qtrunc-2
                               rsign
                               si-rfinal-rewrite
                               quotf-rewrite
                               quotm1f-rewrite)))))

(local
 (defthmd aux-3
   (implies (and (rationalp x)
                 (<= 1 x)
                 (< x 2))
            (equal (bitn x 0) 1))
   :hints (("Goal" :in-theory (enable bitn-def fl)))))

(local
 (defthm-nl aux-4
   (implies (and (rationalp x)
                 (rationalp d)
                 (<= 1 x)
                 (< x 2)
                 (<= 1 d)
                 (< d 2))
            (and (equal (bitn (* 4398046511104 (fl (* 4096 (/ d) x)))
                              54)
                        (if (< x d) 0 1))
                 (equal (bitn (* 134217728 (fl (* 134217728 (/ d) x)))
                              54)
                        (if (< x d) 0 1))
                 (equal (bitn (fl (* 18014398509481984 (/ d) x))
                              54)
                        (if (< x d) 0 1))))
   :hints (("Goal"
            :use ((:instance fl-unique
                             (x (* (/ d) x))
                             (n 0))
                  (:instance fl-unique
                             (x (* (/ d) x))
                             (n 1)))
            :in-theory (enable bitn-def)))))

(defthm bitn54-qtrunc-2-to-x&d
  (implies (not (specialp))
           (equal (equal (bitn (qtrunc-2) 54) 0)
                  (< (x) (d))))
  :hints (("Goal"
           :use (natp-2^prec-1*x
                 (:instance bitn-shift-up
                            (x (x))
                            (k 54)
                            (n 0)))
           :in-theory (e/d (qtrunc-2
                            quotf&quotm1f-to-fl-x/d
                            x
                            d-1
                            siga-rewrite
                            divpow2
                            f
                            n
                            c
                            rsign
                            si-rfinal-rewrite
                            bitn-bits
                            aux-3)
                           (bits-fl)))))

(local
 (encapsulate
   ()

   (local
    (defthm-nl aux-5
      (implies (and (rationalp x)
                    (rationalp d)
                    (rationalp r)
                    (<= 1 x)
                    (< x 2)
                    (<= 1 d)
                    (< d 2)
                    (<= 0 r)
                    (<= r 1/2))
               (and (equal (fl (* r (/ d) x)) 0)
                    (equal (fl (* (/ d) x r)) 0)))))

   (local
    (defthmd-nl qtrunc-rewrite-gen-2-aux-1
      (implies (and (<= (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
               (equal (qtrunc)
	              (fl (* (expt 2 (+ (prec (f))
                                        (si (expq-1) 13)))
                             (/ (x) (d))))))
      :hints (("Goal"
               :in-theory (e/d (divpow2
                                qtrunc
                                fdivlane-segment-result-expand
                                qtrunc-segment
                                qtrunc-2-rewrite
                                f
                                n
                                c
                                shft
                                mod-to-fl
                                bits-to-mod-fl)
                               (acl2::default-expt-2))))))

   (local
    (defthm aux-6
      (implies (and (integerp x)
                    (< 1 x)
                    (< x *2^12*))
               (< 0 (si (1- x) 13)))
      :hints (("Goal" :in-theory (enable si bvecp)))
      :rule-classes :linear))

   (local
    (defthm-nl aux-7
      (implies (and (rationalp x)
                    (rationalp d)
                    (rationalp r)
                    (<= 0 x)
                    (< 0 d)
                    (< x d)
                    (<= 0 r)
                    (<= r 1))
               (equal (fl (* r (/ d) x)) 0))))

   (local
    (defthmd qtrunc-rewrite-gen-2-aux-2
      (implies (and (< (x) (d))
                    (> (si (expq-1) 13) 1)
                    (not (specialp))
                    (not (divpow2)))
               (equal (qtrunc)
                      (if (equal (fnum) 2)
                          (fl (* (expt 2 (+ 2 (prec (f))))
                                 (/ (x) (d))))
                        (* 2 (fl (* (expt 2 (1+ (prec (f))))
                                    (/ (x) (d))))))))
      :hints (("Goal"
               :use (:instance fl-unique
                               (x (* (/ (d)) (x)))
                               (n 0))
               :in-theory (e/d (divpow2
                                qtrunc
                                fdivlane-segment-result-expand
                                qtrunc-segment
                                qtrunc-2-rewrite
                                f
                                n
                                c
                                mod-to-fl
                                bits-to-mod-fl)
                               (acl2::prefer-positive-addends-<
                                acl2::default-plus-2
                                acl2::default-times-2
                                neg-bitn-1
                                bits-fl))))))

   (local
    (defthmd qtrunc-rewrite-gen-2-aux-3
      (implies (and (or (<= (d) (x))
                        (equal (si (expq-1) 13) 1))
                    (> (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
               (equal (qtrunc)
                      (fl (* (expt 2 (1+ (prec (f))))
                             (/ (x) (d))))))
      :hints (("Goal"
               :in-theory (e/d (divpow2
                                qtrunc
                                fdivlane-segment-result-expand
                                qtrunc-segment
                                qtrunc-2-rewrite
                                f
                                n
                                c
                                bits-fl-diff-alt)
                               (acl2::prefer-positive-addends-<
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::default-times-2
                                neg-bitn-1
                                bits-fl))))))

   (defthmd qtrunc-rewrite-gen-2
     (implies (and (not (specialp))
                   (not (divpow2)))
              (equal (qtrunc)
                     (cond ((<= (si (expq-1) 13) 0)
                            (fl (* (expt 2 (+ (prec (f))
                                              (si (expq-1) 13)))
                                   (/ (x) (d)))))
                           ((and (< (x) (d))
                                 (> (si (expq-1) 13) 1))
                            (if (equal (fnum) 2)
                                (fl (* (expt 2 (+ 2 (prec (f))))
                                       (/ (x) (d))))
                              (* 2 (fl (* (expt 2 (1+ (prec (f))))
                                          (/ (x) (d)))))))
                           (t (fl (* (expt 2 (1+ (prec (f))))
                                     (/ (x) (d))))))))
     :hints (("Goal" :use (qtrunc-rewrite-gen-2-aux-1
                           qtrunc-rewrite-gen-2-aux-2
                           qtrunc-rewrite-gen-2-aux-3))))

   (local
    (defthm aux-8
      (implies (and (not (specialp))
                    (equal (rmd j) (- (d))))
               (equal (* (/ (d)) (rmd j)) -1))))

   (local
    (defthmd stk-segment-rewrite-gen-1
      (implies (and (<= (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk-segment)
	              (if (and (or (equal (rmd (n)) 0)
                                   (equal (rmd (n)) (- (d))))
                               (< -54 (si (expq-1) 13))
                               (equal (bits (* *2^54*
                                               (/ (x) (d)))
                                            (- (si (expq-1) 13))
                                            0)
                                      0))
		          0 1)))
      :hints (("Goal"
               :use (quotf-to-x/d
                     quotm1f-to-x/d
                     (:instance bits-mod
                                (x (if (< (rmd (n)) 0)
                                       (quotm1 (n))
                                     (quot (n))))
                                (i (- (si (expq-1) 13)))))
               :in-theory (e/d (divpow2
                                stk-segment
                                qtrunc-2
                                f
                                n
                                c
                                shft
                                quotf-rewrite
                                quotm1f-rewrite
                                rsign
                                rnonzero
                                rplusdis0-rewrite
                                si-rfinal-rewrite
                                bvecp)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                bits-tail-gen))))))

   (local
    (defthmd stk-rewrite-gen-2-1-aux
      (implies (and (<= (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk)
	              (if (and (equal (stk-segment) 0)
                               (equal (bits (* (expt 2 (+ 53 (si (expq-1) 13)))
                                               (/ (x) (d)))
                                            (- 52 (prec (f)))
                                            0)
                                      0)
                               (equal (bitn (* (expt 2 (+ (prec (f))
                                                          (si (expq-1) 13)))
                                               (/ (x) (d)))
                                            0)
                                      0))
		          0 1)))
      :hints (("Goal"
               :use (quotf-to-x/d
                     quotm1f-to-x/d
                     (:instance bitn-shift-up
                                (x (bits (* (if (< (rmd (n)) 0)
                                                (quotm1 (n))
                                              (quot (n)))
                                            (expt 2 (+ -1 (si (expq-1) 13))))
                                         54 0))
                                (k (- (prec (f)) 53))
                                (n (- 53 (prec (f)))))
                     (:instance bitn-shift-up
                                (x (* (if (< (rmd (n)) 0)
                                          (quotm1 (n))
                                        (quot (n)))
                                      (expt 2 (+ -54
                                                 (prec (f))
                                                 (si (expq-1) 13)))))
                                (k (- 53 (prec (f))))
                                (n 0)))
               :in-theory (e/d (divpow2
                                stk
                                fdivlane-segment-result-expand
                                stk-segment-rewrite-gen-1
                                qtrunc-segment
                                qtrunc
                                qtrunc-2
                                f
                                n
                                c
                                shft
                                quotf-rewrite
                                quotm1f-rewrite
                                rsign
                                si-rfinal-rewrite
                                bitn-bits
                                bvecp)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                bits-tail-gen))))))

   (local
    (defthmd aux-9
      (implies (and (acl2-numberp x)
                    (rationalp y)
                    (not (equal x 0))
                    (not (equal y 0))
                    (< (abs x) y))
               (not (integerp (/ x y))))))

   (local
    (defthmd rmd-to-int-x/d
      (implies (not (specialp))
               (equal (integerp (* (expt 2 (1- (n)))
                                   (/ (x) (d))))
                      (or (equal (rmd (n)) 0)
                          (equal (rmd (n)) (- (d))))))
      :hints (("Goal"
               :use (quotf-to-x/d
                     (:instance aux-9
                                (x (rmd (n)))
                                (y (d)))
                     (:instance bits-quot&quotm1-0
                                (j (n)))
                     (:instance bits-plus-bits
                                (x (quot (n)))
                                (m 0)
                                (n 54)
                                (p (- 55 (n)))))
               :in-theory (enable quotf-rewrite
                                  acl2::prefer-positive-exponents-scatter-exponents-theory)))))

   (defthmd stk-rewrite-gen-2-1
     (implies (and (<= (si (expq-1) 13) 0)
                   (not (specialp))
                   (not (divpow2)))
	      (equal (stk)
	             (if (and (integerp (* (expt 2 (1- (n)))
                                           (/ (x) (d))))
                              (< -54 (si (expq-1) 13))
                              (equal (bits (* *2^54*
                                              (/ (x) (d)))
                                           (- (si (expq-1) 13))
                                           0)
                                     0)
                              (equal (bits (* (expt 2 (+ 53 (si (expq-1) 13)))
                                              (/ (x) (d)))
                                           (- 52 (prec (f)))
                                           0)
                                     0)
                              (equal (bitn (* (expt 2 (+ (prec (f))
                                                         (si (expq-1) 13)))
                                              (/ (x) (d)))
                                           0)
                                     0))
		         0 1)))
     :hints (("Goal" :use (rmd-to-int-x/d
                           stk-rewrite-gen-2-1-aux
                           stk-segment-rewrite-gen-1))))

   (local
    (defthmd stk-segment-rewrite-gen-2
      (implies (and (> (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk-segment)
                      (if (or (equal (rmd (n)) 0)
                              (equal (rmd (n)) (- (d))))
                          0 1)))
      :hints (("Goal" :in-theory (e/d (divpow2
                                       stk-segment
                                       rnonzero
                                       rplusdis0-rewrite
                                       si-rfinal-rewrite)
                                      ())))))

   (local
    (defthm aux-10
      (implies (integerp x)
               (equal (bitn (* 2 x) 0) 0))
      :hints (("Goal" :in-theory (enable bitn-def)))))

   (local
    (defthmd aux-11
      (implies (and (<= 0 x)
                    (< x 1))
               (equal (bitn x 0) 0))
      :hints (("Goal" :in-theory (enable bitn-def fl)))))

   (local
    (defthmd stk-rewrite-gen-2-2-aux-1
      (implies (and (< (rmd (n)) 0)
                    (< (x) (d))
                    (> (si (expq-1) 13) 1)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk)
                      (if (and (equal (stk-segment) 0)
                               (equal (bits (* *2^55*
                                               (/ (x) (d)))
                                            (- 52 (prec (f)))
                                            0)
                                      0)
                               (equal (bitn (* (expt 2 (+ 2 (prec (f))))
                                               (/ (x) (d)))
                                            0)
                                      0))
                          0 1)))
      :hints (("Goal"
               :use (quotm1f-to-x/d
                     (:instance aux-10
                                (x (quotm1 (n))))
                     (:instance bitn-shift-up
                                (x (/ (x) (d)))
                                (k 54)
                                (n 0)))
               :in-theory (e/d (divpow2
                                stk
                                fdivlane-segment-result-expand
                                stk-segment-rewrite-gen-2
                                qtrunc-segment
                                qtrunc
                                qtrunc-2
                                f
                                n
                                c
                                quotm1f-rewrite
                                rsign
                                si-rfinal-rewrite
                                bitn-bits
                                aux-11
                                bvecp)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                aux-10
                                bits-tail-gen))))))

   (local
    (defthmd stk-rewrite-gen-2-2-aux-2
      (implies (and (>= (rmd (n)) 0)
                    (< (x) (d))
                    (> (si (expq-1) 13) 1)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk)
                      (if (and (equal (stk-segment) 0)
                               (equal (bits (* *2^55*
                                               (/ (x) (d)))
                                            (- 52 (prec (f)))
                                            0)
                                      0)
                               (equal (bitn (* (expt 2 (+ 2 (prec (f))))
                                               (/ (x) (d)))
                                            0)
                                      0))
                          0 1)))
      :hints (("Goal"
               :use (quotf-to-x/d
                     (:instance aux-10
                                (x (quot (n))))
                     (:instance bitn-shift-up
                                (x (/ (x) (d)))
                                (k 54)
                                (n 0)))
               :in-theory (e/d (divpow2
                                stk
                                fdivlane-segment-result-expand
                                stk-segment-rewrite-gen-2
                                qtrunc-segment
                                qtrunc
                                qtrunc-2
                                f
                                n
                                c
                                quotf-rewrite
                                rsign
                                si-rfinal-rewrite
                                bitn-bits
                                aux-11
                                bvecp)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                aux-10
                                bits-tail-gen))))))

   (defthmd stk-rewrite-gen-2-2
     (implies (and (< (x) (d))
                   (> (si (expq-1) 13) 1)
                   (not (specialp))
                   (not (divpow2)))
	      (equal (stk)
                     (if (and (integerp (* (expt 2 (1- (n)))
                                           (/ (x) (d))))
                              (equal (bits (* *2^55*
                                              (/ (x) (d)))
                                           (- 52 (prec (f)))
                                           0)
                                     0)
                              (equal (bitn (* (expt 2 (+ 2 (prec (f))))
                                              (/ (x) (d)))
                                           0)
                                     0))
                         0 1)))
     :hints (("Goal" :use (rmd-to-int-x/d
                           stk-rewrite-gen-2-2-aux-1
                           stk-rewrite-gen-2-2-aux-2
                           stk-segment-rewrite-gen-2))))

   (local
    (defthmd stk-rewrite-gen-2-3-aux-1
      (implies (and (< (rmd (n)) 0)
                    (or (<= (d) (x))
                        (equal (si (expq-1) 13) 1))
                    (> (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk)
                      (if (and (equal (stk-segment) 0)
                               (equal (bits (* *2^54*
                                               (/ (x) (d)))
                                            (- 52 (prec (f)))
                                            0)
                                      0)
                               (equal (bitn (* (expt 2 (1+ (prec (f))))
                                               (/ (x) (d)))
                                            0)
                                      0))
                          0 1)))
      :hints (("Goal"
               :use (quotm1f-to-x/d
                     (:instance bitn-shift-up
                                (x (/ (x) (d)))
                                (k 54)
                                (n 0)))
               :in-theory (e/d (divpow2
                                stk
                                fdivlane-segment-result-expand
                                stk-segment-rewrite-gen-2
                                qtrunc-segment
                                qtrunc
                                qtrunc-2
                                f
                                n
                                c
                                quotm1f-rewrite
                                rsign
                                si-rfinal-rewrite
                                bitn-bits
                                aux-3)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                bits-tail-gen))))))

   (local
    (defthmd stk-rewrite-gen-2-3-aux-2
      (implies (and (>= (rmd (n)) 0)
                    (or (<= (d) (x))
                        (equal (si (expq-1) 13) 1))
                    (> (si (expq-1) 13) 0)
                    (not (specialp))
                    (not (divpow2)))
	       (equal (stk)
                      (if (and (equal (stk-segment) 0)
                               (equal (bits (* *2^54*
                                               (/ (x) (d)))
                                            (- 52 (prec (f)))
                                            0)
                                      0)
                               (equal (bitn (* (expt 2 (1+ (prec (f))))
                                               (/ (x) (d)))
                                            0)
                                      0))
                          0 1)))
      :hints (("Goal"
               :use (quotf-to-x/d
                     (:instance bitn-shift-up
                                (x (/ (x) (d)))
                                (k 54)
                                (n 0)))
               :in-theory (e/d (divpow2
                                stk
                                fdivlane-segment-result-expand
                                stk-segment-rewrite-gen-2
                                qtrunc-segment
                                qtrunc
                                qtrunc-2
                                f
                                n
                                c
                                quotf-rewrite
                                rsign
                                si-rfinal-rewrite
                                bitn-bits
                                aux-3)
                               (acl2::not-integerp-4a
                                acl2::not-integerp-4b
                                acl2::not-integerp-4d
                                acl2::not-integerp-3a
                                acl2::not-integerp-3b
                                acl2::mod-x-y-=-x-y
                                acl2::mod-x-y-=-x
                                acl2::mod-zero
                                acl2::simplify-products-gather-exponents-<
                                acl2::mod-negative
                                acl2::meta-integerp-correct
                                mod-does-nothing
                                bvecp-bitn-0
                                bvecp-bitn-1
                                acl2::default-times-2
                                acl2::default-expt-2
                                acl2::default-plus-2
                                acl2::mv-nth-of-cons
                                acl2::logand-with-mask
                                acl2::prefer-positive-addends-equal
                                bits-tail-gen))))))

   (defthmd stk-rewrite-gen-2-3
     (implies (and (or (<= (d) (x))
                       (equal (si (expq-1) 13) 1))
                   (> (si (expq-1) 13) 0)
                   (not (specialp))
                   (not (divpow2)))
	      (equal (stk)
                     (if (and (integerp (* (expt 2 (1- (n)))
                                           (/ (x) (d))))
                              (equal (bits (* *2^54*
                                              (/ (x) (d)))
                                           (- 52 (prec (f)))
                                           0)
                                     0)
                              (equal (bitn (* (expt 2 (1+ (prec (f))))
                                              (/ (x) (d)))
                                           0)
                                     0))
                         0 1)))
     :hints (("Goal" :use (rmd-to-int-x/d
                           stk-rewrite-gen-2-3-aux-1
                           stk-rewrite-gen-2-3-aux-2
                           stk-segment-rewrite-gen-2))))
   ))

(defthmd qtrunc-rewrite-gen
  (implies (not (specialp))
           (equal (qtrunc)
                  (cond ((<= (si (expq-1) 13) 1)
                         (fl (* (expt 2 (+ (prec (f))
                                           (si (expq-1) 13)))
                                (/ (x) (d)))))
                        ((< (x) (d))
                         (if (equal (fnum) 2)
                             (fl (* (expt 2 (+ 2 (prec (f))))
                                    (/ (x) (d))))
                           (* 2 (fl (* (expt 2 (1+ (prec (f))))
                                       (/ (x) (d)))))))
                        (t (fl (* (expt 2 (1+ (prec (f))))
                                  (/ (x) (d))))))))
  :hints (("Goal"
           :use (qtrunc-rewrite-gen-1
                 qtrunc-rewrite-gen-2)
           :in-theory (enable d-1))))

(local
 (defthm stk-rewrite-gen-aux-1
  (implies (and (not (specialp))
                (divpow2))
	   (integerp (* (/ (d)) (x) (expt 2 (+ -1 (n))))))
  :hints (("Goal"
           :use natp-2^prec-1*x
           :in-theory (enable f n c d-1)))
  :rule-classes :type-prescription))

(local
 (defthmd stk-rewrite-gen-aux-2
   (implies (and (or (<= (d) (x))
                     (equal (si (expq-1) 13) 1))
                 (> (si (expq-1) 13) 0)
                 (not (specialp)))
	    (equal (stk)
                   (if (and (integerp (* (expt 2 (1- (n)))
                                         (/ (x) (d))))
                            (equal (bits (* *2^54*
                                            (/ (x) (d)))
                                         (- 52 (prec (f)))
                                         0)
                                   0)
                            (equal (bitn (* (expt 2 (1+ (prec (f))))
                                            (/ (x) (d)))
                                         0)
                                   0))
                       0 1)))
   :hints (("Goal"
            :use (natp-2^prec-1*x
                  stk-rewrite-gen-aux-1
                  stk-rewrite-gen-1-2
                  stk-rewrite-gen-2-3
                  (:instance bitn-shift-up
                             (x (* (expt 2 (1- (prec (f))))
                                   (x)))
                             (k 2)
                             (n -2))
                  (:instance bits-shift-up-2
                             (x (* (expt 2 (1- (prec (f)))) (x)))
                             (i -3)
                             (k (- 55 (prec (f))))))
            :in-theory (enable f d-1)))))

(defthmd stk-rewrite-gen-1
  (implies (and (<= (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
	          (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (< -54 (si (expq-1) 13))
                           (equal (bits (* *2^54*
                                           (/ (x) (d)))
                                        (- (si (expq-1) 13))
                                        0)
                                  0)
                           (equal (bits (* (expt 2 (+ 53 (si (expq-1) 13)))
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (+ (prec (f))
                                                      (si (expq-1) 13)))
                                           (/ (x) (d)))
                                        0)
                                  0))
		      0 1)))
  :hints (("Goal" :use (stk-rewrite-gen-1-1
                        stk-rewrite-gen-2-1
                        stk-rewrite-gen-aux-2))))

(defthmd stk-rewrite-gen-2
  (implies (and (< (x) (d))
                (> (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
                  (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (equal (bits (* *2^55*
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (+ 2 (prec (f))))
                                           (/ (x) (d)))
                                        0)
                                  0))
                      0 1)))
  :hints (("Goal"
           :use (stk-rewrite-gen-1-2
                 stk-rewrite-gen-2-2)
           :in-theory (enable d-1))))

(defthmd stk-rewrite-gen-3
  (implies (and (<= (d) (x))
                (>= (si (expq-1) 13) 1)
                (not (specialp)))
	   (equal (stk)
                  (if (and (integerp (* (expt 2 (1- (n)))
                                        (/ (x) (d))))
                           (equal (bits (* *2^54*
                                           (/ (x) (d)))
                                        (- 52 (prec (f)))
                                        0)
                                  0)
                           (equal (bitn (* (expt 2 (1+ (prec (f))))
                                           (/ (x) (d)))
                                        0)
                                  0))
                      0 1)))
  :hints (("Goal" :use stk-rewrite-gen-aux-2)))

