;; Cuong Chau <cuong.chau@arm.com>

;; May 2021

(in-package "RTL")

(include-book "round")

(local (arith-5-for-rtl))

;; ======================================================================

(local
 (defundd rz ()
   (if (and (equal (fzp) 1)
            (not (equal (f) (hp)))
            (or (denormp (opaw) (f))
                (denormp (opbw) (f))))
       (set-flag (idc) (rin))
     (rin))))

(local
 (encapsulate
   ()

   (local
    (defthm zerp-zencode
      (zerp (zencode sgn (f))
            (f))
      :hints (("Goal"
               :in-theory (enable zerp zencode f encodingp expf manf)))))

   (local
    (defthm decode-opz-rewrite
      (implies (not (specialp))
               (and (equal (decode (opaz) (f)) (a))
	            (equal (decode (opbz) (f)) (b))))
      :hints (("Goal" :in-theory (enable specialp
                                         opaz
                                         opbz
                                         a
                                         b
                                         a-class
                                         b-class)))))

   (local
    (defthm arm-binary-spec-to-arm-binary-comp
      (implies (not (specialp))
               (equal (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
                      (arm-binary-comp 'div (opaz) (opbz) (rz) (f))))
      :hints (("Goal" :in-theory (enable specialp
                                         opaz
                                         opbz
                                         rz
                                         fzp
                                         a-class
                                         b-class
                                         binary-undefined-p)))))

   (defthmd arm-binary-spec-to-arm-post-comp
     (implies (not (specialp))
              (equal (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
                     (arm-post-comp (/ (a) (b)) (rz) (f))))
     :hints (("Goal"
              :in-theory (e/d (specialp
                               a-class
                               b-class
                               binary-eval)
                              (arm-binary-spec
                               arm-post-comp)))))
   ))

(local
 (defthmd data-non-special
   (implies (not (specialp))
            (equal (data)
                   (mv-nth 0 (final (qrnd)
                                    (inx)
                                    (sign)
                                    (expq)
                                    (rmode)
                                    (fzp)
                                    (fnum)
                                    (flags-b)))))
   :hints (("Goal" :in-theory (enable specialp data result)))))

(local
 (defthmd flags-non-special
   (implies (not (specialp))
            (equal (flags)
                   (mv-nth 1 (final (qrnd)
                                    (inx)
                                    (sign)
                                    (expq)
                                    (rmode)
                                    (fzp)
                                    (fnum)
                                    (flags-b)))))
   :hints (("Goal" :in-theory (enable specialp flags result)))))

(defthmd signa-a-rel
  (implies (not (specialp))
           (equal (signa)
                  (if (< (a) 0) 1 0)))
  :hints (("Goal"
           :use nonzero-a
           :in-theory (enable spec-fields a decode ndecode ddecode))))

(defthmd signb-b-rel
  (implies (not (specialp))
           (equal (signb)
                  (if (< (b) 0) 1 0)))
  :hints (("Goal"
           :use nonzero-b
           :in-theory (enable spec-fields b decode ndecode ddecode))))

(defthmd sign-a/b-rel
  (implies (not (specialp))
           (equal (sign)
                  (if (< (/ (a) (b)) 0)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable sign signa-a-rel signb-b-rel))))

;; Overflow

(local
 (defthm fpscr-rc-to-rmode
   (equal (fpscr-rc (rin))
          (mode (rmode)))
   :hints (("Goal" :in-theory (enable fpscr-rc mode rmode)))))

(local
 (defthm bitn-set-flag-non-ovl
   (implies (and (natp m)
                 (integerp n)
                 (integerp flags))
            (equal (bitn (set-flag m flags) n)
                   (if (equal m n)
                       1
                     (bitn flags n))))
   :hints (("Goal"
            :cases ((< m n))
            :use (:instance bitn-shift-up
                            (x 1)
                            (k m)
                            (n (- n m)))
            :in-theory (enable set-flag bitn-logior bvecp)))))

(local
 (defthm fpscr-rc-set-flag-non-ovl
   (implies (and (natp b)
                 (not (member b '(22 23)))
                 (integerp flags))
            (equal (fpscr-rc (set-flag b flags))
                   (fpscr-rc flags)))
   :hints (("Goal"
            :cases ((< b 22))
            :use (:instance bits-plus-bits
                            (x 1)
                            (m 0)
                            (n (- 23 b))
                            (p (- 22 b)))
            :in-theory (enable fpscr-rc set-flag bits-logior bits)))))

(local
 (defthmd si13-expq-not-ovf
   (implies (and (<= 1 (si (expq) 13))
                 (not (specialp)))
            (equal (<= (rnd (abs (/ (a) (b)))
                            (rmode-prime (mode (rmode)) (sign))
                            (prec (f)))
                       (lpn (f)))
                   (<= (si (expq) 13)
                       (- (expt 2 (expw (f))) 2))))
   :hints (("Goal"
            :use (expo-rnd-abs-a/b
                  (:instance expo-monotone
                             (x (rnd (abs (/ (a) (b)))
                                     (rmode-prime (mode (rmode)) (sign))
                                     (prec (f))))
                             (y (lpn (f))))
                  (:instance expo-monotone
                             (x (lpn (f)))
                             (y (rnd (abs (/ (a) (b)))
                                     (rmode-prime (mode (rmode)) (sign))
                                     (prec (f)))))
                  (:instance exactp2
                             (x (rnd (abs (/ (a) (b)))
                                     (rmode-prime (mode (rmode)) (sign))
                                     (prec (f))))
                             (n (prec (f))))
                  (:instance expo-upper-bound
                             (x (rnd (abs (/ (a) (b)))
                                     (rmode-prime (mode (rmode)) (sign))
                                     (prec (f)))))
                  (:instance int+1<=
                             (x (* (rnd (abs (/ (a) (b)))
                                        (rmode-prime (mode (rmode)) (sign))
                                        (prec (f)))
                                   (expt 2 (- (1- (prec (f)))
                                              (expo
                                               (rnd (abs (/ (a) (b)))
                                                    (rmode-prime
                                                     (mode (rmode)) (sign))
                                                    (prec (f))))))))
                             (y (expt 2 (prec (f))))))
            :in-theory (enable f lpn)))))

(local
 (defthmd data-when-ovf
   (implies (and (not (specialp))
                 (< (lpn (f))
                    (rnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (prec (f)))))
	    (equal (data)
	           (mv-nth 0 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-not-ovf
                  rnd-abs-a/b-denormal-upper-bound)
            :in-theory (e/d (data-non-special
                             rz
                             f
                             final
                             rnd-minus
                             mode
                             sgn
                             lpn
                             nencode
                             sign-a/b-rel)
                            (acl2::default-expt-2))))))

(local
 (defthm logior-to-set-flag
   (and (equal (logior 8 (rin))
               (set-flag 3 (rin)))
        (equal (logior 16 (rin))
               (set-flag 4 (rin)))
        (equal (logior 20 (rin))
               (set-flag 2 (set-flag 4 (rin))))
        (equal (logior 24 (rin))
               (set-flag 4 (set-flag 3 (rin))))
        (equal (logior 128 (rin))
               (set-flag 7 (rin)))
        (equal (logior 136 (rin))
               (set-flag 3 (set-flag 7 (rin))))
        (equal (logior 144 (rin))
               (set-flag 4 (set-flag 7 (rin))))
        (equal (logior 148 (rin))
               (set-flag 2 (set-flag 4 (set-flag 7 (rin))))))
   :hints (("Goal" :in-theory (enable set-flag)))))

(local
 (defthmd flags-when-ovf
   (implies (and (not (specialp))
                 (< (lpn (f))
                    (rnd (abs (/ (a) (b)))
                         (rmode-prime (mode (rmode)) (sign))
                         (prec (f)))))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-not-ovf
                  rnd-abs-a/b-denormal-upper-bound)
            :in-theory (e/d (flags-non-special
                             rz
                             fzp
                             f
                             final
                             rnd-minus
                             mode
                             lpn
                             flags-b-rewrite
                             sign-a/b-rel)
                            (acl2::default-expt-2
                             acl2::default-logior-2))))))

;; Flush-to-zero

(local
 (defthmd fdivlane-correct-when-fz
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (< (abs (/ (a) (b))) (spn (f)))
		 (equal (fzp) 1))
	    (mv-let (data-spec r-spec) (arm-post-comp (/ (a) (b)) (rz) (f))
	      (and (equal (data) data-spec)
                   (equal (logior (rin) (flags)) r-spec))))
   :hints (("Goal"
            :use si13-expq-denormal
            :in-theory (enable data-non-special
                               flags-non-special
                               rz
                               fzp
                               f
                               final
                               rnd-minus
                               rmode-prime
                               flip-mode
                               flags-b-rewrite
                               bitn-logior
                               sign-a/b-rel)))))

;; Denormal round to zero

(local
 (defthmd data-when-drnd-=-0
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (< (abs (/ (a) (b))) (spn (f)))
		 (equal (fzp) 0)
		 (equal (drnd (/ (a) (b))
                              (mode (rmode))
                              (f))
                        0))
	    (equal (data)
	           (mv-nth 0 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  drnd-abs-a/b-to-qrnd)
            :in-theory (enable data-non-special
                               rz
                               f
                               final
                               rnd-minus
                               drnd-minus
                               rmode-prime
                               flip-mode
                               sign-a/b-rel)))))

(local
 (defthmd flags-when-drnd-=-0
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (< (abs (/ (a) (b))) (spn (f)))
		 (equal (fzp) 0)
		 (equal (drnd (/ (a) (b))
                              (mode (rmode))
                              (f))
                        0))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  inx-exact-a/b-denormal-rel)
            :in-theory (enable flags-non-special
                               rz
                               fzp
                               final
                               rnd-minus
                               drnd-minus
                               rmode-prime
                               flip-mode
                               flags-b-rewrite
                               sign-a/b-rel)))))

;; Denormal round to SPN

(local
 (defthmd data-when-abs-drnd-=-spn
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (< (abs (/ (a) (b))) (spn (f)))
		 (equal (fzp) 0)
		 (equal (abs (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f)))
                        (spn (f))))
	    (equal (data)
	           (mv-nth 0 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  drnd-abs-a/b-to-qrnd)
            :in-theory (e/d (data-non-special
                             rz
                             fzp
                             f
                             final
                             rnd-minus
                             drnd-minus
                             rmode-prime
                             flip-mode
                             spn
                             nencode
                             sign-a/b-rel)
                            (acl2::|(<= x (/ y)) with (< y 0)|
                             acl2::|(< (/ x) y) with (< x 0)|
                             acl2::not-integerp-1b
                             acl2::not-integerp-2b
                             acl2::not-integerp-3b
                             acl2::not-integerp-4b))))))

(local
 (defthmd flags-when-abs-drnd-=-spn
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (< (abs (/ (a) (b))) (spn (f)))
		 (equal (fzp) 0)
		 (equal (abs (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f)))
                        (spn (f))))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  inx-exact-a/b-denormal-rel)
            :in-theory (enable flags-non-special
                               rz
                               fzp
                               final
                               rnd-minus
                               drnd-minus
                               rmode-prime
                               flip-mode
                               flags-b-rewrite
                               sign-a/b-rel)))))

;; Denormal case

(local
 (defthm sgnf-data
   (implies (not (specialp))
            (equal (sgnf (data) (f))
                   (sign)))
   :hints (("Goal" :in-theory (enable sgnf data-non-special f final bvecp)))))

(local
 (defthm common-mode-p-rmode
   (common-mode-p (mode (rmode)))
   :hints (("Goal" :in-theory (enable mode)))))

(local
 (defthmd drnd-<=-spn
   (implies (<= (abs (/ (a) (b))) (spn (f)))
            (<= (abs (drnd (/ (a) (b))
                           (mode (rmode))
                           (f)))
                (spn (f))))
   :hints (("Goal"
            :use ((:instance rnd-monotone
                             (x (+ (/ (a) (b))
                                   (* (sgn (/ (a) (b)))
                                      (spn (f)))))
                             (y (+ (spn (f))
                                   (* (sgn (/ (a) (b)))
                                      (spn (f)))))
                             (mode (mode (rmode)))
                             (n (prec (f))))
                  (:instance rnd-monotone
                             (x (+ (- (spn (f)))
                                   (* (sgn (/ (a) (b)))
                                      (spn (f)))))
                             (y (+ (/ (a) (b))
                                   (* (sgn (/ (a) (b)))
                                      (spn (f)))))
                             (mode (mode (rmode)))
                             (n (prec (f)))))
            :in-theory (enable drnd-rewrite spn f mode sgn)))
   :rule-classes :linear))

(local
 (defthm expf-data-denormal
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
            (and (equal (expf (data) (f))
                        0)
                 (equal (bits (qrnd) (+ -1 (prec (f))) 0)
                        (bits (qrnd) (+ -2 (prec (f))) 0))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  drnd-<=-spn
                  drnd-abs-a/b-to-qrnd
                  (:instance bitn-plus-bits
                             (x (qrnd))
                             (m 0)
                             (n (1- (prec (f))))))
            :in-theory (e/d (expf
                             data-non-special
                             f
                             final
                             drnd-minus
                             rmode-prime
                             flip-mode
                             spn
                             sign-a/b-rel)
                            (acl2::default-expt-2
                             acl2::|(<= x (/ y)) with (< y 0)|
                             acl2::|(< (/ x) y) with (< x 0)|
                             acl2::not-integerp-1b
                             acl2::not-integerp-2b
                             acl2::not-integerp-3b
                             acl2::not-integerp-4b))))))

(local
 (defthm manf-data-denormal
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0))
            (equal (manf (data) (f))
                   (bits (qrnd) (- (prec (f)) 2) 0)))
   :hints (("Goal"
            :use si13-expq-denormal
            :in-theory (enable manf
                               data-non-special
                               f
                               final
                               sign-a/b-rel)))))

(defthm not-explicitp-f
  (not (explicitp (f)))
  :hints (("Goal" :in-theory (enable f))))

(local
 (defthmd drnd-to-ddecode-data
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0)
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
            (equal (drnd (/ (a) (b))
                         (mode (rmode))
                         (f))
                   (ddecode (data) (f))))
   :hints (("Goal"
            :use drnd-abs-a/b-to-qrnd
            :in-theory (enable ddecode
                               drnd-minus
                               rmode-prime
                               flip-mode
                               sign-a/b-rel)))))

(defthmd si-expq-non-neg
  (implies (<= 0 (si (expq) 13))
           (equal (si (expq) 13) (expq)))
  :hints (("Goal" :in-theory (enable si))))

(local
 (defthm encodingp-data
   (implies (not (specialp))
            (encodingp (data) (f)))
   :hints (("Goal"
            :cases ((equal (sign) 0))
            :use ((:instance bits-shift-up-1
                             (x (+ (expt 2 (expw (f)))
                                   (expq)))
                             (i 63)
                             (j (1- (prec (f))))
                             (k (1- (prec (f)))))
                  (:instance bits-shift-up-1
                             (x (+ (expt 2 (expw (f)))
                                   (bitn (qrnd) (1- (prec (f))))))
                             (i 63)
                             (j (1- (prec (f))))
                             (k (1- (prec (f)))))
                  (:instance bits-shift-up-1
                             (x (expq))
                             (i 63)
                             (j (1- (prec (f))))
                             (k (1- (prec (f)))))
                  (:instance bits-shift-up-1
                             (x (bitn (qrnd) (1- (prec (f)))))
                             (i 63)
                             (j (1- (prec (f))))
                             (k (1- (prec (f))))))
            :in-theory (enable encodingp
                               data-non-special
                               f
                               final
                               si-expq-non-neg
                               cat
                               bvecp)))))

(local
 (defthm denormp-data
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0)
                 (not (equal (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f))
                             0))
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
            (denormp (data) (f)))
   :hints (("Goal"
            :use drnd-abs-a/b-to-qrnd
            :in-theory (enable denormp
                               drnd-minus
                               rmode-prime
                               flip-mode
                               sign-a/b-rel)))))

(local
 (defthmd data-to-dencode-drnd
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0)
                 (not (equal (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f))
                             0))
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
            (equal (data)
                   (dencode (drnd (/ (a) (b))
                                  (mode (rmode))
                                  (f))
                            (f))))
   :hints (("Goal" :use drnd-to-ddecode-data))))

(local
 (defthmd data-when-denormal
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0)
                 (not (equal (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f))
                             0))
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
	    (equal (data)
	           (mv-nth 0 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  rnd-abs-a/b-denormal-upper-bound)
            :in-theory (enable data-to-dencode-drnd
                               rz
                               fzp
                               f
                               rnd-minus
                               rmode-prime
                               flip-mode
                               lpn
                               sign-a/b-rel)))))

(local
 (defthmd flags-when-denormal
   (implies (and (not (specialp))
		 (< (abs (/ (a) (b))) (spn (f)))
                 (equal (fzp) 0)
                 (not (equal (drnd (/ (a) (b))
                                   (mode (rmode))
                                   (f))
                             0))
                 (not (equal (abs (drnd (/ (a) (b))
                                        (mode (rmode))
                                        (f)))
                             (spn (f)))))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  rnd-abs-a/b-denormal-upper-bound
                  inx-exact-a/b-denormal-rel)
            :in-theory (enable flags-non-special
                               rz
                               fzp
                               f
                               final
                               rnd-minus
                               drnd-minus
                               rmode-prime
                               flip-mode
                               flags-b-rewrite
                               lpn
                               sign-a/b-rel)))))

;; Normal case

(local
 (defthm expf-data-normal
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
            (equal (expf (data) (f))
                   (si (expq) 13)))
   :hints (("Goal"
            :use (si13-expq-denormal
                  si13-expq-not-ovf)
            :in-theory (enable expf
                               data-non-special
                               f
                               final
                               si-expq-non-neg
                               bvecp)))))

(local
 (defthm manf-data-normal
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
            (equal (manf (data) (f))
                   (bits (qrnd) (- (prec (f)) 2) 0)))
   :hints (("Goal"
            :use (si13-expq-denormal
                  si13-expq-not-ovf)
            :in-theory (enable manf
                               data-non-special
                               f
                               final
                               expo-lpn)))))

(local
 (defthmd rnd-to-ndecode-data
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
            (equal (rnd (/ (a) (b))
                        (mode (rmode))
                        (prec (f)))
                   (ndecode (data) (f))))
   :hints (("Goal"
            :use (rnd-abs-a/b-to-qrnd
                  si13-expq-denormal)
            :in-theory (enable ndecode
                               rnd-minus
                               rmode-prime
                               flip-mode
                               sign-a/b-rel)))))

(local
 (defthm normp-data
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
            (normp (data) (f)))
   :hints (("Goal"
            :use (si13-expq-denormal
                  si13-expq-not-ovf)
            :in-theory (enable normp)))))

(local
 (defthmd data-to-nencode-rnd
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
            (equal (data)
                   (nencode (rnd (/ (a) (b))
                                 (mode (rmode))
                                 (prec (f)))
                            (f))))
   :hints (("Goal" :use rnd-to-ndecode-data))))

(local
 (defthmd data-when-normal
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
	    (equal (data)
	           (mv-nth 0 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :in-theory (enable data-to-nencode-rnd
                               rz
                               f
                               rnd-minus
                               rmode-prime
                               flip-mode
                               sign-a/b-rel)))))

(local
 (defthmd flags-when-normal
   (implies (and (not (specialp))
                 (<= (rnd (abs (/ (a) (b)))
                          (rmode-prime (mode (rmode)) (sign))
                          (prec (f)))
                     (lpn (f)))
		 (<= (spn (f)) (abs (/ (a) (b)))))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-post-comp (/ (a) (b)) (rz) (f)))))
   :hints (("Goal"
            :use (si13-expq-denormal
                  si13-expq-not-ovf
                  inx-exact-a/b-rel)
            :in-theory (e/d (flags-non-special
                             rz
                             f
                             final
                             rnd-minus
                             rmode-prime
                             flip-mode
                             flags-b-rewrite
                             sign-a/b-rel)
                            (acl2::default-logior-2
                             acl2::not-integerp-1b
                             acl2::not-integerp-2b
                             acl2::not-integerp-3b
                             acl2::not-integerp-4b))))))

;; Combine all cases

(local
 (defthmd data-non-special-correct
   (implies (not (specialp))
	    (equal (data)
	           (mv-nth 0 (arm-binary-spec 'div (opaw) (opbw) (rin) (f)))))
   :hints (("Goal"
            :use (data-when-ovf
                  fdivlane-correct-when-fz
                  data-when-drnd-=-0
                  data-when-abs-drnd-=-spn
                  data-when-denormal
                  data-when-normal)
            :in-theory (e/d (arm-binary-spec-to-arm-post-comp)
                            (arm-binary-spec arm-post-comp abs))))))

(local
 (defthmd flags-non-special-correct
   (implies (not (specialp))
	    (equal (logior (rin) (flags))
	           (mv-nth 1 (arm-binary-spec 'div (opaw) (opbw) (rin) (f)))))
   :hints (("Goal"
            :use (flags-when-ovf
                  fdivlane-correct-when-fz
                  flags-when-drnd-=-0
                  flags-when-abs-drnd-=-spn
                  flags-when-denormal
                  flags-when-normal)
            :in-theory (e/d (arm-binary-spec-to-arm-post-comp)
                            (arm-binary-spec arm-post-comp abs))))))

(defthmd fdivlane-main
  (mv-let
    (data-spec r-spec)
    (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
    (and (equal (data) data-spec)
         (equal (logior (rin) (flags)) r-spec)))
  :hints (("Goal"
           :use (fdivlane-special-correct
                 data-non-special-correct
                 flags-non-special-correct)
           :in-theory (disable arm-binary-spec))))

(local
 (defthmd fdivlane-main-inst
   (let* ((f (case (fnum) (1 (hp)) (2 (sp)) (3 (dp))))
          (fmtw (+ 1 (expw f) (sigw f)))
          (fzp (bitn (rin) 24))
          (dnp (bitn (rin) 25))
          (rmode (bits (rin) 23 22)))
     (mv-let (data flags) (fdivlane (opa) (opb) (fnum) (vec) fzp dnp rmode)
       (mv-let
         (data-spec r-spec)
         (arm-binary-spec 'div
                          (bits (opa) (1- fmtw) 0)
                          (bits (opb) (1- fmtw) 0)
                          (rin)
                          f)
         (and (equal data data-spec)
              (equal (logior (rin) flags) r-spec)))))
   :hints (("Goal"
            :use fdivlane-main
            :in-theory (e/d (fdivlane-lemma
                             data flags
                             opaw opbw fmtw
                             f
                             fzp dnp rmode)
                            (arm-binary-spec))))))

(defthmd fdivlane-correct
  (implies (input-constraints opa opb fnum vec rin)
           (let* ((f (case fnum (1 (hp)) (2 (sp)) (3 (dp))))
                  (fmtw (+ 1 (expw f) (sigw f)))
                  (fzp (bitn rin 24))
                  (dnp (bitn rin 25))
                  (rmode (bits rin 23 22)))
             (mv-let (data flags) (fdivlane opa opb fnum vec fzp dnp rmode)
               (mv-let
                 (data-spec r-spec)
                 (arm-binary-spec 'div
                                  (bits opa (1- fmtw) 0)
                                  (bits opb (1- fmtw) 0)
                                  rin
                                  f)
                 (and (equal data data-spec)
                      (equal (logior rin flags) r-spec))))))
  :hints (("Goal"
           :use (:functional-instance
                 fdivlane-main-inst
                 (opa (lambda ()
                        (if (input-constraints opa opb fnum vec rin)
                            opa
                          (opa))))
                 (opb (lambda ()
                        (if (input-constraints opa opb fnum vec rin)
                            opb
                          (opb))))
                 (fnum (lambda ()
                         (if (input-constraints opa opb fnum vec rin)
                             fnum
                           (fnum))))
                 (vec (lambda ()
                        (if (input-constraints opa opb fnum vec rin)
                            vec
                          (vec))))
                 (rin (lambda ()
                        (if (input-constraints opa opb fnum vec rin)
                            rin
                          (rin)))))
	   :in-theory (disable arm-binary-spec))))
