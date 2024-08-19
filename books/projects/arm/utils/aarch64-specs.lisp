;; Cuong Chau <ckc8687@gmail.com>

;; July 2022

;; Extend Arm floating-point specs to AArch64 that includes two new control
;; bits FIZ and AH

(in-package "RTL")

(include-book "rtl-utils")

(local (arith-5-for-rtl))

;; ======================================================================

;; (defsection-rtl |ARM AArch64 Floating-Point Instructions|
;;   |Floating-Point Exceptions and Specification of Elementary Arithmetic Instructions|

;; Extend ARM-BINARY-SPEC to AArch64

;; FPCR bits:

(defconst *fiz*   0)
(defconst *ah*    1)
(defconst *fz16* 19)
(defconst *fz*   24)
(defconst *dn*   25)
(defconst *ahp*  26)

;; FPSR bits:

(defconst *ioc* 0)
(defconst *dzc* 1)
(defconst *ofc* 2)
(defconst *ufc* 3)
(defconst *ixc* 4)
(defconst *idc* 7)

;; An operand is forced to 0:

(defun fzerp (x fz fiz ah fmt)
  (and (denormp x fmt)
       (or (and (= fz 1)
                (or (= ah 0) (equal fmt (hp))))
           (and (= fiz 1)
                (not (equal fmt (hp)))))))

(defun signed-indef (ah f)
  (declare (xargs :guard (and (bitp ah)
                              (formatp f))))
  (if (= ah 1)
      (logior (indef f)
              (expt 2 (+ (expw f) (sigw f))))
    (indef f)))

(defun aarch64-process-nan (x fpcr f)
  (declare (xargs :guard (and (encodingp x f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (= (bitn fpcr *dn*) 1)
      (signed-indef (bitn fpcr *ah*) f)
    (qnanize x f)))

(defun aarch64-binary-pre-comp-val (op a b fpcr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (or (snanp a f)
          (and (= (bitn fpcr *ah*) 1)
               (qnanp a f)))
      (aarch64-process-nan a fpcr f)
    (if (snanp b f)
        (aarch64-process-nan b fpcr f)
      (if (qnanp a f)
          (aarch64-process-nan a fpcr f)
        (if (qnanp b f)
            (aarch64-process-nan b fpcr f)
          (if (binary-undefined-p op a f b f)
              (signed-indef (bitn fpcr *ah*) f)
            ()))))))

(defun aarch64-binary-pre-comp (op a b fpcr fpsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zencode
                                                           set-flag
                                                           sgnf)))))
  (mv-let
    (a b fpsr)
    (if (or (and (not (equal f (hp)))
                 (= (bitn fpcr *fz*) 1)
                 (= (bitn fpcr *ah*) 0))
            (and (equal f (hp))
                 (= (bitn fpcr *fz16*) 1))
            (and (not (equal f (hp)))
                 (= (bitn fpcr *fiz*) 1)))
        (mv (if (denormp a f)
                (zencode (sgnf a f) f)
              a)
            (if (denormp b f)
                (zencode (sgnf b f) f)
              b)
            (if (and (or (denormp a f) (denormp b f))
                     (not (equal f (hp)))
                     (= (bitn fpcr *fz*) 1)
                     (= (bitn fpcr *ah*) 0))
                (set-flag *idc* fpsr)
              fpsr))
      (mv a b
          (if (and (or (denormp a f) (denormp b f))
                   (not (equal f (hp)))
                   (= (bitn fpcr *fiz*) 0)
                   (= (bitn fpcr *ah*) 1)
                   (not (nanp a f))
                   (not (nanp b f))
                   (or (not (eql op 'div)) (not (zerp b f))))
              (set-flag *idc* fpsr)
            fpsr)))
    (mv a b
        (aarch64-binary-pre-comp-val op a b fpcr f)
        (arm-binary-pre-comp-excp op a b fpsr f))))

(defthm common-mode-p-of-fpscr-rc
  (common-mode-p (fpscr-rc x))
  :hints (("Goal" :in-theory (enable fpscr-rc))))

(defthm exactp-lpn
  (implies (and (formatp f)
                (equal n (prec f)))
           (exactp (lpn f) n))
  :hints (("Goal" :in-theory (e/d (exactp2) ()))
          (and stable-under-simplificationp
               '(:in-theory (e/d (lpn) ())))))

(defthm exactp-spn
  (implies (and (formatp f)
                (posp n))
           (exactp (spn f) n))
  :hints (("Goal" :in-theory (e/d (exactp2 spn) ()))))

(defthmd expo-spd
  (implies (formatp f)
           (equal (expo (spd f))
                  (+ 2 (- (bias f)) (- (prec f)))))
  :hints (("Goal" :in-theory (e/d (spd) ()))))

(defthm exactp-spd
  (implies (and (formatp f)
                (posp n))
           (and (exactp (spd f) n)
                (exactp (- (spd f)) n)))
  :hints (("Goal" :in-theory (e/d (spd exactp2) ()))))

(defthmd drnd-tiny-rw
  (implies (and (formatp f)
                (rationalp x)
                (common-mode-p mode)
                (< x (spd f))
                (< 0 x))
           (equal (drnd x mode f)
                  (if (or (and (< x (* 1/2 (spd f)))
                               (member mode '(raz rup)))
                          (and (= x (* 1/2 (spd f)))
                               (member mode '(raz rup rna)))
                          (and (> x (* 1/2 (spd f)))
                               (not (member mode '(rtz rdn)))))
                      (spd f)
                    0)))
  :hints (("Goal" :in-theory (e/d (expo-spd) ())
                  :use (drnd-tiny-a
                        drnd-tiny-b
                        drnd-tiny-c))))

(defthm exactp-0
  (exactp 0 n)
  :hints (("Goal" :in-theory (e/d (exactp) ()))))

(local-defthmd exactp-drnd-when-<-spd
  (implies (and (rationalp x)
                (formatp f)
                (< (abs x) (spd f))
                (posp n))
           (exactp (drnd x mode f) n))
  :hints (("Goal" :cases ((or (not (common-mode-p mode))
                              (= x 0))))
          ("Subgoal 2"
           :in-theory (e/d (drnd-minus flip-mode) (exactp-spd))
           :use ((:instance drnd-tiny-rw
                  (x (abs x))
                  (mode (if (> x 0) mode (flip-mode mode))))
                 (:instance expo-minus
                  (x (drnd x mode f)))
                 exactp-spd))
          ("Subgoal 1"
           :in-theory (e/d (drnd rnd
                            common-mode-p ieee-rounding-mode-p) ()))))

(defthm exactp-drnd
  (implies (and (formatp f)
                (rationalp u)
                (< (abs u) (spn f))
                (equal n (prec f)))
           (exactp (drnd u mode f) n))
  :hints (("Goal" :in-theory (e/d (drnd) (rnd-exactp-a))
                  :cases ((or (= u 0)
                              (<= (+ -1 (bias f) (expo u) (prec f)) 0))))
          ("Subgoal 2"
           :use ((:instance rnd-exactp-a
                  (x u)
                  (n (+ -1 (bias f) (expo u) (prec f))))
                 (:instance exactp-<=
                  (m (+ -1 (bias f) (expo u) (prec f)))
                  (n (prec f))
                  (x (drnd u mode f)))
                 (:instance expo-monotone
                  (x u) (y (spn f)))))
          ("Subgoal 1" :cases ((= u 0)))
          ("Subgoal 1.2"
           :in-theory (e/d (expo-spd) ())
           :use ((:instance exactp-drnd-when-<-spd
                  (x u))
                 (:instance expo-monotone
                  (x (spd f)) (y u))))))

(defun aarch64-post-comp-base (u fpcr fpsr f satovfl)
  (declare (xargs :guard (and (real/rationalp u)
                              (not (= u 0))
                              (natp fpcr)
                              (natp fpsr)
                              (formatp f)
                              (bitp satovfl))
                  :guard-hints (("Goal"
                                 :use ((:instance rnd-monotone
                                        (x (lpn f))
                                        (y u)
                                        (mode (fpscr-rc fpcr))
                                        (n (prec f)))
                                       (:instance rnd-monotone
                                        (x u)
                                        (y (- (lpn f)))
                                        (mode (fpscr-rc fpcr))
                                        (n (prec f)))
                                       (:instance drnd-exactp-a
                                        (x u)
                                        (mode (fpscr-rc fpcr)))
                                       (:instance rnd-drnd-up
                                        (x u)
                                        (mode (fpscr-rc fpcr))))
                                 :in-theory (e/d (sgn set-flag
                                                  rnd-minus
                                                  nrepp)
                                                 (rationalp-abs
                                                  acl2::|(< x (if a b c))|
                                                  nrepp-minus))))))
  (let* ((rmode (fpscr-rc fpcr))
         (r (rnd u rmode (prec f)))
         (d (drnd u rmode f))
         (sgn (if (< u 0) 1 0)))
    (if (and (not (and (equal f (hp))
                       (= (bitn fpcr *ahp*) 1)))
             (> (abs r) (lpn f)))
        (let ((fpsr (set-flag *ofc* (set-flag *ixc* fpsr))))
          (if (or (and (eql rmode 'rdn) (> r 0))
                  (and (eql rmode 'rup) (< r 0))
                  (eql rmode 'rtz)
                  (and (= satovfl 1) (eql rmode 'rne)))
              (mv (nencode (* (sgn r) (lpn f)) f)
                  fpsr)
            (mv (iencode sgn f) fpsr)))
      (if (and (equal f (hp))
               (= (bitn fpcr *ahp*) 1)
               (>= (abs r) (expt 2 17)))
          ;; Alternate HP mode
          (mv (cat sgn 1 #x7FFF 15) (set-flag *ioc* fpsr))
        (if (< (abs u) (spn f))
            ;; When AH = 1, detection of underflow occurs AFTER rounding with an
            ;; UNBOUNDED exponent.
            (if (and (= (bitn fpcr *ah*) 1)
                     (= (abs r) (spn f)))
                (mv (nencode d f) ;; should be the same as (nencode r f)
                    (set-flag *ixc* fpsr))
              (if (or (and (equal f (hp))
                           (= (bitn fpcr *fz16*) 1))
                      (and (not (equal f (hp)))
                           (= (bitn fpcr *fz*) 1)))
                  (mv (zencode sgn f)
                      (if (= (bitn fpcr *ah*) 1)
                          (set-flag *ixc* (set-flag *ufc* fpsr))
                        (set-flag *ufc* fpsr)))
                (if (= d u)
                    (mv (dencode d f) fpsr)
                  (let (;; UFC is set when the result is inexact.
                        (fpsr (set-flag *ixc* (set-flag *ufc* fpsr))))
                    (if (= d 0)
                        (mv (zencode sgn f) fpsr)
                      (if (= (abs d) (spn f))
                          (mv (nencode d f) fpsr)
                        (mv (dencode d f) fpsr)))))))
          (mv (nencode r f)
              (if (= r u) fpsr (set-flag *ixc* fpsr))))))))

(defmacro aarch64-post-comp (u fpcr fpsr f &optional (satovfl ''0))
  `(aarch64-post-comp-base ,u ,fpcr ,fpsr ,f ,satovfl))

(add-macro-alias aarch64-post-comp aarch64-post-comp-base)
  
(defthm ieee-rounding-mode-p-of-fpscr-rc
  (ieee-rounding-mode-p (fpscr-rc x))
  :hints (("Goal" :in-theory (enable fpscr-rc))))

(defun aarch64-binary-comp (op a b fpcr fpsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zerp-decode-rel
                                                           binary-inf-sgn
                                                           binary-zero-sgn
                                                           sgnf)))))
  (if (or (infp a f)
          (if (eql op 'div) (zerp b f) (infp b f)))
      (mv (iencode (binary-inf-sgn op a f b f) f) fpsr)
    (let* ((asgn (sgnf a f))
           (bsgn (sgnf b f))
           (aval (decode a f))
           (bval (decode b f))
           (u (binary-eval op aval bval)))
      (if (or (and (eql op 'div) (infp b f)) (= u 0))
          (mv (zencode (binary-zero-sgn op asgn bsgn (fpscr-rc fpcr)) f)
              fpsr)
        (aarch64-post-comp u fpcr fpsr f)))))

(defthm encodingp-nth0-of-aarch64-binary-pre-comp
  (implies (encodingp a f)
           (encodingp (mv-nth 0 (aarch64-binary-pre-comp op a b fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm encodingp-nth1-of-aarch64-binary-pre-comp
  (implies (encodingp b f)
           (encodingp (mv-nth 1 (aarch64-binary-pre-comp op a b fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm natp-nth3-of-aarch64-binary-pre-comp
  (implies (natp fpsr)
           (natp (mv-nth 3 (aarch64-binary-pre-comp op a b fpcr fpsr f))))
  :hints (("Goal" :in-theory (enable set-flag)))
  :rule-classes :type-prescription)

(defun aarch64-binary-spec (op a b fpcr fpsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal"
                                 :in-theory (disable aarch64-binary-pre-comp)))))
  (mv-let (a b result fpsr) (aarch64-binary-pre-comp op a b fpcr fpsr f)
    (if result
        (mv result fpsr)
      (aarch64-binary-comp op a b fpcr fpsr f))))

;; ======================================================================

;; AArch64 fpdot and fpdotadd specs

(defund aarch64-convert-qnan (a fmt1 fmt2)
  (declare (xargs :guard (and (member-equal fmt1 (list (hp) (sp) (dp)))
                              (member-equal fmt2 (list (hp) (sp) (dp)))
                              (encodingp a fmt1))))
  (b* (((unless (member-equal fmt1 (list (hp) (sp) (dp))))
        (er hard 'convert-nan "Source format must be either HP, SP or DP"))
       ((unless (member-equal fmt2 (list (hp) (sp) (dp))))
        (er hard 'convert-nan "Destination format must be either HP, SP or DP"))
       (frac (manf a fmt1))
       (frac (cond ((equal fmt1 (hp))
                    (cat frac 9 0 42))
                   ((equal fmt1 (sp))
                    (cat frac 22 0 29))
                   (t (bits frac 50 0))))
       (sgn (sgnf a fmt1)))
    (cond ((equal fmt2 (hp))
           (cat sgn 1 #x3F 6 (bits frac 50 42) 9))
          ((equal fmt2 (sp))
           (cat sgn 1 #x1FF 9 (bits frac 50 29) 22))
          (t ;; (equal fmt2 (dp))
           (cat sgn 1 #xFFF 12 frac 51)))))

(defund aarch64-process-nans-4 (a1 b1 a2 b2 fpcr fpsr)
  (declare (xargs :guard (and (bvecp fpcr 32)
                              (bvecp fpsr 32)
                              (encodingp a1 (hp))
                              (encodingp b1 (hp))
                              (encodingp a2 (hp))
                              (encodingp b2 (hp)))
                  :guard-hints (("Goal" :in-theory (e/d (encodingp qnanize) ())))))
  ;; Input format is HP. FPCR.AH bit is not used for determining NaN priority.
  (cond ((snanp a1 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan a1 fpcr (hp)) (hp) (sp))
             (set-flag *ioc* fpsr)))
        ((snanp a2 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan a2 fpcr (hp)) (hp) (sp))
             (set-flag *ioc* fpsr)))
        ((snanp b1 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan b1 fpcr (hp)) (hp) (sp))
             (set-flag *ioc* fpsr)))
        ((snanp b2 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan b2 fpcr (hp)) (hp) (sp))
             (set-flag *ioc* fpsr)))
        ((qnanp a1 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan a1 fpcr (hp)) (hp) (sp))
             fpsr))
        ((qnanp a2 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan a2 fpcr (hp)) (hp) (sp))
             fpsr))
        ((qnanp b1 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan b1 fpcr (hp)) (hp) (sp))
             fpsr))
        ((qnanp b2 (hp))
         (mv (aarch64-convert-qnan (aarch64-process-nan b2 fpcr (hp)) (hp) (sp))
             fpsr))
        (t (mv nil fpsr))))

(defund aarch64-fpdot-comp (a1 b1 a2 b2 fpcr fpsr)
  (declare (xargs :guard (and (bvecp fpcr 32)
                              (bvecp fpsr 32)
                              (encodingp a1 (hp))
                              (encodingp b1 (hp))
                              (encodingp a2 (hp))
                              (encodingp b2 (hp)))
                  :guard-hints (("Goal" :in-theory (e/d (sgnf) ())))))
  (b* ((invalid-op (and (= (bitn fpcr *ahp*) 0)
                        (or (and (infp a1 (hp)) (zerp b1 (hp)))
                            (and (zerp a1 (hp)) (infp b1 (hp)))
                            (and (infp a2 (hp)) (zerp b2 (hp)))
                            (and (zerp a2 (hp)) (infp b2 (hp))))))
       (sgn1 (logxor (sgnf a1 (hp)) (sgnf b1 (hp))))
       (sgn2 (logxor (sgnf a2 (hp)) (sgnf b2 (hp))))
       (infp1 (or (infp a1 (hp)) (infp b1 (hp))))
       (infp2 (or (infp a2 (hp)) (infp b2 (hp))))
       (invalid-op (or invalid-op
                       (and (= (bitn fpcr *ahp*) 0)
                            (and infp1 infp2
                                 (not (= sgn1 sgn2)))))))
    (if invalid-op
        (mv (signed-indef (bitn fpcr *ah*) (sp)) (set-flag *ioc* fpsr))
      (if (and (= (bitn fpcr *ahp*) 0)
               (or (and infp1 (= sgn1 0))
                   (and infp2 (= sgn2 0))))
          (mv (iencode 0 (sp)) fpsr)
        (if (and (= (bitn fpcr *ahp*) 0)
                 (or (and infp1 (= sgn1 1))
                     (and infp2 (= sgn2 1))))
            (mv (iencode 1 (sp)) fpsr)
          (b* ((val (+ (* (decode a1 (hp)) (decode b1 (hp)))
                       (* (decode a2 (hp)) (decode b2 (hp))))))
            (if (= val 0)
                (if (= sgn1 sgn2)
                    (mv (zencode sgn1 (sp)) fpsr)
                  (mv (zencode (if (eql (fpscr-rc fpcr) 'rdn) 1 0) (sp))
                      fpsr))
              (aarch64-post-comp val fpcr fpsr (sp)))))))))

(defund aarch64-fpdot-spec (a1 b1 a2 b2 fpcr fpsr)
  (declare (xargs :otf-flg nil
                  :guard (and (encodingp a1 (hp))
                              (encodingp b1 (hp))
                              (encodingp a2 (hp))
                              (encodingp b2 (hp))
                              (bvecp fpcr 32)
                              (bvecp fpsr 32))
                  :guard-hints (("Goal" :in-theory (e/d (sgnf zencode
                                                         encodingp
                                                         aarch64-process-nans-4
                                                         set-flag) ())))))
  (b* ((fz16 (bitn fpcr *fz16*))
       ((mv a1 a2 b1 b2)
        (if1 fz16
             (b* ((a1 (if (denormp a1 (hp)) (zencode (sgnf a1 (hp)) (hp)) a1))
                  (a2 (if (denormp a2 (hp)) (zencode (sgnf a2 (hp)) (hp)) a2))
                  (b1 (if (denormp b1 (hp)) (zencode (sgnf b1 (hp)) (hp)) b1))
                  (b2 (if (denormp b2 (hp)) (zencode (sgnf b2 (hp)) (hp)) b2)))
               (mv a1 a2 b1 b2))
             (mv a1 a2 b1 b2)))
       ((mv result fpsr)
        (if (= (bitn fpcr *ahp*) 0)
            (aarch64-process-nans-4 a1 b1 a2 b2 fpcr fpsr)
          (mv nil fpsr))))
    (if result
        (mv result fpsr)
      (aarch64-fpdot-comp a1 b1 a2 b2 fpcr fpsr))))

(defthm bvecp-of-zencode-sp
  (bvecp (zencode x (sp)) 32)
  :hints (("Goal" :in-theory (e/d (zencode) ()))))

(defthm bvecp-of-nencode-sp
  (bvecp (nencode x (sp)) 32)
  :hints (("Goal" :in-theory (e/d (nencode) ()))))

(defthm bvecp-of-dencode-sp
  (bvecp (dencode x (sp)) 32)
  :hints (("Goal" :in-theory (e/d (dencode) ()))))

(defthm encodingp-of-aarch64-fpdot-spec
  (encodingp (mv-nth 0 (aarch64-fpdot-spec a1 b1 a2 b2 fpcr fpsr)) (sp))
  :hints (("Goal" :in-theory (e/d (aarch64-fpdot-spec
                                   aarch64-fpdot-comp
                                   aarch64-process-nans-4
                                   encodingp
                                   aarch64-convert-qnan)
                                  (abs
                                   acl2::|(< x (if a b c))|)))))

(defthm bvecp-fpsr-aarch64-post-comp
  (implies (bvecp fpsr 32)
           (bvecp (mv-nth 1 (aarch64-post-comp val fpcr fpsr f)) 32))
  :hints (("Goal" :in-theory (e/d (aarch64-post-comp
                                   set-flag) ()))))

(defthm bvecp-fpsr-aarch64-fpdot-comp
  (implies (bvecp fpsr 32)
           (bvecp (mv-nth 1 (aarch64-fpdot-comp a1 b1 a2 b2 fpcr fpsr)) 32))
  :hints (("Goal" :in-theory (e/d (aarch64-fpdot-comp
                                   set-flag) (aarch64-post-comp)))))

(defthm bvecp-fpsr-aarch64-fpdot-spec
  (implies (bvecp fpsr 32)
           (bvecp (mv-nth 1 (aarch64-fpdot-spec a1 b1 a2 b2 fpcr fpsr)) 32))
  :hints (("Goal" :in-theory (e/d (aarch64-fpdot-spec
                                   aarch64-process-nans-4
                                   set-flag) ()))))

(defund aarch64-fpdotadd-spec (acc a1 b1 a2 b2 fpcr fpsr)
  (declare (xargs :guard (and (encodingp acc (sp))
                              (encodingp a1 (hp))
                              (encodingp b1 (hp))
                              (encodingp a2 (hp))
                              (encodingp b2 (hp))
                              (bvecp fpcr 32)
                              (bvecp fpsr 32))
                  :guard-hints (("Goal" :in-theory (e/d ()
                                                        (bvecp-fpsr-aarch64-fpdot-spec))
                                        :use (bvecp-fpsr-aarch64-fpdot-spec)))))
  (b* (((mv dotres fpsr) (aarch64-fpdot-spec a1 b1 a2 b2 fpcr fpsr)))
    (aarch64-binary-spec 'add acc dotres fpcr fpsr (sp))))

;; ======================================================================

;; Extend ARM-SQRT-SPEC to AArch64

(defun aarch64-sqrt-pre-comp-val (a fpcr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (nanp a f)
      (aarch64-process-nan a fpcr f)
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (signed-indef (bitn fpcr *ah*) f)
      ())))

(defun aarch64-sqrt-pre-comp (a fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zencode
                                                           set-flag
                                                           sgnf)))))
  (mv-let
    (a fpsr)
    (if (and (denormp a f)
             (or (and (not (equal f (hp)))
                      (= (bitn fpcr *fz*) 1)
                      (= (bitn fpcr *ah*) 0))
                 (and (equal f (hp))
                      (= (bitn fpcr *fz16*) 1))
                 (and (not (equal f (hp)))
                      (= (bitn fpcr *fiz*) 1))))
        (mv (zencode (sgnf a f) f)
            (if (and (not (equal f (hp)))
                     (= (bitn fpcr *fz*) 1)
                     (= (bitn fpcr *ah*) 0))
                (set-flag *idc* fpsr)
              fpsr))
      (mv a
          (if (and (denormp a f)
                   (not (equal f (hp)))
                   (= (bitn fpcr *fiz*) 0)
                   (= (bitn fpcr *ah*) 1)
                   (= (sgnf a f) 0))
              (set-flag *idc* fpsr)
            fpsr)))
    (mv a
        (aarch64-sqrt-pre-comp-val a fpcr f)
        (arm-sqrt-pre-comp-excp a fpsr f))))

(defthm qsqrt-pos-linear
  (implies (and (rationalp x) (> x 0))
           (> (qsqrt x n) 0))
  :rule-classes :linear)

(defun aarch64-sqrt-comp (a fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (or (zerp a f) (= (sgnf a f) 0))
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           decode
                                                           ddecode
                                                           ndecode
                                                           zerp-decode-rel)))))
  (if (or (infp a f) (zerp a f))
      (mv a fpsr)
    (aarch64-post-comp (qsqrt (decode a f) (+ (prec f) 2))
                       fpcr
                       fpsr
                       f)))

(defthm encodingp-nth0-of-aarch64-sqrt-pre-comp
  (implies (encodingp a f)
           (encodingp (mv-nth 0 (aarch64-sqrt-pre-comp a fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm nonneg-nth0-of-aarch64-sqrt-pre-comp
  (implies (and (not (mv-nth 1 (aarch64-sqrt-pre-comp a fpcr fpsr f)))
                (equal (sgnf (mv-nth 0 (aarch64-sqrt-pre-comp a fpcr fpsr f))
                             f)
                       1))
           (zerp (mv-nth 0 (aarch64-sqrt-pre-comp a fpcr fpsr f))
                 f)))

(defthm natp-nth2-of-aarch64-sqrt-pre-comp
  (implies (natp fpsr)
           (natp (mv-nth 2 (aarch64-sqrt-pre-comp a fpcr fpsr f))))
  :hints (("Goal" :in-theory (enable set-flag)))
  :rule-classes :type-prescription)

(defun aarch64-sqrt-spec (a fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal"
                                 :in-theory (disable aarch64-sqrt-pre-comp)))))
  (mv-let (a result fpsr) (aarch64-sqrt-pre-comp a fpcr fpsr f)
    (if result
        (mv result fpsr)
      (aarch64-sqrt-comp a fpcr fpsr f))))

;; ======================================================================

;; Extend ARM-FMA-SPEC to AArch64

;; Note that this instruction computes A + B * C.

(defund aarch64-fma-undefined-p (a b c fpcr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr))))
  (and (or (infp a f) (infp b f))
       (or (zerp a f)
           (zerp b f)
           (and (not (nanp a f))
                (not (nanp b f))
                (infp c f)
                (not (= (sgnf c f)
                        (logxor (sgnf a f) (sgnf b f))))))
       (or (= (bitn fpcr *ah*) 0)
           (not (nanp c f)))))

(defun aarch64-fma-pre-comp-excp (a b c fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr)
                              (natp fpsr))))
  (if (or (snanp a f) (snanp b f) (snanp c f)
          (aarch64-fma-undefined-p b c a fpcr f))
      (set-flag *ioc* fpsr)
    fpsr))

(defun aarch64-fma-pre-comp-val (a b c fpcr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (let ((ah (bitn fpcr *ah*)))
    (cond ((and (nanp b f) (= ah 1))
           (aarch64-process-nan b fpcr f))

          ((and (nanp c f) (= ah 1))
           (aarch64-process-nan c fpcr f))

          ((and (nanp a f) (= ah 1))
           (aarch64-process-nan a fpcr f))

          ((and (or (infp b f) (infp c f))
                (or (zerp b f) (zerp c f))
                (= ah 1))
           (signed-indef 1 f))

          ((snanp a f)
           (aarch64-process-nan a fpcr f))

          ((snanp b f)
           (aarch64-process-nan b fpcr f))

          ((snanp c f)
           (aarch64-process-nan c fpcr f))

          ((and (or (infp b f) (infp c f))
                (or (zerp b f) (zerp c f)))
           (signed-indef 0 f))

          ((qnanp a f)
           (aarch64-process-nan a fpcr f))

          ((qnanp b f)
           (aarch64-process-nan b fpcr f))

          ((qnanp c f)
           (aarch64-process-nan c fpcr f))

          ((fma-undefined-p b c a f)
           (signed-indef ah f))

          (t nil))))

(defun aarch64-fma-pre-comp (a b c fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zencode
                                                           set-flag
                                                           sgnf)))))
  (mv-let
    (a b c fpsr)
    (if (or (and (not (equal f (hp)))
                 (= (bitn fpcr *fz*) 1)
                 (= (bitn fpcr *ah*) 0))
            (and (equal f (hp))
                 (= (bitn fpcr *fz16*) 1))
            (and (not (equal f (hp)))
                 (= (bitn fpcr *fiz*) 1)))
        (mv (if (denormp a f)
                (zencode (sgnf a f) f)
              a)
            (if (denormp b f)
                (zencode (sgnf b f) f)
              b)
            (if (denormp c f)
                (zencode (sgnf c f) f)
              c)
            (if (and (or (denormp a f) (denormp b f) (denormp c f))
                     (not (equal f (hp)))
                     (= (bitn fpcr *fz*) 1)
                     (= (bitn fpcr *ah*) 0))
                (set-flag *idc* fpsr)
              fpsr))
      (mv a b c
          (if (and (or (denormp a f) (denormp b f) (denormp c f))
                   (not (equal f (hp)))
                   (= (bitn fpcr *fiz*) 0)
                   (= (bitn fpcr *ah*) 1)
                   (not (nanp a f))
                   (not (nanp b f))
                   (not (nanp c f))
                   (not (and (or (infp b f) (infp c f))
                             (or (zerp b f) (zerp c f))))
                   (not (and (infp a f)
                             (or (infp b f) (infp c f))
                             (not (= (sgnf a f)
                                     (logxor (sgnf b f) (sgnf c f)))))))
              (set-flag *idc* fpsr)
            fpsr)))
    (mv a b c
        (aarch64-fma-pre-comp-val a b c fpcr f)
        (aarch64-fma-pre-comp-excp a b c fpcr fpsr f))))

(defun aarch64-fma-comp (a b c fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp sgnf)))))
  (let* ((asgn (sgnf a f))
         (bsgn (sgnf b f))
         (csgn (sgnf c f))
         (aval (decode a f))
         (bval (decode b f))
         (cval (decode c f))
         (u (+ aval (* bval cval))))
    (if (or (infp b f) (infp c f))
        (mv (iencode (logxor bsgn csgn) f) fpsr)
      (if (infp a f)
          (mv a fpsr)
        (if (= u 0)
            (mv (zencode (if (= (logxor bsgn csgn) asgn)
                             asgn
                           (if (eql (fpscr-rc fpcr) 'rdn) 1 0))
                         f)
                fpsr)
          (aarch64-post-comp u fpcr fpsr f))))))

(defthm encodingp-nth0-of-aarch64-fma-pre-comp
  (implies (encodingp a f)
           (encodingp (mv-nth 0 (aarch64-fma-pre-comp a b c fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm encodingp-nth1-of-aarch64-fma-pre-comp
  (implies (encodingp b f)
           (encodingp (mv-nth 1 (aarch64-fma-pre-comp a b c fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm encodingp-nth2-of-aarch64-fma-pre-comp
  (implies (encodingp c f)
           (encodingp (mv-nth 2 (aarch64-fma-pre-comp a b c fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm natp-nth4-of-aarch64-fma-pre-comp
  (implies (natp fpsr)
           (natp (mv-nth 4 (aarch64-fma-pre-comp a b c fpcr fpsr f))))
  :hints (("Goal" :in-theory (enable set-flag)))
  :rule-classes :type-prescription)

(defun aarch64-fma-spec (a b c fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal"
                                 :in-theory (disable aarch64-fma-pre-comp)))))
  (mv-let (a b c result fpsr) (aarch64-fma-pre-comp a b c fpcr fpsr f)
    (if result
        (mv result fpsr)
      (aarch64-fma-comp a b c fpcr fpsr f))))

;; ======================================================================

;; Extend ARM-FSCALE-SPEC to AArch64

(defun aarch64-fscale-pre-comp (a fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zencode
                                                           set-flag
                                                           sgnf)))))
  (mv-let
    (a fpsr)
    (if (and (denormp a f)
             (or (and (not (equal f (hp)))
                      (= (bitn fpcr *fz*) 1)
                      (= (bitn fpcr *ah*) 0))
                 (and (equal f (hp))
                      (= (bitn fpcr *fz16*) 1))
                 (and (not (equal f (hp)))
                      (= (bitn fpcr *fiz*) 1))))
        (mv (zencode (sgnf a f) f)
            (if (and (not (equal f (hp)))
                     (= (bitn fpcr *fz*) 1)
                     (= (bitn fpcr *ah*) 0))
                (set-flag *idc* fpsr)
              fpsr))
      (mv a
          (if (and (denormp a f)
                   (not (equal f (hp)))
                   (= (bitn fpcr *fiz*) 0)
                   (= (bitn fpcr *ah*) 1))
              (set-flag *idc* fpsr)
            fpsr)))
    (mv a
        (if (nanp a f)
            (aarch64-process-nan a fpcr f)
          ())
        (if (snanp a f)
            (set-flag *ioc* fpsr)
          fpsr))))

(defun aarch64-fscale-comp (a b fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp b)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal" :in-theory (enable encodingp
                                                           zerp-decode-rel)))))
  (if (or (zerp a f) (infp a f))
      (mv a fpsr)
    (let* ((fwidth (+ 1 (expw f) (sigw f)))
           (aval (decode a f))
           (bval (si b fwidth))
           (u (* aval (expt 2 bval))))
      (aarch64-post-comp u fpcr fpsr f))))

(defthm encodingp-nth0-of-aarch64-fscale-pre-comp
  (implies (encodingp a f)
           (encodingp (mv-nth 0 (aarch64-fscale-pre-comp a fpcr fpsr f))
                      f))
  :hints (("Goal" :in-theory (enable encodingp zencode))))

(defthm natp-nth2-of-aarch64-fscale-pre-comp
  (implies (natp fpsr)
           (natp (mv-nth 2 (aarch64-fscale-pre-comp a fpcr fpsr f))))
  :hints (("Goal" :in-theory (enable set-flag)))
  :rule-classes :type-prescription)

(defun aarch64-fscale-spec (a b fpcr fpsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp b)
                              (natp fpcr)
                              (natp fpsr))
                  :guard-hints (("Goal"
                                 :in-theory (disable aarch64-fscale-pre-comp)))))
  (mv-let (a result fpsr) (aarch64-fscale-pre-comp a fpcr fpsr f)
    (if result
        (mv result fpsr)
      (aarch64-fscale-comp a b fpcr fpsr f))))

;; ======================================================================

;; Extend Arm BFloat16 specs to AArch64

;; SP product of 2 BF operands. Note that in the case of a normal result, the
;; product is 16-exact so no rounding is required.

(defund aarch64-bfmul16-spec (a b ah)
  (declare (xargs :guard (and (encodingp a (bf))
                              (encodingp b (bf))
                              (bitp ah))
                  :guard-hints (("Goal" :in-theory (enable sgnf)))))
  (let ((sgnr (logxor (sgnf a (bf)) (sgnf b (bf)))))
    (if (or (nanp a (bf))
            (nanp b (bf))
            (and (infp a (bf))
                 (or (zerp b (bf)) (denormp b (bf))))
            (and (infp b (bf))
                 (or (zerp a (bf)) (denormp a (bf)))))
        (signed-indef ah (sp))
      (if (or (infp a (bf)) (infp b (bf)))
          (iencode sgnr (sp))
        (if (or (zerp a (bf)) (denormp a (bf))
                (zerp b (bf)) (denormp b (bf)))
            (zencode sgnr (sp))
          (bf-post-comp (* (ndecode a (bf)) (ndecode b (bf)))))))))

;; SP sum of 2 SP operands

(defund aarch64-bfadd32-spec (a b ah)
  (declare (xargs :guard (and (encodingp a (sp))
                              (encodingp b (sp))
                              (bitp ah))
                  :guard-hints (("Goal" :in-theory (enable sgnf)))))
  (let* ((sgna (sgnf a (sp)))
         (sgnb (sgnf b (sp)))
         (aval (if (or (zerp a (sp)) (denormp a (sp)))
                   0
                 (ndecode a (sp))))
         (bval (if (or (zerp b (sp)) (denormp b (sp)))
                   0
                 (ndecode b (sp))))
         (u (+ aval bval)))
    (if (or (nanp a (sp))
            (nanp b (sp))
            (and (infp a (sp)) (infp b (sp)) (not (= sgna sgnb))))
        (signed-indef ah (sp))
      (if (infp a (sp))
          a
        (if (infp b (sp))
            b
          (if (= u 0)
              (if (= sgna sgnb)
                  (zencode sgna (sp))
                (zencode 0 (sp)))
            (bf-post-comp u)))))))

;; )

(defthm encodingp-of-aarch64-bfmul16
  (encodingp (aarch64-bfmul16-spec a b ah) (sp))
  :hints (("Goal" :in-theory (e/d (aarch64-bfmul16-spec encodingp
                                   bf-post-comp
                                   nencode zencode) ()))))

(defthm encodingp-of-aarch64-bfadd32
  (implies (and (encodingp a (sp))
                (encodingp b (sp)))
           (encodingp (aarch64-bfadd32-spec a b ah) (sp)))
  :hints (("Goal" :in-theory (e/d (aarch64-bfadd32-spec encodingp
                                   bf-post-comp
                                   nencode zencode) ()))))

;; Dot-product of 2 BF vectors of length 2, followed by SP addition.
(defund aarch64-bfdotadd-spec (addend a1 b1 a2 b2 ah)
  (declare (xargs :guard (and (encodingp addend (sp))
                              (encodingp a1 (bf))
                              (encodingp b1 (bf))
                              (encodingp a2 (bf))
                              (encodingp b2 (bf))
                              (bitp ah))))
  (b* ((p1 (aarch64-bfmul16-spec a1 b1 ah))
       (p2 (aarch64-bfmul16-spec a2 b2 ah))
       (sumprod (aarch64-bfadd32-spec p1 p2 ah)))
    (aarch64-bfadd32-spec addend sumprod ah)))

(defthm encodingp-of-aarch64-bfdotadd-spec
  (implies (encodingp addend (sp))
           (encodingp (aarch64-bfdotadd-spec addend a1 b1 a2 b2 ah) (sp)))
  :hints (("Goal" :in-theory (e/d (aarch64-bfdotadd-spec) ()))))

;; Bfloat matrix multiply operation : multiply a 2x4 and transpose of another
;; 2x4 matrix, and add a 2x2 matrix. The 2x4 matrices hold BF entries and the
;; 2x2 addend matrix contains SP entries.

(defund elem (a n size)
  (declare (xargs :guard (and (integerp a)
                              (integerp size)
                              (integerp n))))
  (bits a (1- (* size (1+ n))) (* size n)))

(defund mat-elem-bf (a i j)
  (declare (xargs :guard (and (integerp a)
                              (integerp i)
                              (integerp j))))
  ;; element of a 2x4 matrix
  (elem a (+ (* 4 i) j) 16))

(defund mat-elem-sp (a i j)
  (declare (xargs :guard (and (integerp a)
                              (integerp i)
                              (integerp j))))
  ;; element of a 2x2 matrix
  (elem a (+ (* 2 i) j) 32))

(defthm encodingp-of-elem-16
  (and (encodingp (elem a n 16) (bf))
       (encodingp (elem a n 16) (hp)))
  :hints (("Goal" :in-theory (e/d (elem encodingp) ()))))

(defthm encodingp-of-elem-32
  (encodingp (elem a n 32) (sp))
  :hints (("Goal" :in-theory (e/d (elem encodingp) ()))))

(defthm encodingp-of-mat-elem-bf
  (encodingp (mat-elem-bf a i j) (bf))
  :hints (("Goal" :in-theory (e/d (mat-elem-bf encodingp elem) ()))))

(defthm encodingp-of-mat-elem-sp
  (encodingp (mat-elem-sp a i j) (sp))
  :hints (("Goal" :in-theory (e/d (mat-elem-sp encodingp elem) ()))))

(defund aarch64-bfmmla-spec (addend a b ah)
  (declare (xargs :guard (and (bvecp addend 128)
                              (bvecp a 128)
                              (bvecp b 128)
                              (bitp ah))
                  :guard-hints
                  (("Goal" :in-theory (e/d () ())))))
  (b* ((addend00 (mat-elem-sp addend 0 0))
       (res00 (aarch64-bfdotadd-spec addend00
                                     (mat-elem-bf a 0 0)
                                     (mat-elem-bf b 0 0)
                                     (mat-elem-bf a 0 1)
                                     (mat-elem-bf b 0 1)
                                     ah))
       (res00 (aarch64-bfdotadd-spec res00
                                     (mat-elem-bf a 0 2)
                                     (mat-elem-bf b 0 2)
                                     (mat-elem-bf a 0 3)
                                     (mat-elem-bf b 0 3)
                                     ah))
       (addend01 (mat-elem-sp addend 0 1))
       (res01 (aarch64-bfdotadd-spec addend01
                                     (mat-elem-bf a 0 0)
                                     (mat-elem-bf b 1 0)
                                     (mat-elem-bf a 0 1)
                                     (mat-elem-bf b 1 1)
                                     ah))
       (res01 (aarch64-bfdotadd-spec res01
                                     (mat-elem-bf a 0 2)
                                     (mat-elem-bf b 1 2)
                                     (mat-elem-bf a 0 3)
                                     (mat-elem-bf b 1 3)
                                     ah))
       (addend10 (mat-elem-sp addend 1 0))
       (res10 (aarch64-bfdotadd-spec addend10
                                     (mat-elem-bf a 1 0)
                                     (mat-elem-bf b 0 0)
                                     (mat-elem-bf a 1 1)
                                     (mat-elem-bf b 0 1)
                                     ah))
       (res10 (aarch64-bfdotadd-spec res10
                                     (mat-elem-bf a 1 2)
                                     (mat-elem-bf b 0 2)
                                     (mat-elem-bf a 1 3)
                                     (mat-elem-bf b 0 3)
                                     ah))
       (addend11 (mat-elem-sp addend 1 1))
       (res11 (aarch64-bfdotadd-spec addend11
                                     (mat-elem-bf a 1 0)
                                     (mat-elem-bf b 1 0)
                                     (mat-elem-bf a 1 1)
                                     (mat-elem-bf b 1 1)
                                     ah))
       (res11 (aarch64-bfdotadd-spec res11
                                     (mat-elem-bf a 1 2)
                                     (mat-elem-bf b 1 2)
                                     (mat-elem-bf a 1 3)
                                     (mat-elem-bf b 1 3)
                                     ah)))
    (cat res11 32 res10 32 res01 32 res00 32)))
