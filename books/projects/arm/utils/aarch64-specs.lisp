;; Cuong Chau <ckc8687@gmail.com>

;; August 2021

;; Extend Arm floating-point specs to AArch64 that includes two new control
;; bits FIZ and AH

(in-package "RTL")

(include-book "rtl-utils")

(local (arith-5-for-rtl))

;; ======================================================================

;; Extend ARM-BINARY-SPEC to AArch64

;; FPCR bits:

(defconst *fiz*   0)
(defconst *ah*    1)
(defconst *fz16* 19)
(defconst *fz*   24)
(defconst *dn*   25)

;; FPSR bits:

(defconst *ioc* 0)
(defconst *dzc* 1)
(defconst *ofc* 2)
(defconst *ufc* 3)
(defconst *ixc* 4)
(defconst *idc* 7)

(defun aarch64-process-nan-1 (x fpcr f)
  (declare (xargs :guard (and (encodingp x f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (= (bitn fpcr *dn*) 1)
      (if (= (bitn fpcr *ah*) 1)
          (logior (indef f)
                  (expt 2 (+ (expw f) (sigw f))))
        (indef f))
    (qnanize x f)))

(defun aarch64-process-nan-2 (x y fpcr f)
  (declare (xargs :guard (and (encodingp x f)
                              (encodingp y f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (= (bitn fpcr *dn*) 1)
      (if (= (bitn fpcr *ah*) 1)
          (logior (indef f)
                  (expt 2 (+ (expw f) (sigw f))))
        (indef f))
    (if (and (= (bitn fpcr *ah*) 1)
             (qnanp y f))
        y
      (qnanize x f))))

(defun aarch64-binary-pre-comp-val (op a b fpcr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (snanp a f)
      (aarch64-process-nan-1 a fpcr f)
    (if (snanp b f)
        (aarch64-process-nan-2 b a fpcr f)
      (if (qnanp a f)
          (aarch64-process-nan-1 a fpcr f)
        (if (qnanp b f)
            (aarch64-process-nan-1 b fpcr f)
          (if (binary-undefined-p op a f b f)
              (if (= (bitn fpcr *ah*) 1)
                  (logior (indef f)
                          (expt 2 (+ (expw f) (sigw f))))
                (indef f))
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

(defun aarch64-post-comp (u fpcr fpsr f)
  (declare (xargs :guard (and (real/rationalp u)
                              (not (= u 0))
                              (natp fpcr)
                              (natp fpsr)
                              (formatp f))
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
                                       (:instance nrepp-minus
                                                  (x (spn f)))
                                       (:instance nrepp-minus
                                                  (x (lpn f)))
                                       (:instance drnd-exactp-a
                                                  (x u)
                                                  (mode (fpscr-rc fpcr)))
                                       (:instance rnd-drnd-up
                                                  (x u)
                                                  (mode (fpscr-rc fpcr))))
                                 :in-theory (e/d (sgn set-flag rnd-minus)
                                                 (rationalp-abs
                                                  acl2::|(< x (if a b c))|
                                                  nrepp-minus))))))
  (let* ((rmode (fpscr-rc fpcr))
         (r (rnd u rmode (prec f)))
         (d (drnd u rmode f))
         (sgn (if (< u 0) 1 0)))
    (if (> (abs r) (lpn f))
        (let ((fpsr (set-flag *ofc* (set-flag *ixc* fpsr))))
          (if (or (and (eql rmode 'rdn) (> r 0))
                  (and (eql rmode 'rup) (< r 0))
                  (eql rmode 'rtz))
              (mv (nencode (* (sgn r) (lpn f)) f)
                  fpsr)
            (mv (iencode sgn f) fpsr)))
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
                (let ((fpsr (set-flag *ixc* (set-flag *ufc* fpsr))))
                  (if (= d 0)
                      (mv (zencode sgn f) fpsr)
                    (if (= (abs d) (spn f))
                        (mv (nencode d f) fpsr)
                      (mv (dencode d f) fpsr)))))))
        (mv (nencode r f)
            (if (= r u) fpsr (set-flag *ixc* fpsr)))))))

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

;; Extend ARM-SQRT-SPEC to AArch64

(defun aarch64-sqrt-pre-comp-val (a fpcr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpcr))
                  :guard-hints (("Goal" :in-theory (enable encodingp)))))
  (if (nanp a f)
      (aarch64-process-nan-1 a fpcr f)
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (if (= (bitn fpcr *ah*) 1)
            (logior (indef f)
                    (expt 2 (+ (expw f) (sigw f))))
          (indef f))
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
            (aarch64-process-nan-1 a fpcr f)
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
