(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(include-book "verify-guards")
(local (include-book "bits"))
(local (include-book "reps"))
(local (include-book "round"))
(local (include-book "sqrt"))

(local (defrule abs-type
  (implies (real/rationalp x)
           (real/rationalp (abs x)))
  :rule-classes :type-prescription))

(defrule encodingp-zencode
  (equal (encodingp (zencode sgn f) f)
         (formatp f))
  :enable (encodingp zencode))

(defrule encodingp-iencode
  (equal (encodingp (iencode sgn f) f)
         (formatp f))
  :enable (encodingp iencode))

(defrule encodingp-indef
  (equal (encodingp (indef f) f)
         (formatp f))
  :enable (encodingp indef))

(local (defrule flip-mode-flip-mode
  (equal (flip-mode (flip-mode mode)) mode)
  :enable flip-mode))

(local (defrule expo-rnd->=
  (implies
   (and
    (rationalp x)
    (posp p)
    (common-mode-p rmode))
   (>= (expo (rnd x rmode p)) (expo x)))
  :cases ((= (rnd x rmode p) (expt 2 (1+ (expo x))))
          (= (rnd x rmode p) (- (expt 2 (1+ (expo x))))))
  :hints (("subgoal 3" :use (:instance expo-rnd
                                       (mode rmode)
                                       (n p))))
  :rule-classes :linear))

(local (defrule exactp-rnd-m<=n
  (implies
    (and
      (posp m)
      (integerp n)
      (<= m n))
    (exactp (rnd u mode m) n))
  :use (:instance exactp-<=
         (x (rnd u mode m)))))

(local (defruled expt-expw-as-bias
  (implies (formatp f)
           (equal (expt 2 (expw f))
                  (+ 2 (* 2 (bias f)))))
  :enable bias))

(defrule rnd-nonzero
  (implies
   (and
    (rationalp u)
    (not (equal u 0))
    (posp p)
    (common-mode-p rm))
   (not (equal (rnd u rm p) 0)))
  :cases ((> u 0) (< u 0)))

(local (defruled drepp-drnd-1
  (implies
   (and
    (formatp f)
    (common-mode-p rmode)
    (rationalp u)
    (<= (expo u) (- (bias f)))
    (not (equal (drnd u rmode f) 0))
    (not (equal (abs (drnd u rmode f)) (spn f))))
   (drepp (drnd u rmode f) f))
  :enable sgn
  :disable (abs<spn-as-expo)
  :use ((:instance drnd-exactp-a
          (x u)
          (mode rmode))
        (:instance abs<spn-as-expo
          (x u)))))

(local (defruled drepp-drnd-2
  (implies
   (and
    (equal (drnd u rmode f) u)
    (formatp f)
    (common-mode-p rmode)
    (rationalp u)
    (not (equal u 0))
    (<= (expo u) (- (bias f))))
   (drepp u f))
  :cases ((= u (spn f))
          (= u (- (spn f))))
  :enable (spn sgn)
  :hints (("subgoal 3" :use drepp-drnd-1))))

;;;***************************************************************
;;;                   SSE Operations
;;;***************************************************************

;; Exception flag bits (indices shared by SSE and x87):

(defnd ibit () 0)
(defnd dbit () 1)
(defnd zbit () 2)
(defnd obit () 3)
(defnd ubit () 4)
(defnd pbit () 5)

(in-theory (disable (ibit) (dbit) (zbit) (obit) (ubit) (pbit)))

;; Other MXCSR bits:

(defnd daz () 6)
(defnd imsk () 7)
(defnd dmsk () 8)
(defnd zmsk () 9)
(defnd omsk () 10)
(defnd umsk () 11)
(defnd pmsk () 12)
(defnd ftz () 15)

(in-theory (disable (daz) (imsk) (dmsk) (zmsk) (omsk) (umsk) (pmsk) (ftz)))

(defund mxcsr-masks (mxcsr)
  (declare (xargs :guard (natp mxcsr)))
  (bits mxcsr 12 7))

(defund mxcsr-rc (mxcsr)
  (declare (xargs :guard (natp mxcsr)))
  (case (bits mxcsr 14 13)
    (0 'rne)
    (1 'rdn)
    (2 'rup)
    (3 'rtz)))

(defrule IEEE-rounding-mode-p-mxcsr-rc
  (rtl::IEEE-rounding-mode-p (mxcsr-rc mxcsr))
  :enable mxcsr-rc
  :use (:instance bits-bounds
         (x mxcsr)
         (i 14)
         (j 13)))

;;--------------------------------------------------------------------------------

;; The arguments of SSE-BINARY-SPEC are an operation (add, sub, mul, or div), 2 data
;; inputs, the initial MXCSR register, and the significand and exponent widths. It
;; returns a data result, which is NIL in the event of an unmasked exception, and the
;; updated MXCSR.

;; An implementation is correct if it returns the same MXCSR as SSE-BINARY-SPEC and,
;; in the event that SSE-BINARY-SPEC returns a non-NIL value, it returns the same value.

;; SSE-BINARY-SPEC is based on two auxiliary functions, SSE-BINARY-PRE-COMP and
;; SSE-BINARY-COMP, each of which returns an optional value and a 6-bit vector
;; of exception flags, which are written to the MXCSR.

;; SSE-BINARY-PRE-COMP calls SSE-BINARY-PRE-COMP-EXCP, which detects pre-computation
;; exceptions, and SSE-BINARY-PRE-COMP-VAL, which may compute a value.  If an unmasked
;; exception occurs, the value is invalid and the operation is terminated.  Otherwise,
;; if the value is NIL, then the computation proceeds by calling SSE-BINARY-COMP, and
;; if non-NIL, the operation is terminated and that value is returned.

;; SSE-BINARY-COMP either returns an infinity or decodes the operands and computes the
;; unrounded result.  If that result is 0, then it sets the sign according to the operand
;; signs and the rounding mode and returns.  Otherwise, it calls SSE-POST-COMP, which detects
;; post-computation exceptions and computes the rounded result, which is invalid in the
;; event of an unmasked exception.

(defund set-flag (b flags)
  (declare (xargs :guard (and (natp b)
                              (natp flags))))
  (logior flags (expt 2 b)))

(defrule set-flag-type
  (implies (natp flags)
           (natp (set-flag b flags)))
  :enable set-flag
  :rule-classes :type-prescription)

(defund unmasked-excp-p (flags masks)
  (declare (xargs :guard (and (natp flags)
                              (natp masks))))
  (or (and (= (bitn flags (ibit)) 1) (= (bitn masks (ibit)) 0))
      (and (= (bitn flags (dbit)) 1) (= (bitn masks (dbit)) 0))
      (and (= (bitn flags (zbit)) 1) (= (bitn masks (zbit)) 0))
      (and (= (bitn flags (obit)) 1) (= (bitn masks (obit)) 0))
      (and (= (bitn flags (ubit)) 1) (= (bitn masks (ubit)) 0))
      (and (= (bitn flags (pbit)) 1) (= (bitn masks (pbit)) 0))))

(defund dazify (x daz f)
  (declare (xargs :guard (and (encodingp x f)
                              (natp daz))))
  (if (and (= daz 1) (denormp x f))
      (zencode (sgnf x f) f)
    x))

(defrule encodingp-dazify
  (implies (encodingp a f)
           (encodingp (dazify a daz f) f))
  :enable (encodingp zencode dazify))

(defund binary-undefined-p (op a af b bf)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf))))
  (case op
    (add (and (infp a af) (infp b bf) (not (= (sgnf a af) (sgnf b bf)))))
    (sub (and (infp a af) (infp b bf) (= (sgnf a af) (sgnf b bf))))
    (mul (and (or (infp a af) (infp b bf))
              (or (zerp a af) (zerp b bf))))
    (div (or (and (infp a af) (infp b bf))
             (and (zerp a af) (zerp b bf))))))

(defund sse-binary-pre-comp-excp (op a b f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f))))
  (if (or (snanp a f) (snanp b f))
      (set-flag (ibit) 0)
    (if (or (qnanp a f) (qnanp b f))
        0
      (if (binary-undefined-p op a f b f)
          (set-flag (ibit) 0)
        (if (and (eql op 'div) (zerp b f) (not (infp a f)))
            (set-flag (zbit) 0)
          (if (or (denormp a f) (denormp b f))
              (set-flag (dbit) 0)
            0))))))

(defund sse-binary-pre-comp-val (op a b f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f))))
  (if (nanp a f)
      (qnanize a f)
    (if (nanp b f)
        (qnanize b f)
      (if (binary-undefined-p op a f b f)
          (indef f)
        ()))))

(defund sse-binary-pre-comp (op a b mxcsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp mxcsr))
                  :guard-hints (("goal" :in-theory (disable member)))))
  (let* ((daz (bitn mxcsr (daz)))
         (a (dazify a daz f))
         (b (dazify b daz f)))
    (mv a b (sse-binary-pre-comp-val op a b f) (sse-binary-pre-comp-excp op a b f))))

(defrule encodingp-qnanize
  (implies
    (encodingp x f)
    (encodingp (qnanize x f) f))
  :prep-books ((include-book "log"))
  :enable (encodingp qnanize formatp explicitp sigw expw prec)
  :cases ((bvecp (expt 2 (- (prec f) 2)) (+ 1 (expw f) (sigw f))))
   :hints (("subgoal 2" :in-theory (enable bvecp))))

(local (defrule nrepp-lpn-sgn
  (implies
    (and
      (rationalp r)
      (< (lpn F) (abs r))
      (formatp f))
    (nrepp (* (lpn f) (sgn r)) f))
  :enable (nrepp sgn)
  :use nrepp-lpn))

(local (defrule nrepp-spn-sgn
  (implies
    (and
      (equal (abs (drnd u mode f)) (spn f))
      (formatp f))
  (nrepp (drnd u mode f) f))
  :enable nrepp
  :use nrepp-spn))

(defund sse-post-comp (u mxcsr f)
  (declare (xargs :guard (and (real/rationalp u)
                              (not (= u 0))
                              (natp mxcsr)
                              (formatp f))
                  :guard-hints
                  (("goal"
                    :in-theory (e/d (nrepp nrepp-lpn drepp-drnd-1 drepp-drnd-2
                                           expt-expw-as-bias
                                           abs<spn-as-expo
                                           lpn<abs-as-expo)
                              (abs))))))
  (let* ((rmode (mxcsr-rc mxcsr))
         (r (rnd u rmode (prec f)))
         (rsgn (if (< r 0) 1 0))
         (flags (if (= r u) 0 (set-flag (pbit) 0))))
    (if (> (abs r) (lpn f))
        (let* ((flags (set-flag (obit) flags)))
          (if (= (bitn mxcsr (omsk)) 1)
              (let ((flags (set-flag (pbit) flags)))
                (if (or (and (eql rmode 'rdn) (> r 0))
                        (and (eql rmode 'rup) (< r 0))
                        (eql rmode 'rtz))
                    (mv (nencode (* (sgn r) (lpn f)) f)
                        flags)
                  (mv (iencode rsgn f) flags)))
            (mv () flags)))
      (if (< (abs r) (spn f))
          (if (= (bitn mxcsr (umsk)) 1)
              (if (= (bitn mxcsr (ftz)) 1)
                  (mv (zencode rsgn f) (set-flag (pbit) (set-flag (ubit) flags)))
                (let ((d (drnd u rmode f)))
                  (if (= d u)
                      (mv (dencode d f) flags)
                    (let ((flags (set-flag (pbit) (set-flag (ubit) flags))))
                      (if (= d 0)
                          (mv (zencode rsgn f) flags)
                        (if (= (abs d) (spn f))
                            (mv (nencode d f) flags)
                          (mv (dencode d f) flags)))))))
            (mv () (set-flag (ubit) flags)))
       (mv (nencode r f) flags)))))

(defrule sse-post-comp-type
  (natp (mv-nth 1 (sse-post-comp u mxcsr f)))
  :enable sse-post-comp
  :disable (rnd drnd)
  :rule-classes :type-prescription)

(defund binary-inf-sgn (op a af b bf)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf))))
  (case op
    (add (if (infp a af) (sgnf a af) (sgnf b bf)))
    (sub (if (infp a af) (sgnf a af) (if (zerop (sgnf b bf)) 1 0)))
    ((mul div) (logxor (sgnf a af) (sgnf b bf)))))

(defrule bvecp-1-of-binary-inf-sgn
  (implies (member op '(add sub mul div))
           (bvecp (binary-inf-sgn op a af b bg) 1))
  :enable binary-inf-sgn)

(defund binary-zero-sgn (op asgn bsgn rmode)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (bvecp asgn 1)
                              (bvecp bsgn 1)
                              (IEEE-rounding-mode-p rmode))))
  (case op
    (add (if (= asgn bsgn) asgn (if (eql rmode 'rdn) 1 0)))
    (sub (if (not (= asgn bsgn)) asgn (if (eql rmode 'rdn) 1 0)))
    ((mul div) (logxor asgn bsgn))))

(defrule bvecp-1-of-binary-zero-sgn
  (implies (and (member op '(add sub mul div))
                (bvecp asgn 1)
                (bvecp bsgn 1))
           (bvecp (binary-zero-sgn op asgn bsgn rmode) 1))
  :enable binary-zero-sgn)

(defund binary-eval (op aval bval)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (real/rationalp aval)
                              (real/rationalp bval)
                              (not (and (eql op 'div) (= bval 0))))))
  (case op
    (add (+ aval bval))
    (sub (- aval bval))
    (mul (* aval bval))
    (div (/ aval bval))))

(defund sse-binary-comp (op a b mxcsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp mxcsr))
                  :guard-hints (("Goal" :in-theory (enable decode-0)))))
  (if (or (infp a f) (if (eql op 'div) (zerp b f) (infp b f)))
      (mv (iencode (binary-inf-sgn op a f b f) f) 0)
    (let* ((asgn (sgnf a f))
           (bsgn (sgnf b f))
           (aval (decode a f))
           (bval (decode b f))
           (u (binary-eval op aval bval)))
        (if (or (and (eql op 'div) (infp b f)) (= u 0))
            (mv (zencode (binary-zero-sgn op asgn bsgn (mxcsr-rc mxcsr)) f) 0)
          (sse-post-comp u mxcsr f)))))

(defrule sse-binary-comp-type
  (natp (mv-nth 1 (sse-binary-comp op a b mxcsr f)))
  :enable sse-binary-comp
  :rule-classes :type-prescription)

(defund sse-binary-spec (op a b mxcsr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp mxcsr))
                  :guard-hints (("goal" :in-theory (enable sse-binary-pre-comp)))))
  (mv-let (adaz bdaz result pre-flags) (sse-binary-pre-comp op a b mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (sse-binary-comp op adaz bdaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;--------------------------------------------------------------------------------

;; The arguments of SSE-SQRT-SPEC are a data input, the initial MXCSR register, and
;; the significand and exponent widths. It returns a data result, which is NIL in
;; the event of an unmasked exception, and the updated MXCSR.

(defund sse-sqrt-pre-comp-excp (a f)
  (declare (xargs :guard (encodingp a f)))
  (if (snanp a f)
      (set-flag (ibit) 0)
    (if (qnanp a f)
        0
      (if (and (not (zerp a f)) (= (sgnf a f) 1))
          (set-flag (ibit) 0)
        (if (denormp a f)
            (set-flag (dbit) 0)
          0)))))

(defund sse-sqrt-pre-comp-val (a f)
  (declare (xargs :guard (encodingp a f)))
  (if (nanp a f)
      (qnanize a f)
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (indef f)
      ())))

(defrule sse-sqrt-pre-comp-val-nil
  (implies (and (encodingp a f)
                (not (sse-sqrt-pre-comp-val (dazify a daz f) f))
                (not (zerp (dazify a daz f) f)))
           (= (sgnf (dazify a daz f) f) 0))
  :enable (sgnf sse-sqrt-pre-comp-val)
  :disable (dazify zerp))

(defund sse-sqrt-pre-comp (a mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp mxcsr))))
  (let ((a (dazify a (bitn mxcsr (daz)) f)))
    (mv a (sse-sqrt-pre-comp-val a f) (sse-sqrt-pre-comp-excp a f))))

(defund sse-sqrt-comp (a mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (or (zerp a f) (= (sgnf a f) 0))
                              (natp mxcsr))
                  :guard-hints (("goal" :cases ((> (decode a f) 0))
                                 :in-theory (enable decode ddecode ndecode zerp
                                                    sigf manf)))))
  (if (or (infp a f) (zerp a f))
      (mv a 0)
    (sse-post-comp (qsqrt (decode a f) (+ (prec f) 2)) mxcsr f)))

(defrule sse-sqrt-comp-type
  (natp (mv-nth 1 (sse-sqrt-comp a mxcsr f)))
  :enable sse-sqrt-comp
  :disable qsqrt
  :rule-classes :type-prescription)

(defund sse-sqrt-spec (a mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp mxcsr))
                  :guard-hints (("goal" :in-theory (enable sse-sqrt-pre-comp)))))
  (mv-let (adaz result pre-flags) (sse-sqrt-pre-comp a mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (sse-sqrt-comp adaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;--------------------------------------------------------------------------------

;; The arguments of SSE-FMA-SPEC are three data inputs, the initial MXCSR register, and
;; the significand and exponent widths. It returns a data result, which is NIL in the
;; event of an unmasked exception, and the updated MXCSR.

(defund fma-undefined-p (a b c f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f))))
  (and (or (infp a f) (infp b f))
       (or (zerp a f)
           (zerp b f)
           (and (not (nanp a f))
                (not (nanp b f))
                (infp c f)
                (not (= (sgnf c f)
                        (logxor (sgnf a f) (sgnf b f))))))))

(defund sse-fma-pre-comp-excp (a b c f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f))))
  (if (or (snanp a f) (snanp b f) (snanp c f))
      (set-flag (ibit) 0)
    (if (or (qnanp a f) (qnanp b f) (qnanp c f))
        0
      (if (fma-undefined-p a b c f)
          (set-flag (ibit) 0)
        (if (or (denormp a f) (denormp b f) (denormp c f))
            (set-flag (dbit) 0)
          0)))))

(defund sse-fma-pre-comp-val (a b c f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f))))
  (if (nanp a f)
      (qnanize a f)
    (if (nanp b f)
        (qnanize b f)
      (if (nanp c f)
          (qnanize c f)
        (if (fma-undefined-p a b c f)
            (indef f)
          ())))))

(defund sse-fma-pre-comp (a b c mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp mxcsr))))
  (let* ((daz (bitn mxcsr (daz)))
         (a (dazify a daz f))
         (b (dazify b daz f))
         (c (dazify c daz f)))
    (mv a b c (sse-fma-pre-comp-val a b c f) (sse-fma-pre-comp-excp a b c f))))

(defund sse-fma-comp (a b c mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp mxcsr))))
  (let* ((asgn (sgnf a f))
         (bsgn (sgnf b f))
         (csgn (sgnf c f))
         (aval (decode a f))
         (bval (decode b f))
         (cval (decode c f))
         (u (+ (* aval bval) cval)))
    (if (or (infp a f) (infp b f))
        (mv (iencode (logxor asgn bsgn) f) 0)
      (if (infp c f)
          (mv c 0)
        (if (= u 0)
            (mv (zencode (if (= (logxor asgn bsgn) csgn)
                             csgn
                           (if (eql (mxcsr-rc mxcsr) 'rdn) 1 0))
                         f)
                0)
          (sse-post-comp u mxcsr f))))))

(defrule sse-fma-comp-type
  (natp (mv-nth 1 (sse-fma-comp a b c mxcsr f)))
  :enable sse-fma-comp
  :rule-classes :type-prescription)

(defund sse-fma-spec (a b c mxcsr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp mxcsr))
                  :guard-hints (("goal" :in-theory (enable sse-fma-pre-comp)))))
  (mv-let (adaz bdaz cdaz result pre-flags) (sse-fma-pre-comp a b c mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (sse-fma-comp adaz bdaz cdaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;;***************************************************************
;;;                   x87 Operations
;;;***************************************************************

;; Rounding and precision control in FCW

(defund fcw-rc (fcw)
  (declare (xargs :guard (natp fcw)))
  (case (bits fcw 11 10)
    (0 'rne)
    (1 'rdn)
    (2 'rup)
    (3 'rtz)))

(defrule IEEE-rounding-mode-p-fcw-rc
  (rtl::IEEE-rounding-mode-p (fcw-rc fcw))
  :enable fcw-rc
  :use (:instance bits-bounds
         (x fcw)
         (i 11)
         (j 10)))

(defund fcw-pc (fcw)
  (declare (xargs :guard (natp fcw)))
  (case (bits fcw 9 8)
    ((0 1) 24)
    (2 53)
    (3 64)))

(defrule fcw-pc-type
  (posp (fcw-pc fcw))
  :enable fcw-pc
  :use (:instance bits-bounds
         (x fcw)
         (i 9)
         (j 8))
  :rule-classes :type-prescription)

(defrule fcp-pc-bound
  (<= (fcw-pc fcw) (prec (ep)))
  :enable (fcw-pc ep)
  :use (:instance bits-bounds
         (x fcw)
         (i 9)
         (j 8))
  :rule-classes ((:linear :trigger-terms ((fcw-pc fcw)))))

;; Additional FSW status bits that are set by x87 instructions:

(defnd es () 7)
(defnd bb () 15)
(defnd c1 () 9)

(in-theory (disable (es) (bb) (c1)))

;; Whenever ES (FSW[7]) is set, so is B (FSW[15]):

(defund set-es (fsw)
  (declare (xargs :guard (natp fsw)))
  (set-flag (bb) (set-flag (es) fsw)))

;; C1 is cleared by default:

(defund clear-c1 (fsw)
  (declare (xargs :guard (natp fsw)))
  (logand fsw #xfdff))

(defrule natp-clear-c1
  (natp (clear-c1 fsw))
  :enable clear-c1
  :rule-classes :type-prescription)

;; The arguments of X87-BINARY-SPEC are two data inputs, their formats, and the initial
;; FCW and FSW registers. It returns a data result, which is NIL in the event of an
;; unmasked pre-computation exception, and the updated FSW.

(defund x87-binary-pre-comp-excp (op a af b bf)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf))))
  (if (or (snanp a af) (unsupp a af) (snanp b bf) (unsupp b bf))
      (set-flag (ibit) 0)
    (if (or (qnanp a af) (qnanp b bf))
        0
      (if (binary-undefined-p op a af b bf)
          (set-flag (ibit) 0)
        (if (and (eql op 'div) (zerp b bf) (not (infp a af)))
            (set-flag (zbit) 0)
          (if (or (denormp a af) (pseudop a af) (denormp b bf) (pseudop b bf))
              (set-flag (dbit) 0)
            0))))))

(defund convert-nan-to-ep (x f)
  (declare (xargs :guard (and (encodingp x f)
                              (<= (prec f) 64))))
  (cat (sgnf x f)
       1
       (1- (expt 2 15))
       15
       1
       1
       (manf x f)
       (1- (prec f))
       0
       (- 64 (prec f))))

(defrule encodingp-convert-nan-to-ep
  (encodingp (convert-nan-to-ep x f) (ep))
  :enable (encodingp convert-nan-to-ep ep))

(defund x87-binary-pre-comp-val (op a af b bf)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf)
                              (<= (prec af) 64)
                              (<= (prec bf) 64))))
  (let ((aep (convert-nan-to-ep a af))
        (bep (convert-nan-to-ep b bf)))
    (if (nanp a af)
        (if (nanp b bf)
            (if (> (sigf aep (ep)) (sigf bep (ep)))
                (qnanize aep (ep))
              (if (< (sigf aep (ep)) (sigf bep (ep)))
                  (qnanize bep (ep))
                (if (= (sgnf aep (ep)) 0)
                    (qnanize (convert-nan-to-ep a af) (ep))
                  (qnanize (convert-nan-to-ep b bf) (ep)))))
          (qnanize aep (ep)))
      (if (nanp b bf)
          (qnanize bep (ep))
        (if (binary-undefined-p op a af b bf)
            (indef (ep))
          ())))))

(defund x87-binary-pre-comp (op a af b bf)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf)
                              (<= (prec af) 64)
                              (<= (prec bf) 64))))
    (mv (x87-binary-pre-comp-val op a af b bf) (x87-binary-pre-comp-excp op a af b bf)))

(local (defrule formatp-ep-forward
  (formatp (ep))
  :rule-classes ((:forward-chaining :trigger-terms ((ep))))))

(local (defruled expt-2-13
  (<= (* 3 (expt 2 13)) (* 2 (bias (ep))))
  :enable (ep)
  :rule-classes :linear))

(defund x87-post-comp (u fcw)
  (declare (xargs :guard (and (real/rationalp u)
                              (not (= u 0))
                              (natp fcw))
                  :guard-hints
                  (("goal"
                    :in-theory
                    (e/d (nrepp nrepp-lpn drepp-drnd-1 drepp-drnd-2 expt-2-13
                                expt-expw-as-bias expo-shift exactp-shift
                                abs<spn-as-expo lpn<abs-as-expo)
                         (abs expt (expt) acl2::|(expt c (* d n))|))))))
  (let* ((rmode (fcw-rc fcw))
         (r (rnd u rmode (fcw-pc fcw)))
         (rsgn (if (< r 0) 1 0))
         (flags (if (= r u) 0 (set-flag (pbit) 0))))
    (if (> (abs r) (lpn (ep)))
        (let ((flags (set-flag (obit) flags)))
          (if (= (bitn fcw (obit)) 1)
              (let ((flags (set-flag (pbit) flags)))
                (if (or (and (eql rmode 'rdn) (> r 0))
                        (and (eql rmode 'rup) (< r 0))
                        (eql rmode 'rtz))
                    (mv (nencode (* (sgn r) (lpn (ep))) (ep)) flags)
                  (mv (iencode rsgn (ep)) (set-flag (c1) flags))))
            (let ((s (* r (expt 2 (- (* 3 (expt 2 13)))))))
              (if (> (abs s) (lpn (ep)))
                  (mv (iencode rsgn (ep))
                      (set-flag (c1) (set-flag (pbit) flags)))
                (mv (nencode s (ep))
                    (if (> (abs r) (abs u)) (set-flag (c1) flags) flags))))))
      (if (< (abs r) (spn (ep)))
          (if (= (bitn fcw (ubit)) 1)
              (let ((d (drnd u rmode (ep))))
                (if (= d u)
                    (mv (dencode d (ep)) flags)
                  (let ((flags (set-flag (pbit) (set-flag (ubit) flags))))
                    (if (= d 0)
                        (mv (zencode rsgn (ep)) flags)
                      (if (= (abs d) (spn (ep)))
                          (mv (nencode d (ep)) (set-flag (c1) flags))
                        (mv (dencode d (ep)) (if (> (abs d) (abs u)) (set-flag (c1) flags) flags)))))))
            (let ((flags (set-flag (ubit) flags))
                  (s (* r (expt 2 (* 3 (expt 2 13))))))
              (if (< (abs s) (spn (ep)))
                  (mv (zencode rsgn (ep)) (set-flag (pbit) flags))
                (mv (nencode s (ep)) (if (> (abs r) (abs u)) (set-flag (c1) flags) flags)))))
        (mv (nencode r (ep)) (if (> (abs r) (abs u)) (set-flag (c1) flags) flags))))))

(defrule x87-post-comp-type
  (natp (mv-nth 1 (x87-post-comp u fcw)))
  :enable x87-post-comp
  :disable (member-equal (expt) acl2::|(expt c (* d n))|)
  :rule-classes :type-prescription)

(defund x87-binary-comp (op a af b bf fcw)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf)
                              (natp fcw))
                  :guard-hints (("Goal" :in-theory (enable decode-0)))))
  (if (or (infp a af) (if (eql op 'div) (zerp b bf) (infp b bf)))
      (mv (iencode (binary-inf-sgn op a af b bf) (ep)) 0)
    (let* ((asgn (sgnf a af))
           (bsgn (sgnf b bf))
           (aval (decode a af))
           (bval (decode b bf))
           (u (binary-eval op aval bval)))
        (if (or (and (eql op 'div) (infp b bf)) (= u 0))
            (mv (zencode (binary-zero-sgn op asgn bsgn (fcw-rc fcw)) (ep)) 0)
          (x87-post-comp u fcw)))))

(defrule x87-binary-comp-type
  (natp (mv-nth 1 (x87-binary-comp op a af b bf fcw)))
  :enable x87-binary-comp
  :rule-classes :type-prescription)

(defund x87-binary-spec (op a af b bf fcw fsw)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a af)
                              (encodingp b bf)
                              (<= (prec af) 64)
                              (<= (prec bf) 64)
                              (natp fcw)
                              (natp fsw))
                 :guard-hints (("goal" :in-theory (e/d (x87-binary-pre-comp)
                                                       (member))))))
  (let ((fsw (clear-c1 fsw)))
    (mv-let (result pre-flags) (x87-binary-pre-comp op a af b bf)
      (if (unmasked-excp-p pre-flags fcw)
          (mv () (set-es (logior fsw pre-flags)))
        (if result
            (mv result (logior fsw pre-flags))
          (mv-let (result post-flags) (x87-binary-comp op a af b bf fcw)
            (mv result
                (if (unmasked-excp-p post-flags fcw)
                    (set-es (logior (logior fsw pre-flags) post-flags))
                  (logior (logior fsw pre-flags) post-flags)))))))))


;;--------------------------------------------------------------------------------

;; The arguments of X87-SQRT-SPEC are a data input, its format, and the initial FCW
;; and FSW registers. It returns a data result, which is NIL in the event of an
;; unmasked pre-computation exception, and the updated FSW.

(defund x87-sqrt-pre-comp-excp (a f)
  (declare (xargs :guard (encodingp a f)))
  (if (or (unsupp a f) (snanp a f))
      (set-flag (ibit) 0)
    (if (qnanp a f)
        0
      (if (and (not (zerp a f)) (= (sgnf a f) 1))
          (set-flag (ibit) 0)
        (if (or (denormp a f) (pseudop a f))
            (set-flag (dbit) 0)
          0)))))

(defund x87-sqrt-pre-comp-val (a f)
  (declare (xargs :guard (and (encodingp a f)
                              (<= (prec f) 64))))
  (if (nanp a f)
      (qnanize (convert-nan-to-ep a f) (ep))
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (indef (ep))
      ())))

(defruled x87-sqrt-pre-comp-val-nil
  (implies (and (encodingp a f)
                (not (x87-sqrt-pre-comp-val a f))
                (not (zerp a f)))
           (= (sgnf a f) 0))
  :enable (x87-sqrt-pre-comp-val sgnf))

(defund x87-sqrt-pre-comp (a f)
  (declare (xargs :guard (and (encodingp a f)
                              (<= (prec f) 64))))
  (mv (x87-sqrt-pre-comp-val a f) (x87-sqrt-pre-comp-excp a f)))

(defund x87-sqrt-comp (a f fcw)
  (declare (xargs :guard (and (encodingp a f)
                              (or (zerp a f) (= (sgnf a f) 0))
                              (<= (prec f) 64)
                              (natp fcw))
                  :guard-hints (("goal" :cases ((> (decode a f) 0))
                                 :in-theory (enable decode ddecode ndecode zerp
                                                    sigf manf)))))
  (if (or (infp a f) (zerp a f))
      (mv a 0)
    (x87-post-comp (qsqrt (decode a f) 66) fcw)))

(defrule x87-sqrt-comp-type
  (natp (mv-nth 1 (x87-sqrt-comp a f fcw)))
  :enable x87-sqrt-comp
  :disable qsqrt
  :rule-classes :type-prescription)

(defund x87-sqrt-spec (a f fcw fsw)
  (declare (xargs :guard (and (encodingp a f)
                              (<= (prec f) 64)
                              (natp fcw)
                              (natp fsw))
                  :guard-hints (("goal" :in-theory (enable
                                                    x87-sqrt-pre-comp)))))
  (let ((fsw (clear-c1 fsw)))
    (mv-let (result pre-flags) (x87-sqrt-pre-comp a f)
      (if (unmasked-excp-p pre-flags fcw)
          (mv () (set-es (logior fsw pre-flags)))
        (if result
            (mv result (logior fsw pre-flags))
          (mv-let (result post-flags) (x87-sqrt-comp a f fcw)
            (mv result
                (if (unmasked-excp-p post-flags fcw)
                    (set-es (logior (logior fsw pre-flags) post-flags))
                  (logior (logior fsw pre-flags) post-flags)))))))))

;;;***************************************************************
;;;                   ARM Instructions
;;;***************************************************************

;; FPSCR bits:

(defn ioc () 0) ; exception flags
(defn dzc () 1)
(defn ofc () 2)
(defn ufc () 3)
(defn ixc () 4)
(defn idc () 7)

(defun fpscr-rc (fpscr) ; rounding mode
  (declare (xargs :guard (natp fpscr)))
  (case (bits fpscr 23 22)
    (0 'rne)
    (1 'rup)
    (2 'rdn)
    (3 'rtz)))

(defn fz () 24) ; force-to-zero mode

(defn dn () 25) ; default NaN mode

;;When a NaN is to be resturned and DN is set, the default is used:

(defun process-nan (x fpscr f)
  (declare (xargs :guard (and (encodingp x f)
                              (natp fpscr))))
  (if (= (bitn fpscr (dn)) 1)
      (indef f)
    (qnanize x f)))

;;--------------------------------------------------------------------------------

;; The arguments of ARM-BINARY-SPEC are an operation (add, sub, mul, or div), 2 data
;; inputs, the initial FPSCR register, and a floating-point format.  It returns a data
;; result and the updated FPSCR.

;; ARM-BINARY-SPEC is based on two auxiliary functions: ARM-BINARY-PRE-COMP returns
;; an optional value and an updated FPSCR, and ARM-BINARY-COMP returns a value
;; an updated FPSCR.

;; ARM-BINARY-PRE-COMP calls ARM-BINARY-PRE-COMP-EXCP, which detects pre-computation
;; exceptions, and ARM-BINARY-PRE-COMP-VAL, which may compute a value.  If the value
;; is NIL, then the computation proceeds by calling ARM-BINARY-COMP, and if non-NIL,
;; the operation is terminated and that value is returned.

;; ARM-BINARY-COMP either returns an infinity or decodes the operands and computes the
;; unrounded result.  If that result is 0, then it sets the sign according to the operand
;; signs and the rounding mode and returns.  Otherwise, it calls ARM-POST-COMP, which detects
;; computation exceptions and computes the rounded result.

(defun arm-binary-pre-comp-excp (op a b fpscr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpscr))))
  (if (or (snanp a f) (snanp b f))
      (set-flag (ioc) fpscr)
    (if (or (qnanp a f) (qnanp b f))
        fpscr
      (if (binary-undefined-p op a f b f)
          (set-flag (ioc) fpscr)
        (if (and (eql op 'div) (zerp b f) (not (infp a f)))
            (set-flag (dzc) fpscr)
          fpscr)))))

(defun arm-binary-pre-comp-val (op a b fpscr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpscr))))
  (if (snanp a f)
      (process-nan a fpscr f)
    (if (snanp b f)
        (process-nan b fpscr f)
      (if (qnanp a f)
          (process-nan a fpscr f)
        (if (qnanp b f)
            (process-nan b fpscr f)
          (if (binary-undefined-p op a f b f)
              (indef f)
            ()))))))

(local (defthm denormp-format
  (implies (denormp x f)
           (formatp f))
  :hints (("Goal" :in-theory (enable denormp encodingp)))))

(defun arm-binary-pre-comp (op a b fpscr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpscr))))
  (mv-let (a b fpscr)
          (if (= (bitn fpscr (fz)) 1)
              (mv (if (denormp a f)
                      (zencode (sgnf a f) f)
                    a)
                  (if (denormp b f)
                      (zencode (sgnf b f) f)
                    b)
                  (if (and (or (denormp a f) (denormp b f))
                           (not (equal f (hp))))
                      (set-flag (idc) fpscr)
                    fpscr))
            (mv a b fpscr))
    (mv a b
        (arm-binary-pre-comp-val op a b fpscr f)
        (arm-binary-pre-comp-excp op a b fpscr f))))

(defun arm-post-comp (u fpscr f)
  (declare (xargs :guard (and (real/rationalp u)
                              (not (= u 0))
                              (natp fpscr)
                              (formatp f))
                  :guard-hints
                  (("goal"
                    :use ((:instance bvecp-member (x (bits fpscr 23 22)) (n 2)))
                    :in-theory (e/d (nrepp nrepp-lpn drepp-drnd-1 drepp-drnd-2
                                           expt-expw-as-bias
                                           abs<spn-as-expo
                                           lpn<abs-as-expo)
                              (abs))))))
  (let* ((rmode (fpscr-rc fpscr))
         (r (rnd u rmode (prec f)))
         (sgn (if (< u 0) 1 0)))
    (if (> (abs r) (lpn f))
        (let ((fpscr (set-flag (ofc) (set-flag (ixc) fpscr))))
          (if (or (and (eql rmode 'rdn) (> r 0))
                  (and (eql rmode 'rup) (< r 0))
                  (eql rmode 'rtz))
              (mv (nencode (* (sgn r) (lpn f)) f)
                  fpscr)
            (mv (iencode sgn f) fpscr)))
      (if (< (abs u) (spn f))
          (if (= (bitn fpscr (fz)) 1)
              (mv (zencode sgn f) (set-flag (ufc) fpscr))
            (let ((d (drnd u rmode f)))
              (if (= d u)
                  (mv (dencode d f) fpscr)
                (let ((fpscr (set-flag (ixc) (set-flag (ufc) fpscr))))
                  (if (= d 0)
                      (mv (zencode sgn f) fpscr)
                    (if (= (abs d) (spn f))
                        (mv (nencode d f) fpscr)
                      (mv (dencode d f) fpscr)))))))
        (mv (nencode r f)
            (if (= r u) fpscr (set-flag (ixc) fpscr)))))))

(defun arm-binary-comp (op a b fpscr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpscr))
                  :guard-hints
                  (("goal" :in-theory (enable decode-0)
                           :use ((:instance bvecp-member (x (bits fpscr 23 22)) (n 2)))))))
  (if (or (infp a f) (if (eql op 'div) (zerp b f) (infp b f)))
      (mv (iencode (binary-inf-sgn op a f b f) f) fpscr)
    (let* ((asgn (sgnf a f))
           (bsgn (sgnf b f))
           (aval (decode a f))
           (bval (decode b f))
           (u (binary-eval op aval bval)))
        (if (or (and (eql op 'div) (infp b f)) (= u 0))
            (mv (zencode (binary-zero-sgn op asgn bsgn (fpscr-rc fpscr)) f) fpscr)
          (arm-post-comp u fpscr f)))))

(defun arm-binary-spec (op a b fpscr f)
  (declare (xargs :guard (and (member op '(add sub mul div))
                              (encodingp a f)
                              (encodingp b f)
                              (natp fpscr))
                  :guard-hints
                  (("goal" :in-theory (e/d (set-flag sse-binary-pre-comp) (encodingp encodingp-disjoint-cases formatp member))))))
  (mv-let (a b result fpscr) (arm-binary-pre-comp op a b fpscr f)
    (if result
        (mv result fpscr)
      (arm-binary-comp op a b fpscr f))))


;;--------------------------------------------------------------------------------

;; The arguments of ARM-SQRT-SPEC are a data input, the initial FPSCR register, and
;; a floating-point formay. It returns a data result and the updated FPSCR.

(defun arm-sqrt-pre-comp-excp (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpscr))))
  (if (snanp a f)
      (set-flag (ioc) fpscr)
    (if (qnanp a f)
        fpscr
      (if (and (not (zerp a f)) (= (sgnf a f) 1))
          (set-flag (ioc) fpscr)
        fpscr))))

(defun arm-sqrt-pre-comp-val (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpscr))))
  (if (nanp a f)
      (process-nan a fpscr f)
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (indef f)
      ())))

(defun arm-sqrt-pre-comp (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpscr))))
  (mv-let (a fpscr)
    (if (and (denormp a f) (= (bitn fpscr (fz)) 1))
        (mv (zencode (sgnf a f) f)
            (if (not (equal f (hp)))
                (set-flag (idc) fpscr)
              fpscr))
      (mv a fpscr))
    (mv a (arm-sqrt-pre-comp-val a fpscr f) (arm-sqrt-pre-comp-excp a fpscr f))))

(local (defthm hack-1
  (implies (and (encodingp a f)
                (= (sgnf a f) 0))
           (>= (decode a f) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ddecode ndecode encodingp decode)))))

(defun arm-sqrt-comp (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (or (zerp a f) (= (sgnf a f) 0))
                              (natp fpscr))
                  :guard-hints
                  (("goal" :in-theory (enable decode-0)
                    :use (hack-1
                          (:instance qsqrt-pos (x (decode a f)) (n (+ (prec f) 2)))
                                 (:instance bvecp-member (x (bits fpscr 23 22)) (n 2)))))))
  (if (or (infp a f) (zerp a f))
      (mv a fpscr)
    (arm-post-comp (qsqrt (decode a f) (+ (prec f) 2)) fpscr f)))

(defun arm-sqrt-spec (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpscr))
                  :guard-hints (("goal" :in-theory (enable encodingp sgnf arm-sqrt-pre-comp)))))
  (mv-let (a result fpscr) (arm-sqrt-pre-comp a fpscr f)
    (if result
        (mv result fpscr)
      (arm-sqrt-comp a fpscr f))))


;;--------------------------------------------------------------------------------

;; The arguments of ARM-FMA-SPEC are three data inputs, the initial FPSCR register, and
;; a floating-point format. It returns a data result and the updated FPSCR.
;; Note that this instruction computes A + B * C.

(defun arm-fma-pre-comp-excp (a b c fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpscr))))
  (if (or (snanp a f) (snanp b f) (snanp c f)
          (fma-undefined-p b c a f))
      (set-flag (ioc) fpscr)
    fpscr))

(defun arm-fma-pre-comp-val (a b c fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpscr))))
  (if (snanp a f)
      (process-nan a fpscr f)
    (if (snanp b f)
        (process-nan b fpscr f)
      (if (snanp c f)
          (process-nan c fpscr f)
        (if (fma-undefined-p b c a f)
            (indef f)
          (if (qnanp a f)
              (process-nan a fpscr f)
            (if (qnanp b f)
                (process-nan b fpscr f)
              (if (qnanp c f)
                  (process-nan c fpscr f)
                ()))))))))

(defun arm-fma-pre-comp (a b c fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpscr))))
  (mv-let (a b c fpscr)
          (if (= (bitn fpscr (fz)) 1)
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
                           (not (equal f (hp))))
                      (set-flag (idc) fpscr)
                    fpscr))
            (mv a b c fpscr))
      (mv a b c
          (arm-fma-pre-comp-val a b c fpscr f)
          (arm-fma-pre-comp-excp a b c fpscr f))))

(defun arm-fma-comp (a b c fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpscr))))
  (let* ((asgn (sgnf a f))
         (bsgn (sgnf b f))
         (csgn (sgnf c f))
         (aval (decode a f))
         (bval (decode b f))
         (cval (decode c f))
         (u (+ aval (* bval cval))))
    (if (or (infp b f) (infp c f))
        (mv (iencode (logxor bsgn csgn) f) fpscr)
      (if (infp a f)
          (mv a fpscr)
        (if (= u 0)
            (mv (zencode (if (= (logxor bsgn csgn) asgn)
                             asgn
                           (if (eql (fpscr-rc fpscr) 'rdn) 1 0))
                         f)
                fpscr)
          (arm-post-comp u fpscr f))))))

(defun arm-fma-spec (a b c fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (encodingp b f)
                              (encodingp c f)
                              (natp fpscr))
                  :guard-hints
                  (("goal" :in-theory (e/d (set-flag sse-binary-pre-comp) (encodingp encodingp-disjoint-cases formatp member))))))
  (mv-let (a b c result fpscr) (arm-fma-pre-comp a b c fpscr f)
    (if result
        (mv result fpscr)
      (arm-fma-comp a b c fpscr f))))

;;--------------------------------------------------------------------------------

(defun arm-fscale-pre-comp (a fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp fpscr))))
  (mv-let (a fpscr)
          (if (and (= (bitn fpscr (fz)) 1)
                   (denormp a f))
              (mv (zencode (sgnf a f) f)
                  (set-flag (idc) fpscr))
            (mv a fpscr))
    (mv a
        (if (nanp a f)
            (process-nan a fpscr f)
          ())
        (if (snanp a f)
            (set-flag (ioc) fpscr)
          fpscr))))

(defun arm-fscale-comp (a b fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp b)
                              (natp fpscr))
                  :guard-hints (("Goal" :in-theory (enable decode-0)))))
  (if (or (zerp a f) (infp a f))
      (mv a fpscr)
    (let* ((fwidth (+ 1 (expw f) (sigw f)))
           (aval (decode a f))
           (bval (si b fwidth))
           (u (* aval (expt 2 bval))))
      (arm-post-comp u fpscr f))))

(defun arm-fscale-spec (a b fpscr f)
  (declare (xargs :guard (and (encodingp a f)
                              (natp b)
                              (natp fpscr))))
  (mv-let (a result fpscr) (arm-fscale-pre-comp a fpscr f)
    (if result
        (mv result fpscr)
      (arm-fscale-comp a b fpscr f))))

;;--------------------------------------------------------------------------------

;; Odd-round a non-zero value u and encode in the SP format, with overflow
;; resulting in an infinity and underflow resulting in a zero:

(defund bf-post-comp (u)
  (let ((sgnf (if (< u 0) 1 0))
	(r (rto u 24)))
    (if (> (abs r) (lpn (sp)))
   	(iencode sgnf (sp))
      (if (< (abs u) (spn (sp)))
	  (zencode sgnf (sp))
	(nencode r (sp))))))

;; SP product of 2 BF operands.  Note that in the case of a normal result,
;; the product is 16-exact so no rounding is required:

(defund bfmul16-spec (a b)
  (let ((sgnr (logxor (sgnf a (bf)) (sgnf b (bf)))))
    (if (or (nanp a (bf))
	    (nanp b (bf))
	    (and (infp a (bf))
		 (or (zerp b (bf)) (denormp b (bf))))
	    (and (infp b (bf))
		 (or (zerp a (bf)) (denormp a (bf)))))
        (indef (sp))
      (if (or (infp a (bf)) (infp b (bf)))
	  (iencode sgnr (sp))
        (if (or (zerp a (bf)) (denormp a (bf))
		(zerp b (bf)) (denormp b (bf)))
	    (zencode sgnr (sp))
	  (bf-post-comp (* (ndecode a (bf)) (ndecode b (bf)))))))))

;; SP sum of 2 SP operands:

(defund bfadd32-spec (a b)
  (let* ((sgna (sgnf a (sp)))
	 (sgnb (sgnf b (sp)))
	 (aval (if (or (zerp a (sp)) (denormp a (sp))) 0 (ndecode a (sp))))
	 (bval (if (or (zerp b (sp)) (denormp b (sp))) 0 (ndecode b (sp))))
	 (u (+ aval bval)))
    (if (or (nanp a (sp))
	    (nanp b (sp))
	    (and (infp a (sp)) (infp b (sp)) (not (= sgna sgnb))))
        (indef (sp))
      (if (infp a (sp))
	  a
	(if (infp b (sp))
	    b
	  (if (= u 0)
	      (if (= sgna sgnb)
	          (zencode sgna (sp))
	        (zencode 0 (sp)))		
	    (bf-post-comp u)))))))
