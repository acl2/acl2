(in-package "RTL")

(include-book "definitions")

;;;***************************************************************
;;;                   SSE Operations
;;;***************************************************************

;; Exception flag bits (indices shared by SSE and x87):

(defun ibit () 0)
(defun dbit () 1)
(defun zbit () 2)
(defun obit () 3)
(defun ubit () 4)
(defun pbit () 5)

;; Other MXCSR bits:

(defun daz () 6)
(defun imsk () 7)
(defun dmsk () 8)
(defun zmsk () 9)
(defun omsk () 10)
(defun umsk () 11)
(defun pmsk () 12)
(defun ftz () 15)

(defun mxcsr-masks (mxcsr)
  (bits mxcsr 12 7))

(defun mxcsr-rc (mxcsr)
  (case (bits mxcsr 14 13)
    (0 'rne)
    (1 'rdn)
    (2 'rup)
    (3 'rtz)))

;;--------------------------------------------------------------------------------

;; The arguments of SSE-BINARY-SPEC are an operation (add, sub, mul, or div), 2 data
;; inputs, the initial MXCSR register, and the significand and exponent widths. It
;; returns a data result, which is NIL in the event of an unmasked exception, and the
;; updated MXCSR.

;; An implementation is correct if it returns the same MXCSR as SSE-BINARY-SPEC and,
;; in the event that SSE-BINARY-SPEC returns a non-NIL value, it returns the same value.

;; SSE-BINARY-SPEC is based on two auxiliary functions, SSE-BINARY-PRE-COMP and
;; SSE-BINARY-POST-COMP, each of which returns an optional value and a 6-bit vector
;; of exception flags, which are written to the MXCSR.

;; SSE-BINARY-PRE-COMP calls SSE-BINARY-PRE-COMP-EXCP, which detects pre-computation
;; exceptions, and SSE-BINARY-PRE-COMP-VAL, which may compute a value.  If an unmasked
;; exception occurs, the value is invalid and the operation is terminated.  Otherwise,
;; if the value is NIL, then the computation proceeds by calling FMA-POST-COMP, and
;; if non-NIL, the operation is terminated and that value is returned.

;; FMA-POST-COMP either returns an infinity or decodes the operands and computes the
;; unrounded result.  If that result is 0, then it sets the sign according to the operand
;; signs and the rounding mode and returns.  Otherwise, it calls SSE-ROUND, which detects
;; post-computation exceptions and computes the rounded result, which is invalid in the
;; event of an unmasked exception.

(defun set-flag (b flags)
  (logior flags (expt 2 b)))

(defun unmasked-excp-p (flags masks)
  (or (and (= (bitn flags (ibit)) 1) (= (bitn masks (ibit)) 0))
      (and (= (bitn flags (dbit)) 1) (= (bitn masks (dbit)) 0))
      (and (= (bitn flags (zbit)) 1) (= (bitn masks (zbit)) 0))
      (and (= (bitn flags (obit)) 1) (= (bitn masks (obit)) 0))
      (and (= (bitn flags (ubit)) 1) (= (bitn masks (ubit)) 0))
      (and (= (bitn flags (pbit)) 1) (= (bitn masks (pbit)) 0))))

(defun dazify (x daz f)
  (if (and (= daz 1) (denormp x f))
      (zencode (sgnf x f) f)
    x))

(defun binary-undefined-p (op a af b bf)
  (case op
    (add (and (infp a af) (infp b bf) (not (= (sgnf a af) (sgnf b bf)))))
    (sub (and (infp a af) (infp b bf) (= (sgnf a af) (sgnf b bf))))
    (mul (and (or (infp a af) (infp b bf))
              (or (zerp a af) (zerp b bf))))
    (div (or (and (infp a af) (infp b bf))
             (and (zerp a af) (zerp b bf))))))

(defun sse-binary-pre-comp-excp (op a b f)
  (if (or (snanp a f) (snanp b f))
      (set-flag (ibit) 0)
    (if (or (qnanp a f) (qnanp b f))
        0
      (if (binary-undefined-p op a f b f)
          (set-flag (ibit) 0)
        (if (or (denormp a f) (denormp b f))
            (set-flag (dbit) 0)
          0)))))

(defun sse-binary-pre-comp-val (op a b f)
  (if (nanp a f)
      (qnanize a f)
    (if (nanp b f)
        (qnanize b f)
      (if (binary-undefined-p op a f b f)
          (indef f)
        ()))))

(defun sse-binary-pre-comp (op a b mxcsr f)
  (let* ((daz (bitn mxcsr (daz)))
         (a (dazify a daz f))
         (b (dazify b daz f)))
    (mv a b (sse-binary-pre-comp-val op a b f) (sse-binary-pre-comp-excp op a b f))))

(defun sse-round (u mxcsr f)
  (let* ((rmode (mxcsr-rc mxcsr))
         (r (rnd u rmode (prec f)))
         (rsgn (if (< r 0) 1 0))
         (flags (if (= r u) 0 (set-flag (pbit) 0))))
    (if (> (abs r) (lpn f))
        (let* ((flags (set-flag (obit) flags)))
          (if (= (bitn mxcsr (omsk)) 1)
              (let ((flags (set-flag (pbit) flags)))
                (if (or (and (= rmode 'rdn) (> r 0))
                        (and (= rmode 'rup) (< r 0))
                        (= rmode 'rtz))
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

(defun binary-inf-sgn (op a af b bf)
  (case op
    (add (if (infp a af) (sgnf a af) (sgnf b bf)))
    (sub (if (infp a af) (sgnf a af) (if (zerop (sgnf b bf)) 1 0)))
    ((mul div) (logxor (sgnf a af) (sgnf b bf)))))

(defun binary-zero-sgn (op asgn bsgn rmode)
  (case op
    (add (if (= asgn bsgn) asgn (if (= rmode 'rdn) 1 0)))
    (sub (if (not (= asgn bsgn)) asgn (if (= rmode 'rdn) 1 0)))
    ((mul div) (logxor asgn bsgn))))

(defun binary-eval (op aval bval)
  (case op
    (add (+ aval bval))
    (sub (- aval bval))
    (mul (* aval bval))
    (div (/ aval bval))))

(defun sse-binary-post-comp (op a b mxcsr f)
  (if (or (infp a f) (and (not (= op 'div)) (infp b f)))
      (mv (iencode (binary-inf-sgn op a f b f) f) 0)
    (let* ((asgn (sgnf a f))
           (bsgn (sgnf b f))
           (aval (decode a f))
           (bval (decode b f))
           (u (binary-eval op aval bval)))
        (if (or (and (= op 'div) (infp b f)) (= u 0))
            (mv (zencode (binary-zero-sgn op asgn bsgn (mxcsr-rc mxcsr)) f) 0)
          (sse-round u mxcsr f)))))

(defun sse-binary-spec (op a b mxcsr f)
  (mv-let (adaz bdaz result pre-flags) (sse-binary-pre-comp op a b mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (sse-binary-post-comp op adaz bdaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;--------------------------------------------------------------------------------

;; The arguments of SSE-SQRT-SPEC are a data input, the initial MXCSR register, and
;; the significand and exponent widths. It returns a data result, which is NIL in
;; the event of an unmasked exception, and the updated MXCSR.

(defun sse-sqrt-pre-comp-excp (a f)
  (if (snanp a f)
      (set-flag (ibit) 0)
    (if (qnanp a f)
        0
      (if (and (not (zerp a f)) (= (sgnf a f) 1))
          (set-flag (ibit) 0)
        (if (denormp a f)
            (set-flag (dbit) 0)
          0)))))

(defun sse-sqrt-pre-comp-val (a f)
  (if (nanp a f)
      (qnanize a f)
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (indef f)
      ())))

(defun sse-sqrt-pre-comp (a mxcsr f)
  (let ((a (dazify a (bitn mxcsr (daz)) f)))
    (mv a (sse-sqrt-pre-comp-val a f) (sse-sqrt-pre-comp-excp a f))))

(defun sse-sqrt-post-comp (a mxcsr f)
  (if (or (infp a f) (zerp a f))
      (mv a 0)
    (sse-round (qsqrt (decode a f) (+ (prec f) 2)) mxcsr f)))

(defun sse-sqrt-spec (a mxcsr f)
  (mv-let (adaz result pre-flags) (sse-sqrt-pre-comp a mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (sse-sqrt-post-comp adaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;--------------------------------------------------------------------------------

;; The arguments of FMA-SPEC are three data inputs, the initial MXCSR register, and
;; the significand and exponent widths. It returns a data result, which is NIL in the
;; event of an unmasked exception, and the updated MXCSR.

(defun fma-undefined-p (a b c f)
  (and (or (infp a f) (infp b f))
       (or (zerp a f)
           (zerp b f)
           (and (infp c f)
                (not (= (sgnf c f)
                        (logxor (sgnf a f) (sgnf b f))))))))

(defun fma-pre-comp-excp (a b c f)
  (if (or (snanp a f) (snanp b f) (snanp c f))
      (set-flag (ibit) 0)
    (if (or (qnanp a f) (qnanp b f) (qnanp c f))
        0
      (if (fma-undefined-p a b c f)
          (set-flag (ibit) 0)
        (if (or (denormp a f) (denormp b f) (denormp c f))
            (set-flag (dbit) 0)
          0)))))

(defun fma-pre-comp-val (a b c f)
  (if (nanp a f)
      (qnanize a f)
    (if (nanp b f)
        (qnanize b f)
      (if (nanp c f)
          (qnanize c f)
        (if (fma-undefined-p a b c f)
            (infp c f)
          ())))))

(defun fma-pre-comp (a b c mxcsr f)
  (let* ((daz (bitn mxcsr (daz)))
         (a (dazify a daz f))
         (b (dazify b daz f))
         (c (dazify c daz f)))
    (mv a b c (fma-pre-comp-val a b c f) (fma-pre-comp-excp a b c f))))

(defun fma-post-comp (a b c mxcsr f)
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
                           (if (= (mxcsr-rc mxcsr)'rdn) 1 0))
                         f)
                0)
          (sse-round u mxcsr f))))))

(defun fma-spec (a b c mxcsr f)
  (mv-let (adaz bdaz cdaz result pre-flags) (fma-pre-comp a b c mxcsr f)
    (if (unmasked-excp-p pre-flags (mxcsr-masks mxcsr))
        (mv () (logior mxcsr pre-flags))
      (if result
          (mv result (logior mxcsr pre-flags))
        (mv-let (result post-flags) (fma-post-comp adaz bdaz cdaz mxcsr f)
          (mv (and (not (unmasked-excp-p post-flags (mxcsr-masks mxcsr)))
                   result)
              (logior (logior mxcsr pre-flags) post-flags)))))))


;;;***************************************************************
;;;                   x87 Operations
;;;***************************************************************

;; Rounding and precision control in FCW

(defun fcw-rc (fcw)
  (case (bits fcw 11 10)
    (0 'rne)
    (1 'rdn)
    (2 'rup)
    (3 'rtz)))

(defun fcw-pc (fcw)
  (case (bits fcw 9 8)
    ((0 1) 24)
    (2 53)
    (3 64)))

;; Additional FSW status bits that are set by x87 instructions:

(defun es () 7)
(defun bb () 15)
(defun c1 () 9)

;; Whenever ES (FSW[7]) is set, so is B (FSW[15]):

(defun set-es (fsw)
  (set-flag (bb) (set-flag (es) fsw)))

;; C1 is cleared by default:

(defun clear-c1 (fsw)
  (logand fsw #xfdff))

;; The arguments of X87-BINARY-SPEC are two data inputs, their formats, and the initial
;; FCW and FSW registers. It returns a data result, which is NIL in the event of an
;; unmasked pre-computation exception, and the updated FSW.

(defun x87-binary-pre-comp-excp (op a af b bf)
  (if (or (snanp a af) (unsupp a af) (snanp b bf) (unsupp b bf))
      (set-flag (ibit) 0)
    (if (or (qnanp a af) (qnanp b bf))
        0
      (if (binary-undefined-p op a af b bf)
          (set-flag (ibit) 0)
        (if (or (denormp a af) (pseudop a af) (denormp b bf) (pseudop b bf))
            (set-flag (dbit) 0)
          0)))))

(defun convert-nan-to-ep (x f)
  (cat (sgnf x f)
       1
       (1- (expt 2 15))
       16
       1
       1
       (manf x f)
       (1- (prec f))
       0
       (- 64 (prec f))))

(defun x87-binary-pre-comp-val (op a af b bf)
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

(defun x87-binary-pre-comp (op a af b bf)
    (mv (x87-binary-pre-comp-val op a af b bf) (x87-binary-pre-comp-excp op a af b bf)))

(defun x87-round (u fcw)
  (let* ((rmode (fcw-rc fcw))
         (r (rnd u rmode (fcw-pc fcw)))
         (rsgn (if (< r 0) 1 0))
         (flags (if (= r u) 0 (set-flag (pbit) 0))))
    (if (> (abs r) (lpn (ep)))
        (let ((flags (set-flag (obit) flags)))
          (if (= (bitn fcw (obit)) 1)
              (let ((flags (set-flag (pbit) flags)))
                (if (or (and (= rmode 'rdn) (> r 0))
                        (and (= rmode 'rup) (< r 0))
                        (= rmode 'rtz))
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

(defun x87-binary-post-comp (op a af b bf fcw)
  (if (or (infp a af) (and (not (= op 'div)) (infp b bf)))
      (mv (iencode (binary-inf-sgn op a af b bf) (ep)) 0)
    (let* ((asgn (sgnf a af))
           (bsgn (sgnf b bf))
           (aval (decode a af))
           (bval (decode b bf))
           (u (binary-eval op aval bval)))
        (if (or (and (= op 'div) (infp b bf)) (= u 0))
            (mv (zencode (binary-zero-sgn op asgn bsgn (fcw-rc fcw)) (ep)) 0)
          (x87-round u fcw)))))

(defun x87-binary-spec (op a af b bf fcw fsw)
  (let ((fsw (clear-c1 fsw)))
    (mv-let (result pre-flags) (x87-binary-pre-comp op a af b bf)
      (if (unmasked-excp-p pre-flags fcw)
          (mv () (set-es (logior fsw pre-flags)))
        (if result
            (mv result (logior fsw pre-flags))
          (mv-let (result post-flags) (x87-binary-post-comp op a af b bf fcw)
            (mv result
                (if (unmasked-excp-p post-flags fcw)
                    (set-es (logior (logior fsw pre-flags) post-flags))
                  (logior (logior fsw pre-flags) post-flags)))))))))


;;--------------------------------------------------------------------------------

;; The arguments of X87-SQRT-SPEC are a data input, its format, and the initial FCW
;; and FSW registers. It returns a data result, which is NIL in the event of an
;; unmasked pre-computation exception, and the updated FSW.

(defun x87-sqrt-pre-comp-excp (a f)
  (if (or (unsupp a f) (snanp a f))
      (set-flag (ibit) 0)
    (if (qnanp a f)
        0
      (if (and (not (zerp a f)) (= (sgnf a f) 1))
          (set-flag (ibit) 0)
        (if (or (denormp a f) (pseudop a f))
            (set-flag (dbit) 0)
          0)))))

(defun x87-sqrt-pre-comp-val (a f)
  (if (nanp a f)
      (qnanize (convert-nan-to-ep a f) (ep))
    (if (and (not (zerp a f)) (= (sgnf a f) 1))
        (indef (ep))
      ())))

(defun x87-sqrt-pre-comp (a f)
  (mv (x87-sqrt-pre-comp-val a f) (x87-sqrt-pre-comp-excp a f)))

(defun x87-sqrt-post-comp (a f fcw)
  (if (or (infp a f) (zerp a f))
      (mv a 0)
    (x87-round (qsqrt (decode a f) 66) fcw)))

(defun x87-sqrt-spec (a f fcw fsw)
  (let ((fsw (clear-c1 fsw)))
    (mv-let (result pre-flags) (x87-sqrt-pre-comp a f)
      (if (unmasked-excp-p pre-flags fcw)
          (mv () (set-es (logior fsw pre-flags)))
        (if result
            (mv result (logior fsw pre-flags))
          (mv-let (result post-flags) (x87-sqrt-post-comp a f fcw)
            (mv result
                (if (unmasked-excp-p post-flags fcw)
                    (set-es (logior (logior fsw pre-flags) post-flags))
                  (logior (logior fsw pre-flags) post-flags)))))))))
