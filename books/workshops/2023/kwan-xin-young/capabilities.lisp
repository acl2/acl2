(in-package "ACL2")

; Matt K. mod: certification with ACL2 based on Allegro CL seemed to be taking
; about 3 hours, so let's exclude that Lisp.
; cert_param: (non-allegro)

(include-book "operations-nbp")

(include-book "std/util/define" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; Capability constants
(defconst *xlen*  64)   ;; Architectural address size in bits
(defconst *clen* 128)   ;; Architectural capability size in bits
(defconst *mw*    14)   ;; Mantissa width
(defconst *tw*    12)   ;; width for encoded top
(defconst *eh*     3)   ;; half width used for storing E

;; MEMORY-RESIDENT CAPABILITIES
;; This section models memory-resident (or in-memory as referred to in the
;; CHERI documentation) capabilities according to the CHERI Concentrate
;; Compression format found in CHERI ISA v8

;; Representation of CHERI Concentrate Compression capabilities:
;;
;;                         |-------bounds---------|
;;     p            otype   I   T    TE   B     BE
;; |--------|   |----------|-|-----|---|------|---|
;;     16     3      18     1   9    3    11    3
;; 63                                             0
;;                      address
;; |----------------------------------------------|
;;                        64

;; Bounds encoding:

;;  MW - mantissa width, for 128-bit capabilities MW == 14

;;   B - MW-bit value that forms "base" of bounds, slightly compressed, in one
;;       of two formats depending on the I (I_E in documentation) bit

;;   T - MW-bit value that forms "base" of bounds, slightly compressed, in one
;;       of two formats depending on the I (I_E in documentation) bit, top two
;;       bits not explicit in memory

;;   I - internal exponent bit that selects between two formats, if set then
;;       exponent is stored instead of lower 3 bits of B & T (reduces precision
;;       by 3 bits), otherwise exponent is zero and full width of B & T used

;;   E - 6-bit exponent, determines position at which B & T are inserted in

;; -------------------------------------------------------
;; helper functions
;; -------------------------------------------------------
;; read last <len> bits after shifting shift bits to the right
(defmacro nb-ash (shift len seq)
  `(let* ((ash-seq (ash ,seq (- ,shift)))
          (len-bit (1- (expt 2 ,len))))
     (logand ash-seq len-bit)))

;; recognizer for compression
(defun compressionp (c)
  (declare (xargs :guard t))
  (and (integerp c)
       (<= 0 c)
       (b* ((exp (expt 2 (1+ (+ *mw* *tw*))))
            (TE (nb-ash *mw* *eh* c))
            (BE (nb-ash 0 *eh* c))
            (IE (nb-ash (+ *tw* *mw*) 1 c))
            (E (logior (ash TE *eh*) BE)))
           (and (< c exp)
                (natp E)
                ;; if IE = 1, {TE, BE <= 52}
                (or (= IE 0) (<= E 52))))))

;; if n is an at most b bits nat
(defmacro nbp (n b)
  `(and (integerp ,n)
        (<= 0 ,n)
        (< ,n (expt 2 ,b))))

(std::defaggregate bounds
    ((top  (and (natp top) (<= top (expt 2 *xlen*))))
     (base (nbp base *xlen*))))

;; See Section 3.5.4 of CHERI ISA v8 for decoding

;; --------------------------------------------------------
;; input compression,
;; returns (E: block size, TS: T[12:0], BL: B[14:0],
;;         Lcarry: carry bit of length=top-base, Lmsb=most significant bit of len)

;; for small block size mode
(defun vars-small-seg (c)
  (declare (xargs :guard (compressionp c)
                  :guard-debug T))
  (b* ((TS (nb-ash *mw* *tw* c))        ;; tshort=t[11:0]
       (BS (nb-ash 0 *tw* c))           ;; bshort=b[11:0]
       (BL (nb-ash 0 *mw* c))           ;; Blong=B[13:0]
       (Lcarry (if (< TS BS) 1 0)))
    ;; (E TS BL Lcarry Lmsb)
    (mv 0 TS BL Lcarry 0)))

;; for large block size mode
(defun vars-large-seg (c)
  (declare (xargs :guard (compressionp c)))
  (b* ((TE (nb-ash *mw* *eh* c))                    ;; e[5:3]
       (BE (nb-ash 0 *eh* c))                       ;; E[2:0]
       (E (logior (ash TE *eh*) BE))                ;; E[5:0]
       (TSH (nb-ash (+ *Mw* *eh*) (- *tw* *eh*) c)) ;; tshorthigh=t[11:3]
       (BSH (nb-ash *EH* (- *tw* *eh*) c))          ;; bshorthigh=b[11:3]
       (BLH (nb-ash *EH* (- *mw* *eh*) c))          ;; blonghigh=b[13:3]
       (Lcarry (if (< TSH BSH) 1 0))
       (TS (ash TSH *eh*))                          ;; T[11:0]
       (BL (ash BLH *eh*)))                         ;; B[13:0]
    ;; (E TS BL Lcarry Lmsb)
    (mv E TS BL Lcarry 1)))

;; -----------------------------------------------------------------
;; out-of-range truncation could happen to B and T when base and top
;; are compressed, in which case the least significant bit of B / T
;; needs to be incremented / decremented
;;
;; corrections returns 1 if T / B needs to be incremented,
;;                     -1                     decremented,
;;                     0    there is no out-of-range truncation
(defun correction (A R bound)
  (declare (xargs :guard (and (nbp A 3) (nbp bound 3)
                              (integerp R) (<= -1 R) (< R 7))))
  (cond ((and (< A R) (<= R bound)) -1)
        ((and (<= R A) (< bound R)) 1)
        (T 0)))

;; returns correction bits for TL and BL
(defun corrections (addr TL BL E)
  (declare (xargs :guard (and (nbp addr *xlen*)
                              (nbp BL *mw*)
                              (nbp TL *mw*)
                              (natp E)
                              (<= E 52))
                  :verify-guards nil))
  (b* ((shift (1- *tw*))
       (AM (nb-ash (+ E shift) *eh* addr))
       (BM (nb-ash shift *eh* BL))
       (TM (nb-ash shift *eh* TL))
       (R (1- BM)))
    (mv (correction AM R TM)
        (correction AM R BM))))

;; input compression c and address addr,
;; output decoded compression
(define decode-compression ((c compressionp) (addr (nbp addr *xlen*)))
  (declare (xargs :verify-guards nil))
  (b* ((IE (nb-ash (+ *mw* *tw*) 1 c))
       ((mv E TS BL Lcarry Lmsb)
        (if (= IE 0)
            (vars-small-seg c)
            (vars-large-seg c)))
       (BLH (+ (nb-ash *tw* (- *mw* *tw*) BL) Lcarry Lmsb))
       (TLH (nb-ash 0 (- *mw* *tw*) BLH)) ;; B[13:12] (nbp TLH 2)
       (TL (logior (ash TLH *tw*) TS))
       ((mv CT CB) (corrections addr TL BL E))
       (AT (ash addr (- (+ *mw* E))))
       (top (nb-ash 0 (1+ *xlen*)
                    (ash (logior (ash (+ AT CT) *mw*) TL) E)))
       (base (nb-ash 0 *xlen*
                     (ash (logior (ash (+ AT CB) *mw*) BL) E)))
       (top (if (and (< E 51)
                     (< 1 (- (nb-ash 63 2 top) (nb-ash 63 1 base))))
                (nb-ash 0 *xlen* top)
                top)))
      ;; top, base
      (bounds top base)))

;; -------------------------------------------------------------
;; START - verifications of decode-compression related function
;;
;; list of items to verify:
;; 1) guards for corrections
;; 2) (nbp TL *MW*=14)
;; 3) output from vars-large-seg and vars-small-seg are correct
;;    - (nbp BL *MW*=14)
;;    - (nbp TS *TW*=12)
;;    - (and (natp E) (<= E 52))
;;    - Lcarry and Lmsb are i bit each
;; --------------------------------------------------------------

;; 1) corrections guard verification ----------------------------
(verify-guards corrections :hints (("Goal" :in-theory (disable ash logand))))

;; 2) ----------------------------------------------------------
(defmacro TL (TS BL Lcarry Lmsb)
  `(b* ((BLH2 (nb-ash *tw* (- *mw* *tw*) ,BL))
        (BLH (+ BLH2 ,Lcarry ,Lmsb))
        (TLH (nb-ash 0 (- *mw* *tw*) BLH)))
     (logior (ash TLH *tw*) ,TS)))

;; notice the input hypotheses about TS, BL, Lcarry, and Lmsb:
;; these are the proofs burden that we'll resolve next.
(def-gl-thm decode-compression-guard-TL
    :hyp   (and (nbp BL *mw*)
                (nbp TS *tw*)
                (nbp Lcarry 1)
                (nbp Lmsb 1))
    :concl (nbp (TL TS BL Lcarry Lmsb) *mw*)
    :g-bindings `((BL ,(gl::g-int 0 2 (1+ *mw*)))
                  (TS ,(gl::g-int 1 2 (1+ *mw*)))
                  (Lcarry ,(gl::g-int (* 2 (1+ *mw*)) 2 2))
                  (Lmsb ,(gl::g-int (+ 3 (* 2 *mw*)) 2 2))))


;; 3) + hypotheses for 2) -------------------------------------
;; verifying output from vars-<smarll/large>-seg, (mv E TS BL Lcarry Lmsb),
;; has the correct number of bits, which provides the hypotheses needed
;; by decode-compression-guard-TL.
(defmacro vars-correct-bit-p (E TS BL Lcarry Lmsb)
  `(and (natp ,E)
        (<= ,E 52)
        (nbp ,BL *mw*)
        (nbp ,TS *tw*)
        (nbp ,Lcarry 1)
        (nbp ,Lmsb 1)))

(defmacro vars-seg-output-correct-bit-p (c)
  `(b* ((IE (nb-ash (+ *mw* *tw*) 1 ,c))
        ((mv E TS BL Lcarry Lmsb)
         (if (= IE 0)
             (vars-small-seg ,c)
             (vars-large-seg ,c))))
       (vars-correct-bit-p E TS BL Lcarry Lmsb)))


(def-gl-thm vars-seg-output-bit-correct
  :hyp   (compressionp c)
  :concl (vars-seg-output-correct-bit-p c)
  :g-bindings `((c ,(gl::g-int 0 1 28))))

;; -------------------------------------------------------
;; END - guard verification
;; -------------------------------------------------------


;; -------------------------------------------------------
;; encode compression
;; -------------------------------------------------------
;; {seq[top: n] + 1, zero'n} - seq[top:0]
(defun align-gap (seq n)
  (declare (xargs :guard (and (integerp seq) (natp n))))
  (1+ (logxor (nb-ash 0 n seq)
              (1- (expt 2 n)))))

;; compute E
(local (include-book "ihs/logops-lemmas" :dir :system))
(defthm e-helper-measure
    (implies (and (integerp len) (< 0 len))
             (natp (ash len -1)))
  :hints (("Goal" :use ((:instance ash-goes-to-0
                                   (size 1)
                                   (i len)
                                   (count -1)))
                  :in-theory (enable ash))))

(defun e-helper (len)
  (declare (xargs :guard (natp len)
                  :hints (("Subgoal 2" :use e-helper-measure))))
  (if (zp len)
      0
      (1+ (e-helper (ash len -1)))))

(defun e (len)
  (declare (xargs :guard (nbp len (1+ *xlen*))))
  (e-helper (nb-ash (1+ *tw*) (- *xlen* *tw*) len)))

(defun ie (E len)
  (declare (xargs :guard (and (natp E)
                              (<= E 52)
                              (nbp len (1+ *xlen*)))))
  (b* ((Lmsb (nb-ash *tw* 1 len)))
      (if (and (= E 0) (= Lmsb 0)) 0 1)))

(defmacro E+3-aligned-p (base len)
  `(b* ((E (e ,len)))
       (and (= (nb-ash 0 (+ E *eh*) ,base) 0)
            (= (nb-ash 0 (+ E *eh*) ,len) 0))))

;; if B[13:12] and T[13:12] are two bits away, and bsn <= tsh,
;; the carry-bit wouldn't be accounted for in decode-compression,
;; in which case we need to increment e
(defun carry? (overflow-flg top base e)
  (b* ((comp-bits (- *tw* *eh*))
       (t-2 (nb-ash (+ e *tw*) 2 top))
       (b-2 (nb-ash (+ e *tw*) 2 base))
       (bsh (nb-ash (+ e *eh*) comp-bits base))
       (tsh (nb-ash (+ e *eh*) comp-bits top)))
      ;; carry is t if following condition is met
      (and (not overflow-flg)
           (= (logxor t-2 b-2) 2)
           (<= bsh tsh))))

;; returns e, T[E+11:E+3], and B[E+13:E+3] when IE=1
(defun rounding (len base)
 (b* ((e (e len))
      (top (+ len base))
      (align (+ e *eh*))
      (gap (align-gap top align))
      ;; reset e and length if Lmsb changes
      ((mv n-e len)
       (if (< 0 (nb-ash 0 align top))
           (mv (e (+ len gap)) (+ len gap))
           (mv e len)))

      ;; if an overflow happens during to rounding up T, set flg to t
      (overflow-flg (not (equal e n-e)))
      ;; if not overflow, check if there is an unaccounted for carry situation
      (carry-flg (carry? overflow-flg (+ base len) base e))

      ;; update E, T and B if E needs to be incremented from either case
      (e (if (or carry-flg overflow-flg) (1+ e) e))
      (top (+ base len))
      (tsh (nb-ash (+ e *eh*) (- *tw* *eh*) top))
      (tsh (if (< 0 (nb-ash 0 (+ e *eh*) top))
               (nb-ash 0 (- *tw* *eh*) (1+ tsh))
               tsh))
      (blh (nb-ash (+ e *eh*) (- *mw* *eh*) base)))
     (mv e
         (logior (ash tsh *eh*) (nb-ash *eh* *eh* e))
         (logior (ash blh *eh*) (nb-ash 0 *eh* e)))))

(defun encode-compression (len base)
  (declare (xargs :guard (and (natp len)
                              (<= len (expt 2 *xlen*))
                              (nbp base *xlen*)
                              (<= (+ base len) (expt 2 *xlen*)))
                  :verify-guards nil))
  (b* ((e (e len))          ;; E = 52 - CountLeadingZeros(len[64:13])
       (ie (ie e len))      ;; IE = if (E = 0 and len[12] = 0) then 0 else 1
       (top (+ base len))
       ((mv & ts bl)        ;; binds ts and bl to T[11:0] and  B[13:0], respectively
        (if (= ie 0)
            (mv 0
                (nb-ash 0 *tw* top)     ;; T[2:0]
                (nb-ash 0 *mw* base))   ;; B[13:0]
            (rounding len base))))
      (logior (ash ie (+ *tw* *mw*))
              (ash ts *mw*) bl)))

;; ------------------------------------------------------
;; helper functions for properties hypothesis
;; ------------------------------------------------------
(defmacro valid-addr-p (addr base len)
  `(and (natp ,addr)
        (<= ,base ,addr)
        (< ,addr (+ ,base ,len))))

(defmacro valid-b-l-p (base len)
  `(and (natp ,len)
        (nbp ,base *xlen*)
        (<= (+ ,base ,len) (expt 2 *xlen*))))

;; ------------------------------------------------------------------------
;; properties of encode / decode functions
;; ------------------------------------------------------------------------
;; output for encode-compression is 27 bit,
;; broken into two cases for efficiency

;; len < 2^12
(def-gl-thm compressionp-encode-small-seg
    :hyp   (and (valid-b-l-p base len)
                (< len (expt 2 *TW*)))
    :concl (compressionp (encode-compression len base))
    :g-bindings `((base ,(gl::g-int 0 3 65))
                  (len ,(gl::g-int 1 3 66))))

;; len >= 2^12
(def-gl-param-thm compressionp-encode-large-seg
    :hyp   (and (valid-b-l-p base len)
                (<= (expt 2 *tw*) len))
    :concl (compressionp (encode-compression len base))
    :param-bindings
    `((((low 12) (high 16)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 16) (high 20)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 20) (high 24)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 24) (high 28)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 28) (high 32)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 32) (high 36)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 36) (high 40)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 40) (high 44)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 44) (high 48)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 48) (high 52)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 52) (high 56)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 56) (high 60)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 60) (high 64)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))
      (((low 64) (high 65)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65)))))
    :param-hyp (and (<= (expt 2 low) len) (< len (expt 2 high)))
    :cov-bindings (gl::auto-bindings (:mix (:nat base 65) (:nat len 65))))

;; Denote t', b' as the top and base returned from decoding after encoding,
;;    and t , b  as the original top and base

;; if IE = 0, or the base and len are aligned at index E+3, t' = t, b' = b
(def-gl-thm decode-encode-equal-small-seg
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (< len (expt 2 *TW*)))
    :concl (equal (decode-compression (encode-compression len base) addr)
                  (bounds (+ len base) base))
    :g-bindings `((base ,(gl::g-int 0 3 65))
                  (len ,(gl::g-int 1 3 66))
                  (addr ,(gl::g-int 2 3 65))))

(def-gl-thm decode-encode-equal-large-seg
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (<= (expt 2 *tw*) len)
                (E+3-aligned-p base len))
    :concl (equal (decode-compression (encode-compression len base) addr)
                  (bounds (+ len base) base))
    :g-bindings `((base ,(gl::g-int 0 3 65))
                  (len ,(gl::g-int 1 3 66))
                  (addr ,(gl::g-int 2 3 65))))

;; if IE = 1, b' <= b
(def-gl-param-thm decode-encode-b-bound-len>2^12
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (<= (expt 2 *tw*) len))
    :concl (<= (bounds->base (decode-compression (encode-compression len base) addr))
               base)
    :param-bindings
    `((((low 12) (high 16)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 16) (high 20)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 20) (high 24)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 24) (high 28)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 28) (high 32)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 32) (high 36)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 36) (high 40)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 40) (high 44)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 44) (high 48)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 48) (high 52)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 52) (high 56)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 56) (high 60)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 60) (high 64)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 64) (high 65)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65)))))
    :param-hyp (and (<= (expt 2 low) len) (< len (expt 2 high)))
    :cov-bindings (gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))

;; if IE = 1, t <= t'
(def-gl-param-thm decode-encode-t-bound-len>2^12
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (<= (expt 2 *tw*) len)
                (< len (expt 2 60)))
    :concl (<= (+ base len)
               (bounds->top (decode-compression (encode-compression len base) addr)))
    :param-bindings
    `((((low 12) (high 16)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 16) (high 20)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 20) (high 24)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 24) (high 28)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 28) (high 32)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 32) (high 36)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 36) (high 40)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 40) (high 44)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 44) (high 48)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 48) (high 52)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 52) (high 56)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 56) (high 60)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 60) (high 64)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 64) (high 65)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65)))))
    :param-hyp (and (<= (expt 2 low) len) (< len (expt 2 high)))
    :cov-bindings (gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))

;; helper macro for proving the following properties
(defmacro E+3-expt (base len)
  `(b* ((e (mv-nth 0 (rounding ,len ,base))))
       (expt 2 (+ 3 e))))

;; if IE = 1, b - b' < 2^(E + 3)
(def-gl-param-thm decode-encode-b-gap
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (<= (expt 2 *tw*) len))
    :concl (< (- base
                 (bounds->base (decode-compression (encode-compression len base) addr)))
              (E+3-expt base len))
    :param-bindings
    `((((low 12) (high 16)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 16) (high 20)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 20) (high 24)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 24) (high 28)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 28) (high 32)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 32) (high 36)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 36) (high 40)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 40) (high 44)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 44) (high 48)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 48) (high 52)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 52) (high 56)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 56) (high 60)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 60) (high 64)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 64) (high 65)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65)))))
    :param-hyp (and (<= (expt 2 low) len) (< len (expt 2 high)))
    :cov-bindings (gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))

;; if IE = 1, t' - t < 2^(E + 3)
(def-gl-param-thm decode-encode-t-gap
    :hyp   (and (valid-addr-p addr base len)
                (valid-b-l-p base len)
                (<= (expt 2 *tw*) len))
    :concl (< (+ (- (+ base len))
                 (bounds->top (decode-compression (encode-compression len base) addr)))
              (E+3-expt base len))
    :param-bindings
    `((((low 12) (high 16)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 16) (high 20)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 20) (high 24)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 24) (high 28)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 28) (high 32)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 32) (high 36)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 36) (high 40)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 40) (high 44)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 44) (high 48)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 48) (high 52)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 52) (high 56)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 56) (high 60)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 60) (high 64)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))
      (((low 64) (high 65)) ,(gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65)))))
    :param-hyp (and (<= (expt 2 low) len) (< len (expt 2 high)))
    :cov-bindings (gl::auto-bindings (:mix (:nat base 65) (:nat len 65) (:nat addr 65))))


;; CHERI Concentrate Compression permissions
;; const: otype width, compression width, perms width
(defconst *otlen* 18)
(defconst *cmplen* 27)
(defconst *plen* 16)

;; Architectural capability permission bits
(std::defaggregate acperm
    ((gb  (nbp gb 1))    ;; GLOBAL - Allow cap to be stored via caps that do
                         ;; not themselves have PERMIT_STORE_LOCAL_CAPABILITY set
     (x   (nbp x 1))     ;; PERMIT_EXECUTE - Allow cap to be used in PCC register as cap
                         ;; for program counter, constraining control flow
     (l   (nbp l 1))     ;; PERMIT_LOAD - Allow cap to be used to load untagged data;
                         ;; requires PERMIT_LOAD_CAPABILITY to load tagged value
     (s   (nbp s 1))     ;; PERMIT_STORE - Allow cap to be used to store untagged data;
                         ;; requires PERMIT_STORE_CAPABILITY to store tagged value
     (lc  (nbp lc 1))    ;; PERMIT_LOAD_CAPABILITY - Allow cap to load caps with valid
                         ;; tags; requires PERMIT_LOAD
     (sc  (nbp sc 1))    ;; PERMIT_STORE_CAPABILITY - Allow cap to store caps with valid
                         ;; tags; requires PERMIT_STORE
     (slc (nbp slc 1))   ;; PERMIT_STORE_LOCAL_CAPABILITY - Allow cap to store non-global
                         ;; caps; requires PERMIT_STORE and PERMIT_STORE_CAPABILITY
     (sl  (nbp sl 1))    ;; PERMIT_SEAL - Allow cap to seal another cap with otype equal to
                         ;; this cap's base + offset
     (ci  (nbp ci 1))    ;; PERMIT_CINVOKE - Allow this sealed cap to be used with CInvoke instruction
     (usl (nbp usl 1))   ;; PERMIT_UNSEAL - Allow cap to unseal another cap with otype
                         ;; equal to this cap's base + offset
     (cid (nbp cid 1)))) ;; PERMIT_SET_CID - Allow architectural compartment ID to be set
                         ;; to this cap's base + offset using CSetCID instruction

;; CHERI Concentrate capability permission bits
(std::defaggregate ccperm
    ((gb  (nbp gb 1))    ;; GLOBAL - Allow cap to be stored via caps that do
                         ;; not themselves have PERMIT_STORE_LOCAL_CAPABILITY set
     (x   (nbp x 1))     ;; PERMIT_EXECUTE - Allow cap to be used in PCC register as cap
                         ;; for program counter, constraining control flow
     (l   (nbp l 1))     ;; PERMIT_LOAD - Allow cap to be used to load untagged data;
                         ;; requires PERMIT_LOAD_CAPABILITY to load tagged value
     (s   (nbp s 1))     ;; PERMIT_STORE - Allow cap to be used to store untagged data;
                         ;; requires PERMIT_STORE_CAPABILITY to store tagged value
     (lc  (nbp lc 1))    ;; PERMIT_LOAD_CAPABILITY - Allow cap to load caps with valid
                         ;; tags; requires PERMIT_LOAD
     (sc  (nbp sc 1))    ;; PERMIT_STORE_CAPABILITY - Allow cap to store caps with valid
                         ;; tags; requires PERMIT_STORE
     (slc (nbp slc 1))   ;; PERMIT_STORE_LOCAL_CAPABILITY - Allow cap to store non-global
                         ;; caps; requires PERMIT_STORE and PERMIT_STORE_CAPABILITY
     (sl  (nbp sl 1))    ;; PERMIT_SEAL - Allow cap to seal another cap with otype equal to
                         ;; this cap's base + offset
     (ci  (nbp ci 1))    ;; PERMIT_CINVOKE - Allow this sealed cap to be used with CInvoke instruction
     (usl (nbp usl 1))   ;; PERMIT_UNSEAL - Allow cap to unseal another cap with otype
                         ;; equal to this cap's base + offset
     (cid (nbp cid 1))   ;; PERMIT_SET_CID - Allow architectural compartment ID to be set
                         ;; to this cap's base + offset using CSetCID instruction
     (asr (nbp asr 1))   ;; ACCESS_SYSTEM_REGISTERS - Allow access to privileged
                         ;; processor permitted by the architecture (e.g., by virtue
                         ;; of being in supervisor mode), with architecture-specific implications.
     (up0 (nbp up0 1))   ;; UPERMS bit 0 - software-defined permission bit
     (up1 (nbp up1 1))   ;; UPERMS bit 1
     (up2 (nbp up3 1))   ;; UPERMS bit 2
     (up3 (nbp up3 1)))) ;; UPERMS bit 3

(std::defaggregate ccap
    ((perms ccperm-p)
     (otype (nbp otype *otlen*))
     (bound (nbp bound *cmplen*))))

(define perms-bits-to-ccperm ((perms (nbp perms *plen*)))
  :verify-guards nil
  (b* ((gb  (nb-ash 15 1 perms))
       (x   (nb-ash 14 1 perms))
       (l   (nb-ash 13 1 perms))
       (s   (nb-ash 12 1 perms))
       (lc  (nb-ash 11 1 perms))
       (sc  (nb-ash 10 1 perms))
       (slc (nb-ash 9 1 perms))
       (sl  (nb-ash 8 1 perms))
       (ci  (nb-ash 7 1 perms))
       (usl (nb-ash 6 1 perms))
       (cid (nb-ash 5 1 perms))
       (asr (nb-ash 4 1 perms))
       (up0 (nb-ash 3 1 perms))
       (up1 (nb-ash 2 1 perms))
       (up2 (nb-ash 1 1 perms))
       (up3 (nb-ash 0 1 perms)))
      (ccperm gb x l s lc sc slc sl ci usl cid asr up0 up1 up2 up3)))

(def-gl-thm perms-bits-to-ccperm-guard
    :hyp   (and (nbp perms *plen*)
                (natp shift)
                (< shift *plen*))
    :concl (nbp (nb-ash shift 1 perms) 1)
    :g-bindings `((perms ,(gl::g-int 0 1 (1+ *plen*)))
                  (shift ,(gl::g-int (1+ *plen*) 1 5))))

(verify-guards perms-bits-to-ccperm
               :hints (("Goal" :in-theory (disable logand-with-mask)
                               :use
                               ((:instance perms-bits-to-ccperm-guard (shift 1))
                                (:instance perms-bits-to-ccperm-guard (shift 2))
                                (:instance perms-bits-to-ccperm-guard (shift 3))
                                (:instance perms-bits-to-ccperm-guard (shift 4))
                                (:instance perms-bits-to-ccperm-guard (shift 5))
                                (:instance perms-bits-to-ccperm-guard (shift 6))
                                (:instance perms-bits-to-ccperm-guard (shift 7))
                                (:instance perms-bits-to-ccperm-guard (shift 8))
                                (:instance perms-bits-to-ccperm-guard (shift 9))
                                (:instance perms-bits-to-ccperm-guard (shift 10))
                                (:instance perms-bits-to-ccperm-guard (shift 11))
                                (:instance perms-bits-to-ccperm-guard (shift 12))
                                (:instance perms-bits-to-ccperm-guard (shift 13))
                                (:instance perms-bits-to-ccperm-guard (shift 14))
                                (:instance perms-bits-to-ccperm-guard (shift 15))))))

;;--------------------------------------------------------------------
;; acap from mcap conversion
;;--------------------------------------------------------------------

;; definition of architectual and memory capabilities
(std::defaggregate acap
    ((tag    (nbp tag 1))
     (perms  (nbp perms *plen*))
     (ot     (nbp ot *xlen*))
     (offset (nbp offset *xlen*))
     (base   (nbp base *xlen*))                            ;; base + offset --> pointer addr
     (len    (and (natp len) (<= len (expt 2 *xlen*)))))   ;; base + len    --> upper bound
  )

(defun mcapp (mcap)
  (declare (xargs :guard t))
  (and (nbp mcap *clen*)
       (compressionp (nb-ash *xlen* *cmplen* mcap))))

;; mcap to acap when mcap = 0
(define null-mcap-to-acap ()
  (b* ((perms 0)
       (tag 0)
       (ot (1- (expt 2 *xlen*)))
       (offset 0)
       (base 0)
       (len (expt 2 *xlen*)))
    (acap tag perms ot offset base len)))

;; Non-zero mcap to acap
(define mcap-to-acap-non-null ((mcap (and (mcapp mcap)
                                          (not (zp mcap)))))
  :verify-guards nil
  (b* ((perms (nb-ash (- *clen* *plen*) *plen* mcap))
       (tag (nb-ash (+ *otlen* *cmplen* *xlen*) 1 mcap))
       (ot (nb-ash (+ *cmplen* *xlen*) *otlen* mcap))
       (cmp (nb-ash *xlen* *cmplen* mcap))
       (addr (nb-ash 0 *xlen* mcap))
       (bounds (decode-compression cmp addr))
       (base (bounds->base bounds))
       (top (bounds->top bounds))
       (offset (- addr base))
       (len (- top base)))
      (acap tag perms ot offset base len)))

;; mcap to acap
(define mcap-to-acap ((mcap (nbp mcap *clen*)))
  :verify-guards nil
  (if (zp mcap)
      (null-mcap-to-acap)
      (mcap-to-acap-non-null mcap)))

;; check if acap should be converted to null mcap
(define null-acap-p ((acap (acap-p acap)))
  (equal (null-mcap-to-acap) acap))

;; architectual otype to memory otype:
;; actual implementation details to be filled
(define aot-to-mot ((aot (nbp aot *xlen*)))
  (nb-ash 0 *otlen* aot))

(define acap-to-mcap ((acap (acap-p acap)))
  :verify-guards nil
  (if (null-acap-p acap)
      0
      (b* ((mbounds (encode-compression (acap->len acap)
                                        (acap->base acap)))
           (mot (aot-to-mot (acap->ot acap))))
          (logior (ash (acap->perms acap) (- *clen* *plen*))
                  (ash (acap->tag acap)
                       (+ *otlen* *cmplen* *xlen*))
                  (ash mot (+ *cmplen* *xlen*))
                  (ash mbounds *xlen*)
                  (+ (acap->base acap) (acap->offset acap))))))

;; proofs that converting acap twices gives back the same input
(def-gl-thm amcap-conversion-eq-small-seg
    :hyp   (and (valid-b-l-p base len)
                (nbp tag 1)
                (nbp perms *plen*)
                (nbp ot *otlen*)
                (nbp offset *xlen*)
                (< len (expt 2 *TW*))
                (< offset len))
    :concl (equal (mcap-to-acap (acap-to-mcap (acap tag perms ot offset base len)))
                  (acap tag perms ot offset base len))
    :g-bindings `((tag ,(gl::g-int 0 1 2))
                  (perms ,(gl::g-int 2 1 (1+ *plen*)))
                  (ot ,(gl::g-int 19 4 65))
                  (offset ,(gl::g-int 20 4 65))
                  (base ,(gl::g-int 21 4 65))
                  (len ,(gl::g-int 22 4 66))))

(def-gl-thm amcap-conversion-eq-large-seg
    :hyp   (and (valid-b-l-p base len)
                (E+3-aligned-p base len)
                (nbp tag 1)
                (nbp perms *plen*)
                (nbp ot *otlen*)
                (nbp offset *xlen*)
                (<= (expt 2 *TW*) len)
                (< offset len))
    :concl (equal (mcap-to-acap (acap-to-mcap (acap tag perms ot offset base len)))
                  (acap tag perms ot offset base len))
    :g-bindings `((tag ,(gl::g-int 0 1 2))
                  (perms ,(gl::g-int 2 1 (1+ *plen*)))
                  (ot ,(gl::g-int 19 4 65))
                  (offset ,(gl::g-int 20 4 65))
                  (base ,(gl::g-int 21 4 65))
                  (len ,(gl::g-int 22 4 66))))

;; ---------------------------------------------------------------------------
;; END of Cheri compression encode/decode + architectural/memory capabilities
;; ---------------------------------------------------------------------------
