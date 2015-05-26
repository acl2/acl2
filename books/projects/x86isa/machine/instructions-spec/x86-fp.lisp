;; AUTHOR:
;; Cuong Chau <ckcuong@cs.utexas.edu>

;; All events beginning with the prefix ACL2:: in this book (except
;; ACL2::with-supporters) are imported from the RTL9 library under the
;; directory "books/rtl/rel9/lib", authored by David
;; M. Russinoff (david@russinoff.com).

(in-package "X86ISA")

(include-book "../x86-decoding-and-spec-utils")

(include-book "tools/with-supporters" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable logbitp)))

;; ======================================================================

;; Generic floating-point arithmetic utils:

(defun set-flag (index flags)
  (declare (xargs :guard (and (natp index) (natp flags))))
  (logior flags (ash 1 index)))

(defthm natp-set-flag
  (implies (natp flags)
           (natp (set-flag index flags)))
  :rule-classes :type-prescription)

(defthm-usb n32p-set-flag
  :hyp (and (natp index)
            (< index 32)
            (n32p flags))
  :bound 32
  :concl (set-flag index flags)
  :gen-linear t)

(in-theory (disable set-flag))

(defmacro rc-cases (&key rn rd ru rz other)
  `(case RC
     (,*RC-RN* ,rn)
     (,*RC-RD* ,rd)
     (,*RC-RU* ,ru)
     (,*RC-RZ* ,rz)
     (otherwise ,other)))

(defmacro fp-max-exp         ()  `(1- (ash 1 exp-width)))
(defmacro fp-inf-exp         ()  `(fp-max-exp))
(defmacro fp-max-finite-exp  ()  `(- (ash 1 exp-width) 2))
(defmacro fp-inf-frac        ()   0)
(defmacro fp-max-frac        ()  `(1- (ash 1 frac-width)))

(defun fp-round-overflow-generic (RC sign exp-width frac-width)
  (declare (xargs :guard (and (integerp RC)
                              (integerp sign)
                              (posp exp-width)
                              (posp frac-width))))
  "Returns rounded sign, exponent, and fraction in case of overflow."
  (RC-cases
   :rn  (mv sign (fp-inf-exp) (fp-inf-frac))
   :rd  (if (eql 0 sign)
            (mv sign (fp-max-finite-exp) (fp-max-frac))
          (mv sign (fp-inf-exp) (fp-inf-frac)))
   :ru  (if (eql 0 sign)
            (mv sign (fp-inf-exp) (fp-inf-frac))
          (mv sign (fp-max-finite-exp) (fp-max-frac)))
   :rz  (mv sign (fp-max-finite-exp) (fp-max-frac))
   ;; Should never get here.
   :other (mv       0               0               0)))

(defthm integerp-fp-round-overflow-generic-0
  (implies (integerp sign)
           (integerp (mv-nth 0 (fp-round-overflow-generic rc sign exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm integerp-fp-round-overflow-generic-1
  (integerp (mv-nth 1 (fp-round-overflow-generic rc sign exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm integerp-fp-round-overflow-generic-2
  (integerp (mv-nth 2 (fp-round-overflow-generic rc sign exp-width frac-width)))
  :rule-classes :type-prescription)

(in-theory (disable fp-round-overflow-generic))

;; ======================================================================

;; SSE arithmetic utils:

(defun fp-encode-integer (sign exp frac exp-width frac-width)
  (declare (xargs :guard (and (integerp sign)
                              (integerp exp)
                              (integerp frac)
                              (posp exp-width)
                              (posp frac-width))))
  (logior frac (logior (ash exp frac-width)
                       (ash sign (+ exp-width frac-width)))))

(defthm integerp-fp-encode-integer
  (integerp (fp-encode-integer sign exp frac
                               exp-width frac-width))
  :hints (("Goal" :in-theory '(fp-encode-integer
                               (:type-prescription binary-logior))))
  :rule-classes :type-prescription)

(in-theory (disable fp-encode-integer))

;; Returns:
;; One of the symbols INDEF, QNAN, SNAN, INF, ZERO, DENORMAL, or NORMAL.
;; sign bit
;; exponent bits
;; implicit bit value
;; fraction bits.
(defun fp-decode (x exp-width frac-width)
  (declare (xargs :guard (and (integerp x)
                              (posp exp-width)
                              (posp frac-width))))
  (b* ((sign-bit-index (+ frac-width exp-width))
       (frac (part-select x :low 0 :width frac-width))
       (exp  (part-select x :low frac-width :width exp-width))
       (sign (part-select x :low sign-bit-index :width 1)))
      (cond ((eql exp 0)
             ;; Denormal or zero
             (b* ((sym (if (not (eql frac 0)) 'denormal 'zero)))
                 (mv sym sign exp 0 frac)))
            ((eql exp (1- (ash 1 exp-width)))
             ;; Infinity or NAN
             (if (eql frac 0)
                 ;; infinity
                 (mv 'inf sign exp 1 frac)
               ;; nan
               (let ((sym (if (logbitp (1- frac-width) frac)
                              ;; qnan
                              (if (and (eql sign 1)
                                       (eql frac (ash 1 (1- frac-width))))
                                  'indef
                                'qnan)
                            'snan)))
                 (mv sym sign exp 1 frac))))
            (t (mv 'normal sign exp 1 frac)))))

(defthm-usb fp-decode-lemma-1
  :bound 1
  :concl (mv-nth 1 (fp-decode x exp-width frac-width))
  :gen-type t
  :gen-linear t)

(defthm fp-decode-lemma-2-1
  (implies (posp exp-width)
           (natp (mv-nth 2 (fp-decode x exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm-usb fp-decode-lemma-2-2
  :hyp (posp exp-width)
  :bound exp-width
  :concl (mv-nth 2 (fp-decode x exp-width frac-width))
  :gen-linear t)

(defthm-usb fp-decode-lemma-3
  :bound 1
  :concl (mv-nth 3 (fp-decode x exp-width frac-width))
  :gen-type t
  :gen-linear t)

(defthm fp-decode-lemma-4-1
  (implies (posp frac-width)
           (natp (mv-nth 4 (fp-decode x exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm-usb fp-decode-lemma-4-2
  :hyp (posp frac-width)
  :bound frac-width
  :concl (mv-nth 4 (fp-decode x exp-width frac-width))
  :gen-type t
  :gen-linear t)

(in-theory (disable fp-decode))

;; Shilpi: Here, I stopped converting stuff to use
;; defthm-usb/defthm-sb.  Maybe I'll convert the rest later on.

(defn sse-daz (kind exp frac daz)
  (if (and daz (eq kind 'denormal))
      (mv 'zero 0 0)
    (mv kind exp frac)))

(defthm integerp-sse-daz-1
  (implies (integerp exp)
           (integerp (mv-nth 1 (sse-daz kind exp frac daz))))
  :rule-classes :type-prescription)

(defthm integerp-sse-daz-2
  (implies (integerp frac)
           (integerp (mv-nth 2 (sse-daz kind exp frac daz))))
  :rule-classes :type-prescription)

(in-theory (disable sse-daz))

(defn denormal-exception (kind1 kind2)
  (and (not (member kind1 '(snan qnan indef)))
       (not (member kind2 '(snan qnan indef)))
       (or (eq kind1 'denormal) (eq kind2 'denormal))))

(in-theory (disable denormal-exception))

(defun fp-to-rat (sign exp frac bias exp-width frac-width)
  ;; Convert the bit-vector or integer representation used by hardware
  ;; to rational for the cases of zero, denormal, and normal.
  (declare (xargs :guard (and (integerp sign) (integerp exp) (integerp frac)
                              (natp bias) (posp exp-width) (posp frac-width))))
  (cond
   ((and (eql exp 0) (eql frac 0))
    0)
   ;; Denormal case
   ((and (eql exp 0) (not (eql frac 0)))
    (let ((man (* frac
                  (expt 2 (- frac-width)))))
      (* (if (eql sign 0) 1 -1)
         man
         (expt 2 (- 1 bias)))))
   ;; Normal case
   ((and (< 0 exp)
         (<= exp (fp-max-finite-exp)))
    (let ((man (* (logior (ash 1 frac-width) frac)
                  (expt 2 (- frac-width)))))
      (* (if (eql sign 0) 1 -1)
         man
         (expt 2 (- exp bias)))))
   ;; Should never get here.
   (t 0)))

(defthm rationalp-fp-to-rat
  (implies (integerp frac)
           (rationalp (fp-to-rat sign exp frac bias exp-width frac-width)))
  :rule-classes :type-prescription)

(in-theory (disable fp-to-rat))

(ACL2::with-supporters
 (local
  (include-book "rtl/rel9/lib/reps" :dir :system))

 :names (ACL2::FORMAL-+ ACL2::CAT-SIZE ACL2::CAT)

 (defun rat-to-fp (rat sign overflow underflow flush rc
                       exp-width frac-width)
   ;; Convert the rational to bit-vector or integer representation
   ;; used by hardware.
   ;; Return (mv sign exp frac)
   (declare (xargs :guard (and (rationalp rat)
                               (integerp sign)
                               (booleanp overflow)
                               (booleanp underflow)
                               (booleanp flush)
                               (integerp rc)
                               (posp exp-width)
                               (posp frac-width))))
   (cond
    ((eql rat 0)
     (fp-encode-integer sign 0 0 exp-width frac-width))
    (overflow
     (b* (((mv sign exp frac)
           (fp-round-overflow-generic rc sign exp-width frac-width)))
         (fp-encode-integer sign exp frac exp-width frac-width)))
    (flush
     (fp-encode-integer sign 0 0 exp-width frac-width))
    (underflow
     (if (ec-call (ACL2::drepp rat (1+ frac-width) exp-width))
         ;; Denormal representable
         (ec-call (ACL2::dencode rat
                                 (1+ frac-width)
                                 exp-width))
       ;; Not denormal representable, should never happen.
       (fp-encode-integer sign 0 0 exp-width frac-width)))
    ;; Denormal number
    ((ec-call (ACL2::drepp rat (1+ frac-width) exp-width))
     (ec-call (ACL2::dencode rat
                             (1+ frac-width)
                             exp-width)))
    ;; Normal number
    ((ec-call (ACL2::nrepp rat (1+ frac-width) exp-width))
     (ec-call (ACL2::nencode rat
                             (1+ frac-width)
                             exp-width)))
    ;; Should never get here.
    (t 0))))

(defthm integerp-rat-to-fp
  (integerp (rat-to-fp rat sign overflow underflow flush rc
                       exp-width frac-width))
  :rule-classes :type-prescription)

(in-theory (disable rat-to-fp))

(ACL2::with-supporters
 (local
  (include-book "rtl/rel9/lib/round" :dir :system))

 (defun normal-rat-round (x rc frac-width)
   (declare (xargs :guard (and (rationalp x)
                               (integerp rc)
                               (posp frac-width))))
   (rc-cases
    :rn (ec-call (ACL2::near x (1+ frac-width)))
    :rd (ec-call (ACL2::minf x (1+ frac-width)))
    :ru (ec-call (ACL2::inf x (1+ frac-width)))
    :rz (ACL2::trunc x (1+ frac-width))
    ;; Should never get here.
    :other x))

 (defun denormal-rat-round (x rc exp-width frac-width)
   (declare (xargs :guard (and (rationalp x)
                               (integerp rc)
                               (posp exp-width)
                               (posp frac-width))))
   (rc-cases
    :rn (ec-call (ACL2::drnd x 'ACL2::near (1+ frac-width) exp-width))
    :rd (ec-call (ACL2::drnd x 'ACL2::minf (1+ frac-width) exp-width))
    :ru (ec-call (ACL2::drnd x 'ACL2::inf (1+ frac-width) exp-width))
    :rz (ec-call (ACL2::drnd x 'ACL2::trunc (1+ frac-width) exp-width))
    ;; Should never get here.
    :other x))

 (defun rat-round (x rc bias exp-width frac-width)
   (declare (xargs :guard (and (rationalp x)
                               (integerp rc)
                               (natp bias)
                               (posp exp-width)
                               (posp frac-width))))
   (if (> (ACL2::expo x) (- bias))
       (normal-rat-round x rc frac-width)
     (denormal-rat-round x rc exp-width frac-width))))

(defthm rationalp-rat-round
  (implies (rationalp x)
           (rationalp (rat-round x rc bias exp-width frac-width)))
  :rule-classes :type-prescription)

(in-theory (disable normal-rat-round denormal-rat-round rat-round))

(defun underflowp (rat rounded-expo bias)
  (declare (xargs :guard (and (rationalp rat)
                              (integerp rounded-expo)
                              (natp bias))))
  (let ((expo (ACL2::expo rat))
        (minus-bias (- bias)))
    (or (<= rounded-expo minus-bias)
        (and (= rounded-expo 0)
             (<= expo minus-bias)))))

(defthm booleanp-underflowp
  (booleanp (underflowp rat rounded-expo bias)))

(in-theory (disable underflowp))

(defn make-special-bp (kind nan-frac-bits sign exp-width frac-width)
  ;; Return (mv sign exp implicit frac)
  (declare (xargs :guard (and (integerp nan-frac-bits)
                              (integerp sign)
                              (posp exp-width) (posp frac-width))))
  (case kind
    (indef     (mv 1 (1- (ash 1 exp-width)) 1 (ash 1 (1- frac-width))))
    (qnan      (mv sign (1- (ash 1 exp-width)) 1
                   (+ (ash 1 (1- frac-width))
                      nan-frac-bits)))
    (snan      (mv sign (1- (ash 1 exp-width)) 1
                   nan-frac-bits))
    (inf       (mv sign (1- (ash 1 exp-width)) 1 0))
    (zero      (mv sign 0                     0 0))
    ;; These two aren't particularly useful -- they're just arbitrary examples
    ;; of denormal and normal, resp.
    (denormal  (mv 0 0                          0 1))
    (otherwise (mv 0 1                          1 0))))

(defthm integerp-make-special-bp-0
  (implies (integerp sign)
           (integerp (mv-nth 0 (make-special-bp kind nan-frac-bits sign
                                                exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm integerp-make-special-bp-1
  (integerp (mv-nth 1 (make-special-bp kind nan-frac-bits sign
                                       exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm integerp-make-special-bp-2
  (integerp (mv-nth 2 (make-special-bp kind nan-frac-bits sign
                                       exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm integerp-make-special-bp-3
  (implies (integerp nan-frac-bits)
           (integerp (mv-nth 3 (make-special-bp kind nan-frac-bits sign
                                                exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable make-special-bp))

(defmacro flag-make-special-bp (kind nan-frac-bits sign invalid)
  `(mv-let (sign exp explicit frac)
     (make-special-bp ,kind ,nan-frac-bits ,sign exp-width frac-width)
    (mv t sign exp explicit frac ,invalid)))

;; If the addition, subtraction, multiplication, or division yields a
;; "non-arithmetic" result, i.e. a special, this function finds it.
;; Returns an mv:
;; ok -- t if this result is correct; if nil, must do the real math.
;; sign, exp, implicit, frac -- answer components if valid
;; invalid -- this was an invalid operation.
(defun sse-add/sub/mul/div-special (kind1 sign1 exp1 implicit1 frac1
                                          kind2 sign2 exp2 implicit2 frac2
                                          rc exp-width frac-width
                                          operation)
  ;; Shilpi: Remove nfix --- probably when the guards become stricter.
  (declare (xargs :guard (and (integerp sign1) (integerp exp1)
                              (integerp implicit1) (integerp frac1)
                              (integerp sign2) (integerp exp2)
                              (integerp implicit2) (integerp frac2)
                              (integerp rc)
                              (posp exp-width) (posp frac-width)
                              (integerp operation)))
           (type (integer 0 36) operation))
  (let ((invalid (or (eq kind1 'snan) (eq kind2 'snan)))
        (is-add (int= operation #.*OP-ADD*))
        (is-sub (int= operation #.*OP-SUB*))
        (is-mul (int= operation #.*OP-MUL*))
        (is-div (int= operation #.*OP-DIV*)))
    (cond
     ((or (eq kind1 'qnan) (eq kind1 'indef))
      (mv t sign1 exp1 implicit1 frac1 invalid))
     ((eq kind1 'snan)
      (flag-make-special-bp 'qnan
                            (part-select frac1 :low 0 :high (nfix (- frac-width 2)))
                            ;; (get-bits 0 (- frac-width 2) frac1)
                            sign1 invalid))
     ((or (eq kind2 'qnan) (eq kind2 'indef))
      (mv t sign2 exp2 implicit2 frac2 invalid))
     ((eq kind2 'snan)
      (flag-make-special-bp 'qnan
                            (part-select frac2 :low 0 :high (nfix (- frac-width 2)))
                            ;; (get-bits 0 (- frac-width 2) frac2)
                            sign2 invalid))
     ((eq kind1 'inf)
      (if (or (and (eq kind2 'inf)
                   (or (and (not (eql sign1 sign2)) is-add)
                       (and (eql sign1 sign2) is-sub)
                       is-div))
              (and (eq kind2 'zero)
                   is-mul))
          ;; indef
          (flag-make-special-bp 'indef 0 1 t)
        (let ((sign (if (or is-mul is-div)
                        (logxor sign1 sign2)
                      sign1)))
          (mv t sign exp1 implicit1 frac1 invalid))))
     ((eq kind2 'inf)
      (if (and (eq kind1 'zero) is-mul)
          ;; indef
          (flag-make-special-bp 'indef 0 1 t)
        (let ((sign (if is-sub
                        (logxor sign2 1)
                      (if (or is-mul is-div)
                          (logxor sign1 sign2)
                        sign2))))
          (if is-div
              (mv t sign 0 0 0 invalid)
            (mv t sign exp2 implicit2 frac2 invalid)))))
     ;; This is probably dependent on the rounding mode:
     ((and (eq kind1 'zero) (eq kind2 'zero))
      (if is-div
          ;; indef
          (flag-make-special-bp 'indef 0 1 t)
        (let ((sign (if (or (and (eql sign1 sign2) is-add)
                            (and (not (eql sign1 sign2)) is-sub))
                        sign1
                      (if is-mul
                          (logxor sign1 sign2)
                        (if (int= rc #.*rc-rd*) 1 0)))))
          (flag-make-special-bp 'zero 0 sign invalid))))
     ;; Divide-by-zero exception
     ((and (eq kind2 'zero) is-div)
      (flag-make-special-bp 'inf 0 (logxor sign1 sign2) invalid))
     (t (mv nil 0 0 0 0 invalid)))))

(defthm integerp-sse-add/sub/mul/div-special-1
  (implies (and (integerp sign1) (integerp sign2))
           (integerp (mv-nth 1 (sse-add/sub/mul/div-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                rc exp-width frac-width operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-add/sub/mul/div-special-2
  (implies (and (integerp exp1) (integerp exp2))
           (integerp (mv-nth 2 (sse-add/sub/mul/div-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                rc exp-width frac-width operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-add/sub/mul/div-special-3
  (implies (and (integerp implicit1) (integerp implicit2))
           (integerp (mv-nth 3 (sse-add/sub/mul/div-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                rc exp-width frac-width operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-add/sub/mul/div-special-4
  (implies (and (integerp frac1) (integerp frac2))
           (integerp (mv-nth 4 (sse-add/sub/mul/div-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                rc exp-width frac-width operation))))
  :rule-classes :type-prescription)

(in-theory (disable sse-add/sub/mul/div-special))

(local
  (defthm natp-bias
    (implies (posp q)
             (natp (ACL2::bias q)))
    :hints (("Goal" :in-theory (enable ACL2::bias)))
    :rule-classes :type-prescription))

(defun-inline sse-add/sub/mul/div-sign (rat sign1 sign2 operation rc)
  (declare (xargs :guard (and (rationalp rat)
                              (integerp sign1)
                              (integerp sign2)
                              (integerp operation)
                              (integerp rc))))
  (cond ((> rat 0) 0)
        ((< rat 0) 1)
        (t (cond ((or (int= operation #.*OP-ADD*)
                      (int= operation #.*OP-SUB*))
                  (if (int= rc #.*rc-rd*) 1 0))
                 ((or (int= operation #.*OP-MUL*)
                      (int= operation #.*OP-DIV*))
                  (logxor sign1 sign2))
                 ;; Unimplemented operations.
                 (t 0)))))

(defthm integerp-sse-add/sub/mul/div-sign
  (implies (forced-and (integerp sign1)
                       (integerp sign2))
           (integerp (sse-add/sub/mul/div-sign rat sign1 sign2 operation rc)))
  :rule-classes :type-prescription)

(in-theory (disable sse-add/sub/mul/div-sign))

(defun sse-add/sub/mul/div (operation op1 op2 mxcsr exp-width frac-width)
  (declare (xargs :guard (and (integerp operation)
                              (integerp op1) (integerp op2) (natp mxcsr)
                              (posp exp-width) (posp frac-width)))
           (type (integer 0 36) operation))
  (b* (((mv kind1 sign1 exp1 implicit1 frac1)
        (fp-decode op1 exp-width frac-width))
       ((mv kind2 sign2 exp2 implicit2 frac2)
        (fp-decode op2 exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind1 exp1 frac1)
        (sse-daz kind1 exp1 frac1 daz))
       ((mv kind2 exp2 frac2)
        (sse-daz kind2 exp2 frac2 daz))
       (rc (mbe :logic (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
       ((mv special-ok sign exp & frac invalid)
        (sse-add/sub/mul/div-special kind1 sign1 exp1 implicit1 frac1
                                     kind2 sign2 exp2 implicit2 frac2
                                     rc exp-width frac-width operation))

       ;; Check invalid operation
       (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check divide-by-zero
       (ze (and (int= operation #.*OP-DIV*)
                (or (eq kind1 'normal)
                    (eq kind1 'denormal))
                (eq kind2 'zero)))
       (mxcsr (if ze (set-flag #.*mxcsr-ze* mxcsr) mxcsr))
       (zm (logbitp #.*mxcsr-zm* mxcsr))
       ((when (and ze (not zm)))
        (mv 'divide-by-zero-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (and (denormal-exception kind1 kind2)
                (not ze)))
       (mxcsr (if de (set-flag #.*mxcsr-de* mxcsr) mxcsr))
       (dm (logbitp #.*mxcsr-dm* mxcsr))
       ((when (and de (not dm)))
        (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

      (if special-ok
          (mv nil
              (fp-encode-integer sign exp frac exp-width frac-width)
              mxcsr)
        (b* ((bias (ec-call (ACL2::bias exp-width)))
             (rat1 (fp-to-rat sign1 exp1 frac1 bias exp-width frac-width))
             (rat2 (fp-to-rat sign2 exp2 frac2 bias exp-width frac-width))
             (rat (case operation
                    (#.*OP-ADD* (+ rat1 rat2))
                    (#.*OP-SUB* (- rat1 rat2))
                    (#.*OP-MUL* (* rat1 rat2))
                    (#.*OP-DIV* (if (eql rat2 0)
                                    ;; this case should never happen
                                    ;; cause we already handled in
                                    ;; sse-add/sub/mul/div-special function.
                                    0
                                  (/ rat1 rat2)))
                    ;; Unimplemented operations.
                    (otherwise 0)))

             (rounded-rat (rat-round rat rc bias exp-width frac-width))
             (rounded-sign
              (sse-add/sub/mul/div-sign rounded-rat sign1 sign2 operation rc))
             (rounded-expo (ACL2::expo rounded-rat))

             ;; Check overflow
             (overflow (>= rounded-expo (1+ bias)))
             ;; Set OE flag
             (mxcsr (if overflow (set-flag #.*mxcsr-oe* mxcsr) mxcsr))

             (om (logbitp #.*mxcsr-om* mxcsr))

             ;; Check underflow
             (underflow (underflowp rat rounded-expo bias))
             (um (logbitp #.*mxcsr-um* mxcsr))

             ;; Check flush-to-zero
             (fz (logbitp #.*mxcsr-fz* mxcsr))
             (flush (and underflow um fz))

             ;; Check precision
             (imprecision (or (not (eql rat rounded-rat))
                              (and overflow om)
                              flush))
             (pm (logbitp #.*mxcsr-pm* mxcsr))

             ;; Set UE flag
             (mxcsr (if um
                        (if (and underflow imprecision)
                            (set-flag #.*mxcsr-ue* mxcsr)
                          mxcsr)
                      (if underflow (set-flag #.*mxcsr-ue* mxcsr) mxcsr)))

             ;; Set PE flag
             (mxcsr (if imprecision (set-flag #.*mxcsr-pe* mxcsr) mxcsr))

             ((when (and overflow (not om)))
              (mv 'overflow-exception-is-not-masked 0 mxcsr))

             ((when (and underflow (not um)))
              (mv 'underflow-exception-is-not-masked 0 mxcsr))

             ((when (and imprecision (not pm)))
              (mv 'precision-exception-is-not-masked 0 mxcsr))

             (fp-result
              (rat-to-fp rounded-rat rounded-sign
                         overflow underflow flush rc
                         exp-width frac-width)))

            (mv nil fp-result mxcsr)))))

(defthm integerp-sse-add/sub/mul/div-1
  (integerp (mv-nth 1 (sse-add/sub/mul/div operation op1 op2 mxcsr
                                           exp-width frac-width)))
  :hints (("Goal" :in-theory (disable RATIONALP-FP-TO-RAT
                                      INTEGERP-SSE-DAZ-1
                                      INTEGERP-SSE-DAZ-2
                                      POSP
                                      FP-DECODE-LEMMA-4-1
                                      FP-DECODE-LEMMA-2-1
                                      NATP-BIAS)))
  :rule-classes :type-prescription)

(defthm natp-sse-add/sub/mul/div-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-add/sub/mul/div operation op1 op2 mxcsr
                                                exp-width frac-width))))
  :hints (("Goal" :in-theory (disable RATIONALP-FP-TO-RAT
                                      INTEGERP-SSE-DAZ-1
                                      INTEGERP-SSE-DAZ-2
                                      POSP
                                      DEFAULT-<-1
                                      DEFAULT-<-2
                                      DEFAULT-*-1
                                      DEFAULT-*-2
                                      DEFAULT-+-2
                                      DEFAULT-+-1
                                      DEFAULT-UNARY-/
                                      DEFAULT-UNARY-MINUS
                                      INTEGERP-RAT-TO-FP
                                      RATIONALP-IMPLIES-ACL2-NUMBERP
                                      INTEGERP-FP-ENCODE-INTEGER
                                      FP-DECODE-LEMMA-4-1
                                      FP-DECODE-LEMMA-2-1
                                      NATP-BIAS)))
  :rule-classes :type-prescription)

(in-theory (disable sse-add/sub/mul/div))

(defun sse-sqrt-special (kind sign exp implicit frac
                              exp-width frac-width)

  ;; Shilpi: Remove nfix later...

  ;; Check invalid operation conditions and then return corresponding
  ;; result. Also handle the infinities.
  ;; Return (mv flag sign exp implicit frac invalid).
  (declare (xargs :guard (and (integerp sign)
                              (integerp exp)
                              (integerp implicit)
                              (integerp frac)
                              (posp exp-width) (posp frac-width))))
  (cond
   ((eq kind 'snan)
    (flag-make-special-bp 'qnan
                          (part-select frac :low 0 :high (nfix (- frac-width 2)))
                          ;; (get-bits 0 (- frac-width 2) frac)
                          sign t))
   ((or (eq kind 'qnan) (eq kind 'indef)
        (and (eq kind 'inf) (int= sign 0)))
    (mv t sign exp implicit frac nil))
   ((and (int= sign 1) (not (eq kind 'zero)))
    ;; indef
    (flag-make-special-bp 'indef 0 1 t))
   (t (mv nil 0 0 0 0 nil))))

(defthm integerp-sse-sqrt-special-1
  (implies (integerp sign)
           (integerp (mv-nth 1 (sse-sqrt-special
                                kind sign exp implicit frac
                                exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm integerp-sse-sqrt-special-2
  (implies (integerp exp)
           (integerp (mv-nth 2 (sse-sqrt-special
                                kind sign exp implicit frac
                                exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm integerp-sse-sqrt-special-3
  (implies (integerp implicit)
           (integerp (mv-nth 3 (sse-sqrt-special
                                kind sign exp implicit frac
                                exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm integerp-sse-sqrt-special-4
  (implies (integerp frac)
           (integerp (mv-nth 4 (sse-sqrt-special
                                kind sign exp implicit frac
                                exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-sqrt-special))

(ACL2::with-supporters
 (local
  (include-book "rtl/rel9/lib/sqrt" :dir :system))

 (defun sse-sqrt (op mxcsr exp-width frac-width)
   (declare (xargs :guard (and (integerp op) (natp mxcsr)
                               (posp exp-width) (posp frac-width))))
   (b* (((mv kind sign exp implicit frac)
         (fp-decode op exp-width frac-width))
        (daz (logbitp #.*mxcsr-daz* mxcsr))
        ((mv kind exp frac)
         (sse-daz kind exp frac daz))

        ((mv special-ok sign-special exp-special & frac-special invalid)
         (sse-sqrt-special kind sign exp implicit frac
                           exp-width frac-width))

        ;; Check invalid operation
        (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
        (im (logbitp #.*mxcsr-im* mxcsr))
        ((when (and invalid (not im)))
         (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

        ;; Check denormal operand
        (de (and (eq kind 'denormal)
                 (not special-ok)))
        (mxcsr (if de (set-flag #.*mxcsr-de* mxcsr) mxcsr))
        (dm (logbitp #.*mxcsr-dm* mxcsr))
        ((when (and de (not dm)))
         (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

       (if special-ok
           (mv nil
               (fp-encode-integer sign-special exp-special frac-special
                                  exp-width frac-width)
               mxcsr)
         (b* ((bias (ec-call (ACL2::bias exp-width)))
              (rat (fp-to-rat sign exp frac bias exp-width frac-width))
              (sqrt-rat
               (if (>= rat 0)
                   (ec-call (ACL2::qsqrt rat (+ 3 exp-width frac-width)))
                 ;; Would never be reached as we've already handled negative
                 ;; operand in sse-sqrt-special function.
                 0))

              (rc (mbe :logic
                       (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                       ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                       :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))

              (rounded-sqrt-rat (rat-round sqrt-rat rc bias
                                           exp-width frac-width))

              ;; Check precision
              (imprecision (not (eql sqrt-rat rounded-sqrt-rat)))
              (pm (logbitp #.*mxcsr-pm* mxcsr))

              ;; Set PE flag
              (mxcsr (if imprecision (set-flag #.*mxcsr-pe* mxcsr) mxcsr))

              ((when (and imprecision (not pm)))
               (mv 'precision-exception-is-not-masked 0 mxcsr))

              (fp-result
               (rat-to-fp rounded-sqrt-rat sign
                          nil nil nil rc
                          exp-width frac-width)))

             (mv nil fp-result mxcsr))))))

(defthm integerp-sse-sqrt-1
  (integerp (mv-nth 1 (sse-sqrt op mxcsr exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm natp-sse-sqrt-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-sqrt op mxcsr exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-sqrt))

;; Define max/min functions.

(defun sse-max/min-special (kind1 sign1 exp1 implicit1 frac1
                                  kind2 sign2 exp2 implicit2 frac2
                                  operation)
  ;; Check whether the operands are SNaN or QNaN. If at least one of them is
  ;; NaN or both of them are zeros, return the second operand.
  ;; Also handle the infinities.
  ;; Return (mv flag sign exp implicit frac invalid).
  (declare (xargs :guard (and (integerp sign1) (integerp sign2)
                              (integerp exp1) (integerp exp2)
                              (integerp implicit1) (integerp implicit2)
                              (integerp frac1) (integerp frac2)
                              (integerp operation)))
           (type (integer 0 36) operation))
  (cond
   ((or (eq kind1 'snan) (eq kind1 'qnan) (eq kind1 'indef)
        (eq kind2 'snan) (eq kind2 'qnan) (eq kind2 'indef))
    (mv t sign2 exp2 implicit2 frac2 t))
   ((and (eq kind1 'zero) (eq kind2 'zero))
    (mv t sign2 exp2 implicit2 frac2 nil))
   ((eq kind1 'inf)
    (if (or (and (int= operation #.*OP-MAX*) (int= sign1 0))
            (and (int= operation #.*OP-MIN*) (int= sign1 1)))
        (mv t sign1 exp1 implicit1 frac1 nil)
      (mv t sign2 exp2 implicit2 frac2 nil)))
   ((eq kind2 'inf)
    (if (or (and (int= operation #.*OP-MAX*) (int= sign2 0))
            (and (int= operation #.*OP-MIN*) (int= sign2 1)))
        (mv t sign2 exp2 implicit2 frac2 nil)
      (mv t sign1 exp1 implicit1 frac1 nil)))
   (t (mv nil 0 0 0 0 nil))))

(defthm integerp-sse-max/min-special-1
  (implies (and (integerp sign1) (integerp sign2))
           (integerp (mv-nth 1 (sse-max/min-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-max/min-special-2
  (implies (and (integerp exp1) (integerp exp2))
           (integerp (mv-nth 2 (sse-max/min-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-max/min-special-3
  (implies (and (integerp implicit1) (integerp implicit2))
           (integerp (mv-nth 3 (sse-max/min-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                operation))))
  :rule-classes :type-prescription)

(defthm integerp-sse-max/min-special-4
  (implies (and (integerp frac1) (integerp frac2))
           (integerp (mv-nth 4 (sse-max/min-special
                                kind1 sign1 exp1 implicit1 frac1
                                kind2 sign2 exp2 implicit2 frac2
                                operation))))
  :rule-classes :type-prescription)

(in-theory (disable sse-max/min-special))

(defun-inline sse-max/min-sign (rat rat1 sign1 sign2)
  (declare (xargs :guard (and (rationalp rat)
                              (rationalp rat1)
                              (integerp sign1)
                              (integerp sign2))))
  (if (eql rat rat1) sign1 sign2))

(defthm integerp-sse-max/min-sign
  (implies (forced-and (integerp sign1)
                      (integerp sign2))
           (integerp (sse-max/min-sign rat rat1 sign1 sign2)))
  :rule-classes :type-prescription)

(in-theory (disable sse-max/min-sign))

(defun sse-max/min (operation op1 op2 mxcsr exp-width frac-width)
  (declare (xargs :guard (and (integerp operation)
                              (integerp op1) (integerp op2) (natp mxcsr)
                              (posp exp-width) (posp frac-width)))
           (type (integer 0 36) operation))
  (b* (((mv kind1 sign1 exp1 implicit1 frac1)
        (fp-decode op1 exp-width frac-width))
       ((mv kind2 sign2 exp2 implicit2 frac2)
        (fp-decode op2 exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind1 exp1 frac1)
        (sse-daz kind1 exp1 frac1 daz))
       ((mv kind2 exp2 frac2)
        (sse-daz kind2 exp2 frac2 daz))
       ((mv special-ok sign exp & frac invalid)
        (sse-max/min-special kind1 sign1 exp1 implicit1 frac1
                             kind2 sign2 exp2 implicit2 frac2
                             operation))

       ;; Check invalid operation
       (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (denormal-exception kind1 kind2))
       (mxcsr (if de (set-flag #.*mxcsr-de* mxcsr) mxcsr))
       (dm (logbitp #.*mxcsr-dm* mxcsr))
       ((when (and de (not dm)))
        (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

      (if special-ok
          (mv nil
              (fp-encode-integer sign exp frac exp-width frac-width)
              mxcsr)
        (b* ((bias (ec-call (ACL2::bias exp-width)))
             (rat1 (fp-to-rat sign1 exp1 frac1 bias exp-width frac-width))
             (rat2 (fp-to-rat sign2 exp2 frac2 bias exp-width frac-width))
             (rat (case operation
                    (#.*OP-MAX* (if (> rat1 rat2) rat1 rat2))
                    (#.*OP-MIN* (if (< rat1 rat2) rat1 rat2))
                    ;; Should never be reached.
                    (otherwise 0)))

             (sign (sse-max/min-sign rat rat1 sign1 sign2))

             (fp-result
              (rat-to-fp rat sign
                         nil nil nil 0 ;; rc will not be used here.
                                       ;; I just put a dummy value 0.
                         exp-width frac-width)))

            (mv nil fp-result mxcsr)))))

(defthm integerp-sse-max/min-1
  (integerp (mv-nth 1 (sse-max/min operation op1 op2 mxcsr
                                   exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm natp-sse-max/min-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-max/min operation op1 op2 mxcsr
                                        exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-max/min))

;; ======================================================================

;; SSE comparison utils:

(defun sse-cmp-special (kind1 sign1 kind2 sign2
                              exp-width frac-width operation)
  ;; Check whether operands are NaN and then return the corresponding
  ;; results. Also handle the infinities.
  ;; Return (mv flag integer-result invalid).
  (declare (xargs :guard (and (integerp sign1) (integerp sign2)
                              (posp exp-width) (posp frac-width)
                              (integerp operation)))
           (type (integer 0 9) operation))
  (let ((invalid (or (eq kind1 'snan)
                     (eq kind2 'snan)
                     (and (or (eq kind1 'qnan) (eq kind1 'indef)
                              (eq kind2 'qnan) (eq kind2 'indef))
                          (or (int= operation #.*OP-CMPLT*)
                              (int= operation #.*OP-CMPLE*)
                              (int= operation #.*OP-CMPNLT*)
                              (int= operation #.*OP-CMPNLE*)
                              (int= operation #.*OP-COMI*))))))
    (cond
     ((or (eq kind1 'snan) (eq kind1 'qnan) (eq kind1 'indef)
          (eq kind2 'snan) (eq kind2 'qnan) (eq kind2 'indef))
      (cond ((or (int= operation #.*OP-CMPUNORD*)
                 (int= operation #.*OP-CMPNEQ*)
                 (int= operation #.*OP-CMPNLT*)
                 (int= operation #.*OP-CMPNLE*))
             ;; Return the mask of all 1s.
             (mv t
                 (1- (ash 1 (+ 1 exp-width frac-width)))
                 invalid))
            ((or (int= operation #.*OP-COMI*)
                 (int= operation #.*OP-UCOMI*))
             ;; Return a particular integer result for this case (here we
             ;; return 7). We then use this result to recognize the unordered
             ;; relationship and set the corresponding flags in the EFLAGS
             ;; register.
             (mv t 7 invalid))
            ;; Return the mask of all 0s.
            (t (mv t 0 invalid))))
     ((or (eq kind1 'inf) (eq kind2 'inf))
      ;; Convert -inf to -1,
      ;;         +inf to  1,
      ;;         finite to 0.
      ;; The purpose of this conversion is used for comparison between two
      ;; operands in which at least one of them is infinity.
      (b* ((rat1 (if (eq kind1 'inf)
                      (if (int= sign1 0) 1 -1)
                    0))
            (rat2 (if (eq kind2 'inf)
                      (if (int= sign2 0) 1 -1)
                    0))
            (cmp-result
              (case operation
                (#.*OP-CMPEQ* (= rat1 rat2))
                (#.*OP-CMPLT* (< rat1 rat2))
                (#.*OP-CMPLE* (<= rat1 rat2))
                (#.*OP-CMPUNORD* nil) ;; Neither source operand is a NaN.
                (#.*OP-CMPNEQ* (not (= rat1 rat2)))
                (#.*OP-CMPNLT* (not (< rat1 rat2)))
                (#.*OP-CMPNLE* (not (<= rat1 rat2)))
                (#.*OP-CMPORD* t) ;; Neither source operand is a NaN.
                (otherwise nil)))

             (result
              (if (or (int= operation #.*OP-COMI*)
                      (int= operation #.*OP-UCOMI*))
                  ;; Compare rat1 with rat2.
                  ;; Return 0 standing for rat1 > rat2,
                  ;;        1 standing for rat1 < rat2,
                  ;;        4 standing for ra1 = rat2.
                  ;; Of course, we can choose any other values to return.
                  ;; The only requirement is that they must be distinct and
                  ;; different from the value returned for the case of
                  ;; unordered relationship, which is 7.
                  (cond ((> rat1 rat2) 0)
                        ((< rat1 rat2) 1)
                        (t 4))
                (if cmp-result
                    ;; Return the mask of all 1s.
                    (1- (ash 1 (+ 1 exp-width frac-width)))
                  ;; Return the mask of all 0s.
                  0))))
          (mv t result invalid)))
     (t (mv nil 0 invalid)))))

(defthm integerp-sse-cmp-special-1
  (integerp (mv-nth 1 (sse-cmp-special
                       kind1 sign1 kind2 sign2
                       exp-width frac-width operation)))
  :rule-classes :type-prescription)

(in-theory (disable sse-cmp-special))

(defun sse-cmp (operation op1 op2 mxcsr exp-width frac-width)
  (declare (xargs :guard (and (integerp operation)
                              (integerp op1) (integerp op2) (natp mxcsr)
                              (posp exp-width) (posp frac-width)))
           (type (integer 0 9) operation))
  (b* (((mv kind1 sign1 exp1 ?implicit1 frac1)
        (fp-decode op1 exp-width frac-width))
       ((mv kind2 sign2 exp2 ?implicit2 frac2)
        (fp-decode op2 exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind1 exp1 frac1)
        (sse-daz kind1 exp1 frac1 daz))
       ((mv kind2 exp2 frac2)
        (sse-daz kind2 exp2 frac2 daz))
       ((mv special-ok result invalid)
        (sse-cmp-special kind1 sign1 kind2 sign2
                         exp-width frac-width operation))

       ;; Check invalid operation
       (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (denormal-exception kind1 kind2))
       (mxcsr (if de (set-flag #.*mxcsr-de* mxcsr) mxcsr))
       (dm (logbitp #.*mxcsr-dm* mxcsr))
       ((when (and de (not dm)))
        (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

      (if special-ok
          (mv nil result mxcsr)
        (b* ((bias (ec-call (ACL2::bias exp-width)))
             (rat1 (fp-to-rat sign1 exp1 frac1 bias exp-width frac-width))
             (rat2 (fp-to-rat sign2 exp2 frac2 bias exp-width frac-width))
             (cmp-result
              (case operation
                (#.*OP-CMPEQ* (= rat1 rat2))
                (#.*OP-CMPLT* (< rat1 rat2))
                (#.*OP-CMPLE* (<= rat1 rat2))
                (#.*OP-CMPUNORD* nil) ;; Neither source operand is a NaN.
                (#.*OP-CMPNEQ* (not (= rat1 rat2)))
                (#.*OP-CMPNLT* (not (< rat1 rat2)))
                (#.*OP-CMPNLE* (not (<= rat1 rat2)))
                (#.*OP-CMPORD* t) ;; Neither source operand is a NaN.
                (otherwise nil)))

             (result
              (if (or (int= operation #.*OP-COMI*)
                      (int= operation #.*OP-UCOMI*))
                  ;; Compare rat1 with rat2.
                  ;; Return 0 standing for rat1 > rat2,
                  ;;        1 standing for rat1 < rat2,
                  ;;        4 standing for ra1 = rat2.
                  ;; Of course, we can choose any other values to return.
                  ;; The only requirement is that they must be distinct and
                  ;; different from the value returned by the function
                  ;; sse-cmp-special for the case of unordered relationship,
                  ;; which is 7.
                  (cond ((> rat1 rat2) 0)
                        ((< rat1 rat2) 1)
                        (t 4))
                (if cmp-result
                    ;; Return all 1s.
                    (1- (ash 1 (+ 1 exp-width frac-width)))
                  ;; Return all 0s.
                  0))))

            (mv nil result mxcsr)))))

(defthm integerp-sse-cmp-1
  (integerp (mv-nth 1 (sse-cmp operation op1 op2 mxcsr exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm natp-sse-cmp-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-cmp operation op1 op2 mxcsr
                                    exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-cmp))

;; ======================================================================

;; SSE conversion utils:

; fp-to-i:

(defun rat-round-to-int-rn (rat)
  (declare (xargs :guard (rationalp rat)))
  (round rat 1))

(defthm integerp-rat-round-to-int-rn
  (integerp (rat-round-to-int-rn rat))
  :rule-classes :type-prescription)

(defun rat-round-to-int-rd (rat)
  (declare (xargs :guard (rationalp rat)))
  (let ((rn (round rat 1)))
    (if (> rn rat) (1- rn) rn)))

(defthm integerp-rat-round-to-int-rd
  (integerp (rat-round-to-int-rd rat))
  :rule-classes :type-prescription)

(defun rat-round-to-int-ru (rat)
  (declare (xargs :guard (rationalp rat)))
  (let ((rn (round rat 1)))
    (if (< rn rat) (1+ rn) rn)))

(defthm integerp-rat-round-to-int-ru
  (integerp (rat-round-to-int-ru rat))
  :rule-classes :type-prescription)

(defun rat-round-to-int-rz (rat)
  (declare (xargs :guard (rationalp rat)))
  (truncate rat 1))

(defthm integerp-rat-round-to-int-rz
  (integerp (rat-round-to-int-rz rat))
  :rule-classes :type-prescription)

(in-theory (disable rat-round-to-int-rn
                    rat-round-to-int-rd
                    rat-round-to-int-ru
                    rat-round-to-int-rz))

(defun-inline rat-round-to-int (rat rc)
  (declare (xargs :guard (and (rationalp rat)
                              (integerp rc))))
  (rc-cases
   :rn (rat-round-to-int-rn rat)
   :rd (rat-round-to-int-rd rat)
   :ru (rat-round-to-int-ru rat)
   :rz (rat-round-to-int-rz rat)
   ;; Should never get here.
   :other 0))

(defthm integerp-rat-round-to-int
  (integerp (rat-round-to-int rat rc))
  :rule-classes :type-prescription)

(in-theory (disable rat-round-to-int))

(defun sse-cvt-fp-to-int-special (kind nbytes)
  ;; Check whether the operand is NaN or infinity. If so, return the integer
  ;; indefinite.
  ;; Return (mv flag integer-result invalid).
  (declare (xargs :guard (natp nbytes)))
  (let ((invalid (or (eq kind 'snan) (eq kind 'qnan)
                     (eq kind 'indef) (eq kind 'inf))))
    (if invalid
        (mv t (ash 1 (1- (ash nbytes 3))) invalid)
      (mv nil 0 invalid))))

(defthm integerp-sse-cvt-fp-to-int-special-1
  (implies (natp nbytes)
           (integerp (mv-nth 1 (sse-cvt-fp-to-int-special kind nbytes))))
  :rule-classes :type-prescription)

(in-theory (disable sse-cvt-fp-to-int-special))

(defun sse-cvt-fp-to-int (nbytes op mxcsr trunc exp-width frac-width)
  (declare (xargs :guard (and (natp nbytes)
                              (integerp op) (natp mxcsr)
                              (booleanp trunc)
                              (posp exp-width) (posp frac-width))))
  (b* (((mv kind sign exp ?implicit frac)
        (fp-decode op exp-width frac-width))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind exp frac)
        (sse-daz kind exp frac daz))
       ((mv special-ok result invalid)
        (sse-cvt-fp-to-int-special kind nbytes))

       ;; Check invalid operation
       (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr)))

      (if special-ok
          (mv nil result mxcsr)
        (b* ((bias (ec-call (ACL2::bias exp-width)))
             (rat (fp-to-rat sign exp frac bias exp-width frac-width))
             (rc (mbe :logic
                      (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                      ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                      :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
             (rc (if trunc #b11 rc))
             (rat-to-int (rat-round-to-int rat rc))
             (nbits (ash nbytes 3))
             (min-signed-int (- (expt 2 (1- nbits))))
             (max-signed-int (1- (expt 2 (1- nbits))))
             (out-of-range (or (< rat-to-int min-signed-int)
                               (> rat-to-int max-signed-int)))
             ;; If the converted integer is out-of-range, set IE flag.
             (mxcsr (if out-of-range (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
             ((when (and out-of-range (not im)))
              (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))
             ;; If out-of-range and IM is masked, return integer indefinite.
             ((when out-of-range)
              (mv nil (ash 1 (1- nbits)) mxcsr))

             ;; Check precision
             (pe (not (= rat-to-int rat)))
             (mxcsr (if pe (set-flag #.*mxcsr-pe* mxcsr) mxcsr))
             (pm (logbitp #.*mxcsr-pm* mxcsr))
             ((when (and pe (not pm)))
              (mv 'precision-exception-is-not-masked 0 mxcsr)))

            (mv nil rat-to-int mxcsr)))))

(defthm integerp-sse-cvt-fp-to-int-1
  (implies (natp nbytes)
           (integerp (mv-nth 1 (sse-cvt-fp-to-int nbytes op mxcsr trunc
                                                  exp-width frac-width))))
  :rule-classes :type-prescription)

(defthm natp-sse-cvt-fp-to-int-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-cvt-fp-to-int nbytes op mxcsr trunc
                                              exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-cvt-fp-to-int))

; i-to-fp:
(defun sse-cvt-int-to-fp (op mxcsr exp-width frac-width)
  (declare (xargs :guard (and (integerp op) (natp mxcsr)
                              (posp exp-width) (posp frac-width))))
  (b* ((rc (mbe :logic
                (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
       (bias (ec-call (ACL2::bias exp-width)))
       (int-to-rat (rat-round op rc bias exp-width frac-width))
       (sign (cond ((> int-to-rat 0) 0)
                   ((< int-to-rat 0) 1)
                   (t (if (int= rc #.*rc-rd*) 1 0))))

       ;; Check precision
       (pe (not (= op int-to-rat)))
       (mxcsr (if pe (set-flag #.*mxcsr-pe* mxcsr) mxcsr))
       (pm (logbitp #.*mxcsr-pm* mxcsr))
       ((when (and pe (not pm)))
        (mv 'precision-exception-is-not-masked 0 mxcsr))

       (fp-result
        (rat-to-fp int-to-rat sign
                   nil nil nil rc
                   exp-width frac-width)))

      (mv nil fp-result mxcsr)))

(defthm integerp-sse-cvt-int-to-fp-1
  (integerp (mv-nth 1 (sse-cvt-int-to-fp op mxcsr
                                         exp-width frac-width)))
  :rule-classes :type-prescription)

(defthm natp-sse-cvt-int-to-fp-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-cvt-int-to-fp op mxcsr
                                              exp-width frac-width))))
  :rule-classes :type-prescription)

(in-theory (disable sse-cvt-int-to-fp))

; fp1-to-fp2:

(defun sse-cvt-fp1-to-fp2-special (kind sign implicit frac frac-width1
                                        exp-width2 frac-width2)

  ;; Shilpi: nfix...

  ;; Check whether the operand is SNaN or QNaN and then return corresponding
  ;; result. Also handle the infinities.
  ;; Return (mv flag sign exp implicit frac invalid).
  (declare (xargs :guard (and (integerp sign)
                              (integerp implicit)
                              (integerp frac)
                              (posp frac-width1)
                              (posp exp-width2) (posp frac-width2))))
  (let ((invalid (eq kind 'snan)))
    (cond
     ((eq kind 'snan)
      (let ((exp-width exp-width2)
            (frac-width frac-width2)
            (nan-frac-bits (ash
                            (part-select frac :low 0 :high (nfix (- frac-width1 2)))
                            ;; (get-bits 0 (- frac-width1 2) frac)
                            (- frac-width2 frac-width1))))
        (flag-make-special-bp 'qnan nan-frac-bits
                              sign invalid)))
     ((or (eq kind 'qnan) (eq kind 'indef))
      (let ((exp-width exp-width2)
            (frac (ash frac (- frac-width2 frac-width1))))
        (mv t sign (fp-max-exp) implicit frac invalid)))
     ((eq kind 'inf)
      (let ((exp-width exp-width2)
            (frac-width frac-width2))
        (flag-make-special-bp 'inf 0 sign invalid)))
     (t (mv nil 0 0 0 0 invalid)))))

(defthm integerp-sse-cvt-fp1-to-fp2-special-1
  (implies (integerp sign)
           (integerp (mv-nth 1 (sse-cvt-fp1-to-fp2-special kind
                                                           sign
                                                           implicit
                                                           frac
                                                           frac-width1
                                                           exp-width2
                                                           frac-width2))))
  :rule-classes :type-prescription)

(defthm integerp-sse-cvt-fp1-to-fp2-special-2
  (integerp (mv-nth 2 (sse-cvt-fp1-to-fp2-special kind
                                                  sign
                                                  implicit
                                                  frac
                                                  frac-width1
                                                  exp-width2
                                                  frac-width2)))
  :rule-classes :type-prescription)

(defthm integerp-sse-cvt-fp1-to-fp2-special-3
  (implies (integerp implicit)
           (integerp (mv-nth 3 (sse-cvt-fp1-to-fp2-special kind
                                                           sign
                                                           implicit
                                                           frac
                                                           frac-width1
                                                           exp-width2
                                                           frac-width2))))
  :rule-classes :type-prescription)

(defthm integerp-sse-cvt-fp1-to-fp2-special-4
  (integerp (mv-nth 4 (sse-cvt-fp1-to-fp2-special kind
                                                  sign
                                                  implicit
                                                  frac
                                                  frac-width1
                                                  exp-width2
                                                  frac-width2)))
  :rule-classes :type-prescription)

(in-theory (disable sse-cvt-fp1-to-fp2-special))

(defun sse-cvt-fp1-to-fp2 (op mxcsr
                              exp-width1 frac-width1
                              exp-width2 frac-width2)
  (declare (xargs :guard (and (integerp op) (natp mxcsr)
                              (posp exp-width1) (posp frac-width1)
                              (posp exp-width2) (posp frac-width2))))
  (b* (((mv kind sign exp ?implicit frac)
        (fp-decode op exp-width1 frac-width1))
       (daz (logbitp #.*mxcsr-daz* mxcsr))
       ((mv kind ?exp frac)
        (sse-daz kind exp frac daz))
       ((mv special-ok sign-special exp-special & frac-special invalid)
        (sse-cvt-fp1-to-fp2-special kind sign implicit frac frac-width1
                                    exp-width2 frac-width2))

       ;; Check invalid operation
       (mxcsr (if invalid (set-flag #.*mxcsr-ie* mxcsr) mxcsr))
       (im (logbitp #.*mxcsr-im* mxcsr))
       ((when (and invalid (not im)))
        (mv 'invalid-operand-exception-is-not-masked 0 mxcsr))

       ;; Check denormal operand
       (de (eq kind 'denormal))
       (mxcsr (if de (set-flag #.*mxcsr-de* mxcsr) mxcsr))
       (dm (logbitp #.*mxcsr-dm* mxcsr))
       ((when (and de (not dm)))
        (mv 'denormal-operand-exception-is-not-masked 0 mxcsr)))

      (if special-ok
          (mv nil
              (fp-encode-integer sign-special exp-special frac-special
                                 exp-width2 frac-width2)
              mxcsr)
        (b* ((bias1 (ec-call (ACL2::bias exp-width1)))
             (bias2 (ec-call (ACL2::bias exp-width2)))
             (rat (fp-to-rat sign exp frac bias1 exp-width1 frac-width1))
             (rc (mbe :logic (part-select mxcsr :low #.*mxcsr-rc* :high (1+ #.*mxcsr-rc*))
                      ;; (get-bits #.*mxcsr-rc* (1+ #.*mxcsr-rc*) mxcsr)
                      :exec  (logand #b11 (ash mxcsr (- #.*mxcsr-rc*)))))
             (rounded-rat (rat-round rat rc bias2 exp-width2 frac-width2))
             (rounded-expo (ACL2::expo rounded-rat))

             ;; Check overflow
             (overflow (>= rounded-expo (1+ bias2)))
             ;; Set OE flag
             (mxcsr (if overflow (set-flag #.*mxcsr-oe* mxcsr) mxcsr))

             (om (logbitp #.*mxcsr-om* mxcsr))

             ;; Check underflow
             (underflow (underflowp rat rounded-expo bias2))
             (um (logbitp #.*mxcsr-um* mxcsr))

             ;; Check flush-to-zero
             (fz (logbitp #.*mxcsr-fz* mxcsr))
             (flush (and underflow um fz))

             ;; Check precision
             (imprecision (or (not (eql rat rounded-rat))
                              (and overflow om)
                              flush))
             (pm (logbitp #.*mxcsr-pm* mxcsr))

             ;; Set UE flag
             (mxcsr (if um
                        (if (and underflow imprecision)
                            (set-flag #.*mxcsr-ue* mxcsr)
                          mxcsr)
                      (if underflow (set-flag #.*mxcsr-ue* mxcsr) mxcsr)))

             ;; Set PE flag
             (mxcsr (if imprecision (set-flag #.*mxcsr-pe* mxcsr) mxcsr))

             ((when (and overflow (not om)))
              (mv 'overflow-exception-is-not-masked 0 mxcsr))

             ((when (and underflow (not um)))
              (mv 'underflow-exception-is-not-masked 0 mxcsr))

             ((when (and imprecision (not pm)))
              (mv 'precision-exception-is-not-masked 0 mxcsr))

             (fp-result
              (rat-to-fp rounded-rat sign
                         overflow underflow flush rc
                         exp-width2 frac-width2)))

            (mv nil fp-result mxcsr)))))

(defthm integerp-sse-cvt-fp1-to-fp2-1
  (integerp (mv-nth 1 (sse-cvt-fp1-to-fp2 op mxcsr
                                          exp-width1 frac-width1
                                          exp-width2 frac-width2)))
  :rule-classes :type-prescription)

(defthm natp-sse-cvt-fp1-to-fp2-2
  (implies (natp mxcsr)
           (natp (mv-nth 2 (sse-cvt-fp1-to-fp2 op mxcsr
                                               exp-width1 frac-width1
                                               exp-width2 frac-width2))))
  :rule-classes :type-prescription)

(in-theory (disable sse-cvt-fp1-to-fp2))

;; ======================================================================

;; Single-Precision Operations:

(defn sp-sse-add/sub/mul/div (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n32p op1)
                              (n32p op2)
                              (n32p mxcsr))
                  :guard-hints (("Goal"
                                 :in-theory (enable sse-add/sub/mul/div))))
           (type (integer 0 36) operation)
           (type (unsigned-byte 32) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-add/sub/mul/div operation op1 op2 mxcsr
                             #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))
       (result (n32 result))
       (mxcsr (mbe :logic (n32 mxcsr)
                   :exec  mxcsr)))
      (mv flg result mxcsr)))

(defthm n32p-sp-sse-add/sub/mul/div-1
  (n32p (mv-nth 1 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-add/sub/mul/div-2
  (n32p (mv-nth 2 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (sp-sse-add/sub/mul/div operation op1 op2 mxcsr))
       *2^32*))))

(defn sp-sse-max/min (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n32p op1)
                              (n32p op2)
                              (n32p mxcsr))
                  :guard-hints (("Goal"
                                 :in-theory (enable sse-max/min))))
           (type (integer 0 36) operation)
           (type (unsigned-byte 32) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-max/min operation op1 op2 mxcsr
                     #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))
       (result (n32 result))
       (mxcsr (mbe :logic (n32 mxcsr)
                   :exec  mxcsr)))
      (mv flg result mxcsr)))

(defthm n32p-sp-sse-max/min-1
  (n32p (mv-nth 1 (sp-sse-max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-max/min operation op1 op2 mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-max/min-2
  (n32p (mv-nth 2 (sp-sse-max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (sp-sse-max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (sp-sse-max/min operation op1 op2 mxcsr))
       *2^32*))))

(in-theory (disable sp-sse-add/sub/mul/div
                    sp-sse-max/min))

(defn sp-sse-add/sub/mul/div/max/min (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n32p op1)
                              (n32p op2)
                              (n32p mxcsr)))
           (type (integer 0 36) operation)
           (type (unsigned-byte 32) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (if (or (int= operation #.*OP-MAX*) (int= operation #.*OP-MIN*))
      (sp-sse-max/min operation op1 op2 mxcsr)
    (sp-sse-add/sub/mul/div operation op1 op2 mxcsr)))

(defthm n32p-sp-sse-add/sub/mul/div/max/min-1
  (n32p (mv-nth 1 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-add/sub/mul/div/max/min-2
  (n32p (mv-nth 2 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (sp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
       *2^32*))))

(defn sp-sse-sqrt (op mxcsr)
  (declare (xargs :guard (and (n32p op)
                              (n32p mxcsr)))
           (type (unsigned-byte 32) op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-sqrt op mxcsr
                  #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
      (mv flg result mxcsr)))

(defthm n32p-sp-sse-sqrt-1
  (n32p (mv-nth 1 (sp-sse-sqrt op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-sqrt op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-sqrt op mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-sqrt-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (sp-sse-sqrt op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-sqrt) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (sp-sse-sqrt op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (sp-sse-sqrt op mxcsr))
                *2^32*)))))

(defn sp-sse-cmp (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n32p op1)
                              (n32p op2)
                              (n32p mxcsr)))
           (type (integer 0 9) operation)
           (type (unsigned-byte 32) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cmp operation op1 op2 mxcsr
                 #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
      (mv flg result mxcsr)))

(defthm n32p-sp-sse-cmp-1
  (n32p (mv-nth 1 (sp-sse-cmp operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-cmp operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-cmp operation op1 op2 mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-cmp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (sp-sse-cmp operation op1 op2 mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cmp) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (sp-sse-cmp operation op1 op2 mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (sp-sse-cmp operation op1 op2 mxcsr))
                *2^32*)))))

(defn sp-sse-cvt-fp-to-int (nbytes op mxcsr trunc)
  (declare (xargs :guard (and (natp nbytes)
                              (n32p op)
                              (n32p mxcsr)
                              (booleanp trunc)))
           (type (integer 0 *) nbytes)
           (type (unsigned-byte 32) op)
           (type (unsigned-byte 32) mxcsr)
           (type (or t nil) trunc))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp-to-int nbytes op mxcsr trunc
                           #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (trunc nbytes result)))
      (mv flg result mxcsr)))

(defthm bytesp-sp-sse-cvt-fp-to-int-1
  ;; Shilpi: Try to eliminate (member nbytes '(1 2 4 8 16)) hyp. Also,
  ;; concl had bytesp instead of unsigned-byte-p.
  (implies (and (natp nbytes)
                (member nbytes '(1 2 4 8 16)))
           (unsigned-byte-p
            (ash nbytes 3)
            (mv-nth 1 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc))))
  :hints (("Goal" :in-theory (e/d () ()))))

(defthm n32p-sp-sse-cvt-fp-to-int-2
  (implies (and (n32p mxcsr)
                (natp nbytes))
           (n32p (mv-nth 2 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-fp-to-int) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (forced-and (n32p mxcsr)
                         (natp nbytes))
             (natp (mv-nth 2 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc)))))
   (:linear
    :corollary
    (implies (forced-and (n32p mxcsr)
                         (natp nbytes))
             (< (mv-nth 2 (sp-sse-cvt-fp-to-int nbytes op mxcsr trunc))
                *2^32*)))))

(defn sp-sse-cvt-int-to-fp (op mxcsr)
  (declare (xargs :guard (and (integerp op)
                              (n32p mxcsr)))
           (type integer op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cvt-int-to-fp op mxcsr
                           #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
      (mv flg result mxcsr)))

(defthm n32p-sp-sse-cvt-int-to-fp-1
  (n32p (mv-nth 1 (sp-sse-cvt-int-to-fp op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sp-sse-cvt-int-to-fp op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sp-sse-cvt-int-to-fp op mxcsr))
       *2^32*))))

(defthm n32p-sp-sse-cvt-int-to-fp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (sp-sse-cvt-int-to-fp op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-int-to-fp) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (sp-sse-cvt-int-to-fp op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (sp-sse-cvt-int-to-fp op mxcsr))
                *2^32*)))))

(defn sse-cvt-sp-to-dp (op mxcsr)
  (declare (xargs :guard (and (n32p op)
                              (n32p mxcsr)))
           (type (unsigned-byte 32) op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp1-to-fp2 op mxcsr
                            #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*
                            #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n64 result)))
      (mv flg result mxcsr)))

(defthm n64p-sse-cvt-sp-to-dp-1
  (n64p (mv-nth 1 (sse-cvt-sp-to-dp op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sse-cvt-sp-to-dp op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sse-cvt-sp-to-dp op mxcsr))
       *2^64*))))

(defthm n32p-sse-cvt-sp-to-dp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (sse-cvt-sp-to-dp op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-fp1-to-fp2) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (sse-cvt-sp-to-dp op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (sse-cvt-sp-to-dp op mxcsr))
                *2^32*)))))

(in-theory (disable sp-sse-add/sub/mul/div/max/min
                    sp-sse-sqrt
                    sp-sse-cmp
                    sp-sse-cvt-fp-to-int
                    sp-sse-cvt-int-to-fp
                    sse-cvt-sp-to-dp))

;; Double-Precision Operations:

(defn dp-sse-add/sub/mul/div (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n64p op1)
                              (n64p op2)
                              (n32p mxcsr))
                  :guard-hints (("Goal"
                                 :in-theory (enable sse-add/sub/mul/div))))
           (type (integer 0 36) operation)
           (type (unsigned-byte 64) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-add/sub/mul/div operation op1 op2 mxcsr
                             #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))
       (result (n64 result))
       (mxcsr (mbe :logic (n32 mxcsr)
                   :exec  mxcsr)))
      (mv flg result mxcsr)))

(defthm n64p-dp-sse-add/sub/mul/div-1
  (n64p (mv-nth 1 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-add/sub/mul/div-2
  (n32p (mv-nth 2 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (dp-sse-add/sub/mul/div operation op1 op2 mxcsr))
       *2^32*))))

(defn dp-sse-max/min (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n64p op1)
                              (n64p op2)
                              (n32p mxcsr))
                  :guard-hints (("Goal"
                                 :in-theory (enable sse-max/min))))
           (type (integer 0 36) operation)
           (type (unsigned-byte 64) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-max/min operation op1 op2 mxcsr
                     #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))
       (result (n64 result))
       (mxcsr (mbe :logic (n32 mxcsr)
                   :exec  mxcsr)))
      (mv flg result mxcsr)))

(defthm n64p-dp-sse-max/min-1
  (n64p (mv-nth 1 (dp-sse-max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-max/min operation op1 op2 mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-max/min-2
  (n32p (mv-nth 2 (dp-sse-max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (dp-sse-max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (dp-sse-max/min operation op1 op2 mxcsr))
       *2^32*))))

(in-theory (disable dp-sse-add/sub/mul/div
                    dp-sse-max/min))

(defn dp-sse-add/sub/mul/div/max/min (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n64p op1)
                              (n64p op2)
                              (n32p mxcsr)))
           (type (integer 0 36) operation)
           (type (unsigned-byte 64) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (if (or (int= operation #.*OP-MAX*) (int= operation #.*OP-MIN*))
      (dp-sse-max/min operation op1 op2 mxcsr)
    (dp-sse-add/sub/mul/div operation op1 op2 mxcsr)))

(defthm n64p-dp-sse-add/sub/mul/div/max/min-1
  (n64p (mv-nth 1 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-add/sub/mul/div/max/min-2
  (n32p (mv-nth 2 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 2 (dp-sse-add/sub/mul/div/max/min operation op1 op2 mxcsr))
       *2^32*))))

(defn dp-sse-sqrt (op mxcsr)
  (declare (xargs :guard (and (n64p op)
                              (n32p mxcsr)))
           (type (unsigned-byte 64) op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-sqrt op mxcsr
                  #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n64 result)))
      (mv flg result mxcsr)))

(defthm n64p-dp-sse-sqrt-1
  (n64p (mv-nth 1 (dp-sse-sqrt op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-sqrt op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-sqrt op mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-sqrt-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (dp-sse-sqrt op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-sqrt) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (dp-sse-sqrt op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (dp-sse-sqrt op mxcsr))
                *2^32*)))))

(defn dp-sse-cmp (operation op1 op2 mxcsr)
  (declare (xargs :guard (and (integerp operation)
                              (n64p op1)
                              (n64p op2)
                              (n32p mxcsr)))
           (type (integer 0 9) operation)
           (type (unsigned-byte 64) op1 op2)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cmp operation op1 op2 mxcsr
                 #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n64 result)))
      (mv flg result mxcsr)))

(defthm n64p-dp-sse-cmp-1
  (n64p (mv-nth 1 (dp-sse-cmp operation op1 op2 mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-cmp operation op1 op2 mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-cmp operation op1 op2 mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-cmp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (dp-sse-cmp operation op1 op2 mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cmp) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (dp-sse-cmp operation op1 op2 mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (dp-sse-cmp operation op1 op2 mxcsr))
                *2^32*)))))

(defn dp-sse-cvt-fp-to-int (nbytes op mxcsr trunc)
  (declare (xargs :guard (and (natp nbytes)
                              (n64p op)
                              (n32p mxcsr)
                              (booleanp trunc)))
           (type (integer 0 *) nbytes)
           (type (unsigned-byte 64) op)
           (type (unsigned-byte 32) mxcsr)
           (type (or t nil) trunc))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp-to-int nbytes op mxcsr trunc
                           #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (trunc nbytes result)))
      (mv flg result mxcsr)))

(defthm bytesp-dp-sse-cvt-fp-to-int-1
  ;; Shilpi: Try to eliminate (member nbytes '(1 2 4 8 16)) hyp.
  ;; Also, concl had bytesp instead of unsigned-byte-p.
  (implies (and (natp nbytes)
                (member nbytes '(1 2 4 8 16)))
           (unsigned-byte-p (ash nbytes 3)
                            (mv-nth 1 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc)))))

(defthm n32p-dp-sse-cvt-fp-to-int-2
  (implies (and (n32p mxcsr)
                (natp nbytes))
           (n32p (mv-nth 2 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-fp-to-int) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (forced-and (n32p mxcsr)
                         (natp nbytes))
             (natp (mv-nth 2 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc)))))
   (:linear
    :corollary
    (implies (forced-and (n32p mxcsr)
                         (natp nbytes))
             (< (mv-nth 2 (dp-sse-cvt-fp-to-int nbytes op mxcsr trunc))
                *2^32*)))))

(defn dp-sse-cvt-int-to-fp (op mxcsr)
  (declare (xargs :guard (and (integerp op)
                              (n32p mxcsr)))
           (type integer op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cvt-int-to-fp op mxcsr
                           #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*))

       (result (n64 result)))
      (mv flg result mxcsr)))

(defthm n64p-dp-sse-cvt-int-to-fp-1
  (n64p (mv-nth 1 (dp-sse-cvt-int-to-fp op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (dp-sse-cvt-int-to-fp op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (dp-sse-cvt-int-to-fp op mxcsr))
       *2^64*))))

(defthm n32p-dp-sse-cvt-int-to-fp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (dp-sse-cvt-int-to-fp op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-int-to-fp) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (dp-sse-cvt-int-to-fp op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (dp-sse-cvt-int-to-fp op mxcsr))
                *2^32*)))))

(defn sse-cvt-dp-to-sp (op mxcsr)
  (declare (xargs :guard (and (n64p op)
                              (n32p mxcsr)))
           (type (unsigned-byte 64) op)
           (type (unsigned-byte 32) mxcsr))
  (b* (((mv flg result mxcsr)
        (sse-cvt-fp1-to-fp2 op mxcsr
                            #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*
                            #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*))

       (result (n32 result)))
      (mv flg result mxcsr)))

(defthm n32p-sse-cvt-dp-to-sp-1
  (n32p (mv-nth 1 (sse-cvt-dp-to-sp op mxcsr)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 1 (sse-cvt-dp-to-sp op mxcsr))))
   (:linear
    :corollary
    (< (mv-nth 1 (sse-cvt-dp-to-sp op mxcsr))
       *2^32*))))

(defthm n32p-sse-cvt-dp-to-sp-2
  (implies (n32p mxcsr)
           (n32p (mv-nth 2 (sse-cvt-dp-to-sp op mxcsr))))
  :hints (("Goal" :in-theory (e/d (sse-cvt-fp1-to-fp2) nil)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (force (n32p mxcsr))
             (natp (mv-nth 2 (sse-cvt-dp-to-sp op mxcsr)))))
   (:linear
    :corollary
    (implies (force (n32p mxcsr))
             (< (mv-nth 2 (sse-cvt-dp-to-sp op mxcsr))
                *2^32*)))))

(in-theory (disable dp-sse-add/sub/mul/div/max/min
                    dp-sse-sqrt
                    dp-sse-cmp
                    dp-sse-cvt-fp-to-int
                    dp-sse-cvt-int-to-fp
                    sse-cvt-dp-to-sp))

;; ======================================================================
