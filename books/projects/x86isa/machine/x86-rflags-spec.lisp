;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-programmer-level-memory")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection rflag-specifications
  :parents (machine)
  :short "Specifications of @('rflags')"
  )

;; ======================================================================

(define general-cf-spec-fn (result-nbits raw-result)
  :long "<p>General @('CF') Specification (Source: Intel Manuals,
  Vol. 1, Section 3.4.3.1):</p>

<p><b>Carry flag</b>   Set if an arithmetic operation generates a
carry or a borrow out of the most-significant bit of the result;
cleared otherwise. This flag indicates an overflow condition for
unsigned-integer arithmetic. It is also used in multiple-precision
arithmetic.</p>"
  :parents (rflag-specifications)
  :inline t
  :guard (and (natp result-nbits)
              (natp raw-result))
  (acl2::bool->bit (not (unsigned-byte-p result-nbits raw-result)))

  ///

  (defthm-usb n01p-general-cf-spec-fn
    :hyp t
    :bound 1
    :concl (general-cf-spec-fn result-nbits raw-result)
    :gen-linear t
    :gen-type t))

(define cf-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "cf-spec" result-nbits)
     ((raw-result :type (unsigned-byte ,(1+ result-nbits))))
     :inline t
     :parents (rflag-specifications)
     (acl2::bool->bit (mbe :logic (not (unsigned-byte-p ,result-nbits raw-result))
                           :exec (not (< raw-result ,(expt 2 result-nbits)))))

     ///

     (defthm-usb ,(mk-name "n01p-cf-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "cf-spec" result-nbits) raw-result)
       :gen-linear t
       :gen-type t)))

(make-event (cf-spec-gen-fn  8))
(make-event (cf-spec-gen-fn 16))
(make-event (cf-spec-gen-fn 32))
(make-event (cf-spec-gen-fn 64))

(defmacro general-cf-spec (result-nbits raw-result)
  (cond ((eql result-nbits 8)
         `(cf-spec8 ,raw-result))
        ((eql result-nbits 16)
         `(cf-spec16 ,raw-result))
        ((eql result-nbits 32)
         `(cf-spec32 ,raw-result))
        ((eql result-nbits 64)
         `(cf-spec64 ,raw-result))
        (t
         `(general-cf-spec-fn ,result-nbits ,raw-result))))

(add-macro-alias general-cf-spec general-cf-spec-fn)

;; ======================================================================

(define general-of-spec-fn (result-nbits signed-raw-result)
  :guard (and (natp result-nbits)
              (integerp signed-raw-result))
  :long "<p>General @('OF') Specification (Source: Intel Manuals,
  Vol. 1, Section 3.4.3.1):</p>

<p><b>Overflow flag</b>   Set if the integer result is too large a
positive number or too small a negative number (excluding the
sign-bit) to fit in the destination operand; cleared otherwise. This
flag indicates an overflow condition for signed-integer (two s
complement) arithmetic.</p>"
  :parents (rflag-specifications)

  (acl2::bool->bit (not (signed-byte-p result-nbits signed-raw-result)))

  ///

  (defthm-usb n01p-general-of-spec-fn
    :hyp t
    :bound 1
    :concl (general-of-spec-fn result-nbits signed-raw-result)))

(define of-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "of-spec" result-nbits)
     ((signed-raw-result :type (signed-byte ,(1+ result-nbits))))
     :inline t
     :parents (rflag-specifications)
     (acl2::bool->bit (mbe :logic (not (signed-byte-p ,result-nbits signed-raw-result))
                           :exec (or
                                  (not (<= ,(- (expt 2 (1- result-nbits))) signed-raw-result))
                                  (not (< signed-raw-result ,(expt 2 (1- result-nbits)))))))

     ///

     (defthm-usb ,(mk-name "n01p-of-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "of-spec" result-nbits) signed-raw-result)
       :gen-type t
       :gen-linear t)))

(make-event (of-spec-gen-fn  8))
(make-event (of-spec-gen-fn 16))
(make-event (of-spec-gen-fn 32))
(make-event (of-spec-gen-fn 64))

(defmacro general-of-spec (result-nbits signed-raw-result)
  (cond ((eql result-nbits 8)
         `(of-spec8 ,signed-raw-result))
        ((eql result-nbits 16)
         `(of-spec16 ,signed-raw-result))
        ((eql result-nbits 32)
         `(of-spec32 ,signed-raw-result))
        ((eql result-nbits 64)
         `(of-spec64 ,signed-raw-result))
        (t
         `(general-of-spec-fn ,result-nbits ,signed-raw-result))))

(add-macro-alias general-of-spec general-of-spec-fn)

;; ======================================================================

(define zf-spec
  ;; CCL generates great code for this function, even without type
  ;; declarations.
  ((result :type (integer 0 *)))
  :inline t
  :long "<p>General @('ZF') Specification (Source: Intel Manuals,
  Vol. 1, Section 3.4.3.1):</p>

<p><b>Zero flag</b>   Set if the result is zero; cleared
otherwise.</p>"
  :parents (rflag-specifications)

  (if (equal result 0) 1 0)
  ///

  (defthm-usb n01p-zf-spec
    :hyp t
    :bound 1
    :concl (zf-spec result)
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; [Shilpi]: I could have put the theorems preceding the define of
;; pf-spec inside its :prepwork, but I believe that these theorems can
;; be useful later on too.  Putting them outside the define makes them
;; more visible.

(local
 (encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm logbitp-and-loghead
    (implies (integerp x)
             (equal (acl2::bool->bit (logbitp 0 x))
                    (loghead 1 x)))
    :hints (("Goal" :in-theory
             (e/d (acl2::bool->bit
                   evenp oddp
                   logbitp
                   loghead)
                  ()))))

  (defthm logbitp-and-logtail
    (implies (unsigned-byte-p (1+ n) x)
             (equal (acl2::bool->bit (logbitp n x))
                    (logtail n x)))
    :hints (("Goal" :in-theory
             (e/d (acl2::bool->bit
                   evenp oddp
                   logbitp
                   logtail
                   nfix)
                  ()))))

  ))

(defthm logcount-and-loghead
  (implies (and (integerp x)
                (natp n))
           (<= (logcount (loghead n x)) n))
  :hints (("Goal" :in-theory
           (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
                 (logcount loghead)))))


(defthm logcount-bound
  (<= (logcount x) (integer-length x))
  :hints (("Goal" :in-theory
           (e/d* (acl2::ihsext-inductions
                  acl2::ihsext-recursive-redefs)
                 (logcount))))
  :rule-classes :linear)

(encapsulate
 ()
 (local (include-book "centaur/bitops/signed-byte-p" :dir :system))

 (defthm unsigned-byte-p-and-integer-length
   (implies (and (unsigned-byte-p n x)
                 (natp n))
            (<= (integer-length x) n))
   :hints (("Goal" :in-theory (e/d* (acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs)
                                    ())))
   :rule-classes :linear)
 )


(define bitcount8
  ((x :type (unsigned-byte 8)))
  :measure (integer-length x)
  :inline t
  :verify-guards nil
  :enabled t
  (if (zp x)
      0
    (+ (the (unsigned-byte 1)
         (mbe :logic
              ;; (logcar x)
              (loghead 1 x)
              :exec  (logand 1 x)))
       (the (integer 0 8)
         (bitcount8
          (the (unsigned-byte 8)
            (mbe :logic
                 ;; (logcdr x)
                 (logtail 1 x)
                 :exec  (ash x -1)))))))
  ///


  (defthm bitcount8-and-logcount
    (implies (unsigned-byte-p 8 x)
             (equal (bitcount8 x)
                    (logcount x)))
    :hints (("Goal" :in-theory
             (e/d* (acl2::ihsext-inductions
                    acl2::ihsext-recursive-redefs)
                   (logcount)))))

  (local
   (defthm logtail-1-bound-linear
     (implies (and (unsigned-byte-p 8 x)
                   (unsigned-byte-p 7 (logtail 1 x)))
              (<= (integer-length (logtail 1 x)) 7))
     :hints (("Goal" :use ((:instance unsigned-byte-p-and-integer-length
                                      (x (logtail 1 x))
                                      (n 7)))
              :in-theory (e/d ()
                              (unsigned-byte-p-and-integer-length))))
     :rule-classes :linear))

  (verify-guards bitcount8$inline))

(define pf-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "pf-spec" result-nbits)
     ((result :type (unsigned-byte ,result-nbits)))
     :parents (rflag-specifications)
     :inline t
     :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

     (mbe :logic (acl2::bool->bit (not
                                   (logbitp
                                    0
                                    (logcount
                                     ,(if (equal result-nbits 8)
                                          `result
                                        `(loghead 8 result))))))
          :exec  (if (eql (logand 1
                                  (the (integer 0 8)
                                    (bitcount8
                                     (the (unsigned-byte 8)
                                       ,(if (equal result-nbits 8)
                                            `result
                                          `(logand 255 result))))))
                          0)
                     1 0))

     ///

     (defthm-usb ,(mk-name "n01p-pf-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "pf-spec" result-nbits) result)
       :gen-type t
       :gen-linear t)))

(make-event (pf-spec-gen-fn  8))
(make-event (pf-spec-gen-fn 16))
(make-event (pf-spec-gen-fn 32))
(make-event (pf-spec-gen-fn 64))

(define general-pf-spec-fn
  ((result-nbits :type (member 8 16 32 64))
   (result       :type (integer 0 *)))
  :long "<p>General @('PF') Specification (Source: Intel Manuals,
  Vol. 1, Section 3.4.3.1):</p>

<p><b>Parity flag</b>   Set if the least-significant byte of the
result contains an even number of 1 bits; cleared otherwise.</p>"
  :parents (rflag-specifications)
  :inline t
  :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
  :guard (unsigned-byte-p result-nbits result)
  (mbe :logic (acl2::bool->bit (not (logbitp 0 (logcount (loghead 8 result)))))
       :exec  (if (eql (logand 1
                               (the (integer 0 8)
                                 (bitcount8
                                  (the (unsigned-byte 8)
                                    (logand 255
                                            (if (eql result-nbits 64)
                                                result
                                              (the (unsigned-byte 32)
                                                result)))))))
                       0)
                  1 0))

  ///

  (defthm-usb n01p-general-pf-spec-fn
    :hyp t
    :bound 1
    :concl (general-pf-spec-fn result-nbits result)
    :gen-type t
    :gen-linear t))

(defmacro general-pf-spec (result-nbits result)
  (cond ((eql result-nbits 8)
         `(pf-spec8 ,result))
        ((eql result-nbits 16)
         `(pf-spec16 ,result))
        ((eql result-nbits 32)
         `(pf-spec32 ,result))
        ((eql result-nbits 64)
         `(pf-spec64 ,result))
        (t
         `(general-pf-spec-fn ,result-nbits ,result))))

(add-macro-alias general-pf-spec general-pf-spec-fn)

;; ======================================================================

(define sf-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "sf-spec" result-nbits)
     ((result       :type (unsigned-byte ,result-nbits)))
     :inline t

     :parents (rflag-specifications)

     (mbe
      :logic
      (part-select result :low ,(1- result-nbits) :width 1)
      :exec
      (the (unsigned-byte 1) (ash result ,(- (1- result-nbits)))))

     ///

     (defthm-usb ,(mk-name "n01p-sf-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "sf-spec" result-nbits) result)
       :gen-type t
       :gen-linear t)
     ))

(make-event (sf-spec-gen-fn  8))
(make-event (sf-spec-gen-fn 16))
(make-event (sf-spec-gen-fn 32))
(make-event (sf-spec-gen-fn 64))

(define general-sf-spec-fn
  ((result-nbits :type (member 8 16 32 64))
   (result       :type (integer 0 *)))
  :inline t
  :guard (unsigned-byte-p result-nbits result)
  :long "<p>General @('SF') Specification (Source: Intel Manuals,
  Vol. 1, Section 3.4.3.1):</p>

<p><b>Sign flag</b>   Set equal to the most-significant bit of the
result, which is the sign bit of a signed integer. (0 indicates a
positive value and 1 indicates a negative value.)</p>"
  :parents (rflag-specifications)

  (mbe
   :logic
   (part-select result :low (1- result-nbits) :width 1)
   :exec
   (the (unsigned-byte 1)
     (ash
      (if (eql result-nbits 64)
          result
        (the (unsigned-byte 50) result))
      (the (integer -63 0)
        (- (the (integer 0 63)
             (1- (the (integer 0 64) result-nbits))))))))
  ///

  (defthm-usb n01p-general-sf-spec-fn
    :hyp t
    :bound 1
    :concl (general-sf-spec-fn result-nbits result)
    :gen-type t
    :gen-linear t)
  )

(defmacro general-sf-spec (result-nbits result)
  (cond ((eql result-nbits 8)
         `(sf-spec8 ,result))
        ((eql result-nbits 16)
         `(sf-spec16 ,result))
        ((eql result-nbits 32)
         `(sf-spec32 ,result))
        ((eql result-nbits 64)
         `(sf-spec64 ,result))
        (t
         `(general-sf-spec-fn ,result-nbits ,result))))

(add-macro-alias general-sf-spec general-sf-spec-fn)

;; ======================================================================

;; Instruction-specific AF specification:

(define add-af-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "add-af-spec" result-nbits)
     ((dst         :type (unsigned-byte ,result-nbits))
      (src         :type (unsigned-byte ,result-nbits)))
     :inline t
     :parents (rflag-specifications)

     (b* (((the (unsigned-byte 4) dst-3-0)
           (mbe :logic (part-select dst   :low 0 :width 4)
                :exec  (logand #xF dst)))
          ((the (unsigned-byte 4) src-3-0)
           (mbe :logic (part-select src   :low 0 :width 4)
                :exec  (logand #xF src)))

          (add
           (the (unsigned-byte 5)
             (+ (the (unsigned-byte 4) dst-3-0)
                (the (unsigned-byte 4) src-3-0))))

          (af (the (unsigned-byte 1) (bool->bit (< #xF add)))))

         af)

     ///

     (defthm-usb ,(mk-name "n01p-add-af-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "add-af-spec" result-nbits) dst src)
       :gen-linear t
       :gen-type t)))

(make-event (add-af-spec-gen-fn  8))
(make-event (add-af-spec-gen-fn 16))
(make-event (add-af-spec-gen-fn 32))
(make-event (add-af-spec-gen-fn 64))

(defmacro add-af-spec (result-nbits dst src)
  (cond ((eql result-nbits 8)
         `(add-af-spec8  ,dst ,src))
        ((eql result-nbits 16)
         `(add-af-spec16  ,dst ,src))
        ((eql result-nbits 32)
         `(add-af-spec32  ,dst ,src))
        (t
         `(add-af-spec-fn
           ,result-nbits ,dst ,src))))

(define sub-af-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "sub-af-spec" result-nbits)
     ((dst         :type (unsigned-byte ,result-nbits))
      (src         :type (unsigned-byte ,result-nbits)))
     :inline t
     :parents (rflag-specifications)

     (b* (((the (unsigned-byte 4) dst-3-0)
           (mbe :logic (part-select dst   :low 0 :width 4)
                :exec  (logand #xF dst)))
          ((the (unsigned-byte 4) src-3-0)
           (mbe :logic (part-select src   :low 0 :width 4)
                :exec  (logand #xF src)))

          (sub
           (the (signed-byte 5)
             (- (the (unsigned-byte 4) dst-3-0)
                (the (unsigned-byte 4) src-3-0))))

          (af (the (unsigned-byte 1) (bool->bit (< sub 0)))))

         af)

     ///

     (defthm-usb ,(mk-name "n01p-sub-af-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "sub-af-spec" result-nbits)
                dst src)
       :gen-linear t
       :gen-type t)))

(make-event (sub-af-spec-gen-fn  8))
(make-event (sub-af-spec-gen-fn 16))
(make-event (sub-af-spec-gen-fn 32))
(make-event (sub-af-spec-gen-fn 64))

(defmacro sub-af-spec
  (result-nbits dst src)
  (cond ((eql result-nbits 8)
         `(sub-af-spec8  ,dst ,src))
        ((eql result-nbits 16)
         `(sub-af-spec16  ,dst ,src))
        ((eql result-nbits 32)
         `(sub-af-spec32  ,dst ,src))
        (t
         `(sub-af-spec-fn
            ,result-nbits ,dst ,src))))

(define adc-af-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "adc-af-spec" result-nbits)
     ((dst         :type (unsigned-byte ,result-nbits))
      (src         :type (unsigned-byte ,result-nbits))
      (cf          :type (unsigned-byte 1)))
     :inline t
     :parents (rflag-specifications)

     (b* (((the (unsigned-byte 4) dst-3-0)
           (mbe :logic (part-select dst   :low 0 :width 4)
                :exec  (logand #xF dst)))
          ((the (unsigned-byte 4) src-3-0)
           (mbe :logic (part-select src   :low 0 :width 4)
                :exec  (logand #xF src)))

          (adc
           (the (unsigned-byte 6)
             (+ (the (unsigned-byte 4) dst-3-0)
                (the (unsigned-byte 4) src-3-0)
                (the (unsigned-byte 1) cf))))

          (af (the (unsigned-byte 1) (bool->bit (< #xF adc)))))

         af)

     ///

     (defthm-usb ,(mk-name "n01p-adc-af-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "adc-af-spec" result-nbits)
                dst src cf)
       :gen-linear t
       :gen-type t)))

(make-event (adc-af-spec-gen-fn  8))
(make-event (adc-af-spec-gen-fn 16))
(make-event (adc-af-spec-gen-fn 32))
(make-event (adc-af-spec-gen-fn 64))

(defmacro adc-af-spec
  (result-nbits dst src cf)
  (cond ((eql result-nbits 8)
         `(adc-af-spec8  ,dst ,src ,cf))
        ((eql result-nbits 16)
         `(adc-af-spec16  ,dst ,src ,cf))
        ((eql result-nbits 32)
         `(adc-af-spec32  ,dst ,src ,cf))
        (t
         `(adc-af-spec-fn
           ,result-nbits ,dst ,src ,cf))))

(define sbb-af-spec-gen-fn (result-nbits)
  :verify-guards nil

  `(define ,(mk-name "sbb-af-spec" result-nbits)
     ((dst         :type (unsigned-byte ,result-nbits))
      (src         :type (unsigned-byte ,result-nbits))
      (cf          :type (unsigned-byte 1)))
     :inline t
     :parents (rflag-specifications)

     (b* (((the (unsigned-byte 4) dst-3-0)
           (mbe :logic (part-select dst   :low 0 :width 4)
                :exec  (logand #xF dst)))
          ((the (unsigned-byte 4) src-3-0)
           (mbe :logic (part-select src   :low 0 :width 4)
                :exec  (logand #xF src)))

          (sbb
           (- (the (unsigned-byte 4) dst-3-0)
              (+ (the (unsigned-byte 4) src-3-0)
                 (the (unsigned-byte 4) cf))))

          (af (the (unsigned-byte 1) (bool->bit (< sbb 0)))))

         af)

     ///

     (defthm-usb ,(mk-name "n01p-sbb-af-spec" result-nbits)
       :hyp t
       :bound 1
       :concl (,(mk-name "sbb-af-spec" result-nbits)
                dst src cf)
       :gen-linear t
       :gen-type t)))

(make-event (sbb-af-spec-gen-fn  8))
(make-event (sbb-af-spec-gen-fn 16))
(make-event (sbb-af-spec-gen-fn 32))
(make-event (sbb-af-spec-gen-fn 64))

(defmacro sbb-af-spec
  (result-nbits dst src cf)
  (cond ((eql result-nbits 8)
         `(sbb-af-spec8  ,dst ,src ,cf))
        ((eql result-nbits 16)
         `(sbb-af-spec16  ,dst ,src ,cf))
        ((eql result-nbits 32)
         `(sbb-af-spec32  ,dst ,src ,cf))
        (t
         `(sbb-af-spec-fn
            ,result-nbits ,dst ,src ,cf))))

;; ======================================================================
