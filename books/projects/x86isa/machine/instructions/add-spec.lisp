;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This book contains the specification of the following instructions:
;; add  adc

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; SPECIFICATION: ADD
;; ======================================================================

(define gpr-add-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-add-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "add-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
         ((dst            :type (unsigned-byte ,result-nbits))
          (src            :type (unsigned-byte ,result-nbits))
          (input-rflags   :type (unsigned-byte 32)))
         :inline t

         :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))

         (b* ((dst (mbe :logic (n-size ,result-nbits dst)
                        :exec dst))
              (src (mbe :logic (n-size ,result-nbits src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

              (raw-result (the (unsigned-byte ,(1+ result-nbits))
                            (+ (the (unsigned-byte ,result-nbits) dst)
                               (the (unsigned-byte ,result-nbits) src))))
              (signed-raw-result
               (the (signed-byte ,(1+ result-nbits))
                 (+ (the (signed-byte ,result-nbits)
                      (,ntoi dst))
                    (the (signed-byte ,result-nbits)
                      (,ntoi src)))))

              (result (the (unsigned-byte ,result-nbits)
                        (n-size ,result-nbits raw-result)))

              (cf (the (unsigned-byte 1) (,cf-spec-fn raw-result)))
              (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
              (af (the (unsigned-byte 1) (,af-spec-fn dst src)))
              (zf (the (unsigned-byte 1) (zf-spec result)))
              (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
              (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

              (output-rflags (the (unsigned-byte 32)
                               (!rflags-slice
                                :cf cf
                                (!rflags-slice
                                 :pf pf
                                 (!rflags-slice
                                  :af af
                                  (!rflags-slice
                                   :zf zf
                                   (!rflags-slice
                                    :sf sf
                                    (!rflags-slice
                                     :of of input-rflags))))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              ;; No undefined flags.
              (undefined-flags 0))

             (mv result output-rflags undefined-flags))

         ///

         (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
           :bound ,result-nbits
           :concl (mv-nth 0 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
           :bound 32
           :concl (mv-nth 1 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
           :bound 32
           :concl (mv-nth 2 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t))))

(make-event (gpr-add-spec-gen-fn 1))
(make-event (gpr-add-spec-gen-fn 2))
(make-event (gpr-add-spec-gen-fn 4))
(make-event (gpr-add-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: ADC
;; ======================================================================

(define gpr-adc-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-adc-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "adc-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
         ((dst           :type (unsigned-byte ,result-nbits))
          (src           :type (unsigned-byte ,result-nbits))
          (input-rflags  :type (unsigned-byte 32)))

         :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
         :inline t

         (b* ((dst (mbe :logic (n-size ,result-nbits dst)
                        :exec dst))
              (src (mbe :logic (n-size ,result-nbits src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))
              (input-cf (the (unsigned-byte 1)
                          (rflags-slice :cf input-rflags)))

              (raw-result (the (unsigned-byte ,(1+ result-nbits))
                            (+
                             (the (unsigned-byte ,result-nbits) dst)
                             (the (unsigned-byte ,result-nbits) src)
                             (the (unsigned-byte 1) input-cf))))
              (signed-raw-result
               (the (signed-byte ,(1+ result-nbits))
                 (+ (the (signed-byte ,result-nbits)
                      (,ntoi dst))
                    (the (signed-byte ,result-nbits)
                      (,ntoi src))
                    (the (unsigned-byte 1)
                      input-cf))))

              (result (the (unsigned-byte ,result-nbits)
                        (n-size ,result-nbits raw-result)))

              (cf (the (unsigned-byte 1) (,cf-spec-fn raw-result)))
              (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
              (af (the (unsigned-byte 1) (,af-spec-fn dst src input-cf)))
              (zf (the (unsigned-byte 1) (zf-spec result)))
              (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
              (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

              (output-rflags (the (unsigned-byte 32)
                               (!rflags-slice
                                :cf cf
                                (!rflags-slice
                                 :pf pf
                                 (!rflags-slice
                                  :af af
                                  (!rflags-slice
                                   :zf zf
                                   (!rflags-slice
                                    :sf sf
                                    (!rflags-slice
                                     :of of input-rflags))))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              (undefined-flags 0))

             (mv result output-rflags undefined-flags))

         ///

         (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
           :bound ,result-nbits
           :concl (mv-nth 0 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
           :bound 32
           :concl (mv-nth 1 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
           :bound 32
           :concl (mv-nth 2 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t))))

(make-event (gpr-adc-spec-gen-fn 1))
(make-event (gpr-adc-spec-gen-fn 2))
(make-event (gpr-adc-spec-gen-fn 4))
(make-event (gpr-adc-spec-gen-fn 8))

;; ======================================================================
