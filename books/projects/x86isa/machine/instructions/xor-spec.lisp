;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This book contains the specification of the following instructions:
;; xor

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; SPECIFICATION: XOR
;; ======================================================================

(define gpr-xor-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-xor-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits)))


      `(define ,fn-name
         ((dst          :type (unsigned-byte ,result-nbits))
          (src          :type (unsigned-byte ,result-nbits))
          (input-rflags :type (unsigned-byte 32)))
         :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
         :inline t

         (b* ((dst (mbe :logic (n-size ,result-nbits dst)
                        :exec dst))
              (src (mbe :logic (n-size ,result-nbits src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

              ((the (unsigned-byte ,result-nbits) result)
               (mbe :logic (part-select (logxor dst src)
                                        :low 0 :width ,result-nbits)
                    :exec (logxor dst src)))

              (cf 0)
              (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
              ;; AF is undefined.
              (zf (the (unsigned-byte 1) (zf-spec result)))
              (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
              (of 0)

              (output-rflags (the (unsigned-byte 32)
                               (!rflags-slice
                                :cf cf
                                (!rflags-slice
                                 :pf pf
                                 (!rflags-slice
                                  :zf zf
                                  (!rflags-slice
                                   :sf sf
                                   (!rflags-slice
                                    :of of input-rflags)))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              ;; AF is undefined.
              (undefined-flags (!rflags-slice :af 1 0)))

             (mv result output-rflags undefined-flags))

         ///

         (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
           :bound ,result-nbits
           :concl (mv-nth 0 (,fn-name dst src input-rflags))
           :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
           :gen-type t
           :gen-linear t
           :hints-l (("Goal"
                      :in-theory
                      (e/d (unsigned-byte-p)
                           (acl2::unsigned-byte-p-of-logxor)))))

         (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
           :bound 32
           :concl (mv-nth 1 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
           :bound 32
           :concl (mv-nth 2 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t))

      ))

(make-event (gpr-xor-spec-gen-fn 1))
(make-event (gpr-xor-spec-gen-fn 2))
(make-event (gpr-xor-spec-gen-fn 4))
(make-event (gpr-xor-spec-gen-fn 8))

;; ======================================================================
