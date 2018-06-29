; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This book contains the specification of the following instructions:
;; sub  sbb

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; SPECIFICATION: SUB
;; ======================================================================

;; The SUB instruction performs integer subtraction. It evaluates the
;; result for both signed and unsigned integer operands and sets the
;; OF and CF flags to indicate an overflow in the signed or unsigned
;; result, respectively. The SF flag indicates the sign of the signed
;; result.

;; (def-gl-thm sub-signed-and-unsigned-check
;;   :hyp (and (n32p x)
;;             (n32p y))
;;   :concl (equal (n32 (- (n32-to-i32 x) (n32-to-i32 y)))
;;                 (n32 (- x y)))
;;   :g-bindings `((x (:g-number ,(gl-int 0 2 33)))
;;                 (y (:g-number ,(gl-int 1 2 33)))))

(define gpr-sub-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-sub-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (?cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "sub-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


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

              (signed-raw-result
               (the (signed-byte ,(1+ result-nbits))
                 (- (the (signed-byte ,result-nbits)
                      (,ntoi dst))
                    (the (signed-byte ,result-nbits)
                      (,ntoi src)))))

              (result (the (unsigned-byte ,result-nbits)
                        (n-size ,result-nbits signed-raw-result)))

              (cf (the (unsigned-byte 1) (acl2::bool->bit (< dst src))))
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
           :gen-linear t))

      ))

(make-event (gpr-sub-spec-gen-fn 1))
(make-event (gpr-sub-spec-gen-fn 2))
(make-event (gpr-sub-spec-gen-fn 4))
(make-event (gpr-sub-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: SBB
;; ======================================================================

(define gpr-sbb-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-sbb-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (?cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "sbb-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


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
              (input-cf (the (unsigned-byte 1)
                          (rflags-slice :cf input-rflags)))

              (signed-raw-result
               (the (signed-byte ,(+ 2 result-nbits))
                 (- (the (signed-byte ,result-nbits)
                      (,ntoi dst))
                    (the (signed-byte ,(1+ result-nbits))
                      (+ (the (signed-byte ,result-nbits)
                           (,ntoi src))
                         input-cf)))))

              (result (the (unsigned-byte ,result-nbits)
                        (n-size ,result-nbits signed-raw-result)))

              (cf (the (unsigned-byte 1)
                    (acl2::bool->bit
                     (< dst
                        (the (unsigned-byte ,(1+ result-nbits))
                          (+ input-cf src))))))
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
           :concl (mv-nth 0 (,fn-name dst src cf))
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
           :gen-linear t))

      ))

(make-event (gpr-sbb-spec-gen-fn 1))
(make-event (gpr-sbb-spec-gen-fn 2))
(make-event (gpr-sbb-spec-gen-fn 4))
(make-event (gpr-sbb-spec-gen-fn 8))

;; ======================================================================
