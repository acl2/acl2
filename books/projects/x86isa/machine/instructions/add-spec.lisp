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
