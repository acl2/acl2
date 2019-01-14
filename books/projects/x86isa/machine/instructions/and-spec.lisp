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
;; and

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; SPECIFICATION: AND
;; ======================================================================

(define gpr-and-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "GPR-AND-SPEC-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (?cf-spec-fn (mk-name "CF-SPEC" result-nbits))
       (pf-spec-fn (mk-name "PF-SPEC" result-nbits))
       (sf-spec-fn (mk-name "SF-SPEC" result-nbits)))


      `(define ,fn-name
         ((dst          :type (unsigned-byte ,result-nbits))
          (src          :type (unsigned-byte ,result-nbits))
          (input-rflags :type (unsigned-byte 32)))
         :parents (,(mk-name "GPR-ARITH/LOGIC-SPEC-" operand-size))
         :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                                ((tau-system)))))
         :inline t
         :no-function t

         (b* ((dst (mbe :logic (n-size ,result-nbits dst)
                        :exec dst))
              (src (mbe :logic (n-size ,result-nbits src)
                        :exec src))
              (input-rflags (mbe :logic (n32 input-rflags)
                                 :exec input-rflags))

              ((the (unsigned-byte ,result-nbits) result)
               (mbe :logic (part-select (logand dst src)
                                        :low 0 :width ,result-nbits)
                    :exec (logand dst src)))

              (cf 0)
              (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
              ;; AF is undefined
              (zf (the (unsigned-byte 1) (zf-spec result)))
              (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
              (of 0)

              (output-rflags (mbe :logic
                                  (change-rflagsBits
                                   input-rflags
                                   :cf cf
                                   :pf pf
                                   :zf zf
                                   :sf sf
                                   :of of)
                                  :exec
                                  (the (unsigned-byte 32)
                                    (!rflagsBits->cf
                                     cf
                                     (!rflagsBits->pf
                                      pf
                                      (!rflagsBits->zf
                                       zf
                                       (!rflagsBits->sf
                                        sf
                                        (!rflagsBits->of
                                         of
                                         input-rflags))))))))

              (output-rflags (mbe :logic (n32 output-rflags)
                                  :exec output-rflags))

              ;; AF is undefined.
              (undefined-flags (!rflagsBits->af 1 0)))

             (mv result output-rflags undefined-flags))

         ///

         (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
           :bound ,result-nbits
           :concl (mv-nth 0 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-unsigned-byte-p ,(mk-name "MV-NTH-1-" fn-name)
           :bound 32
           :concl (mv-nth 1 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t)

         (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
           :bound 32
           :concl (mv-nth 2 (,fn-name dst src input-rflags))
           :gen-type t
           :gen-linear t))

      ))

(make-event (gpr-and-spec-gen-fn 1))
(make-event (gpr-and-spec-gen-fn 2))
(make-event (gpr-and-spec-gen-fn 4))
(make-event (gpr-and-spec-gen-fn 8))

;; ======================================================================
