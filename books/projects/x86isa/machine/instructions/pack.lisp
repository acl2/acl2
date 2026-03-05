; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2026, Kestrel Technology, LLC
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
; Cuong Chau          <ckcuong@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils" :ttags (:undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemmas to verify guards and return types in the pack specification functions.

(defruledl pack-spec-lemma1
  (implies (and (natp total)
                (posp chunk)
                (evenp chunk)
                (equal (mod total chunk) 0))
           (evenp total))
  :enable acl2::evenp-becomes-equal-of-0-and-mod
  :disable acl2::mod-zero)

(defruledl pack-spec-lemma2
  (implies (and (natp total)
                (posp chunk)
                (evenp chunk)
                (equal (mod total chunk) 0))
           (integerp (* 1/2 total)))
  :use pack-spec-lemma1
  :enable evenp)

(defruled pack-spec-lemma3
  (implies (and (posp total)
                (posp chunk)
                (equal (mod total chunk) 0)
                (evenp chunk)
                (> total 0)
                (unsigned-byte-p (- (* 1/2 total)
                                    (* 1/2 chunk))
                                 hi))
           (unsigned-byte-p (* 1/2 total)
                            (logapp (* 1/2 chunk) lo hi)))
  :use (:instance unsigned-byte-p-of-logapp
                  (size1 (* 1/2 total))
                  (size (* 1/2 chunk))
                  (i lo)
                  (j hi))
  :disable (unsigned-byte-p
            unsigned-byte-p-of-logapp)
  :enable (evenp pack-spec-lemma2))

(defruled pack-spec-lemma4
  (implies (and (natp size)
                (unsigned-byte-p (/ size 2) hi))
           (unsigned-byte-p size (logapp (* 1/2 size) lo hi)))
  :use (:instance unsigned-byte-p-of-logapp
                  (size1 size)
                  (size (/ size 2))
                  (i lo)
                  (j hi))
  :disable unsigned-byte-p-of-logapp)

; Specification functions for the pack instructions.

(define packus-spec-one ((total-size natp)
                         (chunk-size posp)
                         (x (unsigned-byte-p total-size x)))
  :guard (and (equal (mod total-size chunk-size) 0)
              (evenp chunk-size))
  :returns (result (unsigned-byte-p (* 1/2 total-size) result)
                   :hyp :guard
                   :hints
                   (("Goal"
                     :induct (packus-spec-one total-size chunk-size x)
                     :in-theory (e/d (pack-spec-lemma2
                                      pack-spec-lemma3)
                                     (unsigned-byte-p)))))
  :parents (packus-spec)
  :short "Specification of packing with unsigned saturation,
          for just one operand."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee packus-spec), for each operand,
     before joining the individual results into the full result:
     the function @(tsee packus-spec) specifies the PACKUS... instructions.")
   (xdoc::p
    "See Figure 4-6 in Intel manual Volume 2 (Feb 2026):
     each 64-bit operand is packed into 32 bits,
     forming half of the final result.
     Here we generalize 64 to @('total-size') and 32 to @('chunk-size'),
     where the former must be a multiple of the latter,
     and where the chunk size must be even.
     Each chunk of the operand @('x') is packed into a half chunk
     (i.e. a value half the size of the chunk,
     e.g. 16 bits for a 32-bit chunk),
     using unsigned saturation on the signed value of the chunk.
     That is, the chunk value is interpreted as signed (see @('x-lo') below),
     and this value is saturated to 0 if negative,
     and to the maximum unsigned value representable in half chunk if larger."))
  (b* (((when (zp total-size)) 0)
       ((unless (mbt (and (posp chunk-size)
                          (evenp chunk-size))))
        0)
       (half-chunk-size (/ chunk-size 2))
       (max-half-chunk-val (1- (expt 2 half-chunk-size)))
       (x-lo (logext chunk-size x))
       (result-lo (cond ((< x-lo 0) 0)
                        ((> x-lo max-half-chunk-val) max-half-chunk-val)
                        (t x-lo)))
       (x-hi (logtail chunk-size x))
       (result-hi (packus-spec-one (- total-size chunk-size) chunk-size x-hi)))
    (logapp half-chunk-size result-lo result-hi))
  :measure (nfix total-size)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable evenp))))

(define packss-spec-one ((total-size natp)
                         (chunk-size posp)
                         (x (unsigned-byte-p total-size x)))
  :guard (and (equal (mod total-size chunk-size) 0)
              (evenp chunk-size))
  :returns (result (unsigned-byte-p (* 1/2 total-size) result)
                   :hyp :guard
                   :hints
                   (("Goal"
                     :induct (packss-spec-one total-size chunk-size x)
                     :in-theory (e/d (pack-spec-lemma2
                                      pack-spec-lemma3)
                                     (unsigned-byte-p)))))
  :parents (packss-spec)
  :short "Specification of packing with signed saturation,
          for just one operand."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee packus-spec-one):
     see that function's documentation first.
     The only difference here is that we do signed saturation,
     i.e. we consider the signed range of each half chunk.
     This function is used in @(tsee packss-spec),
     which is used to specify the PACKSS... instructions."))
  (b* (((when (zp total-size)) 0)
       ((unless (mbt (and (posp chunk-size)
                          (evenp chunk-size))))
        0)
       (half-chunk-size (/ chunk-size 2))
       (max-half-chunk-val (1- (expt 2 half-chunk-size)))
       (x-lo (logext chunk-size x))
       (result-lo (cond ((< x-lo 0) 0)
                        ((> x-lo max-half-chunk-val) max-half-chunk-val)
                        (t x-lo)))
       (x-hi (logtail chunk-size x))
       (result-hi (packss-spec-one (- total-size chunk-size) chunk-size x-hi)))
    (logapp half-chunk-size result-lo result-hi))
  :measure (nfix total-size)
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable evenp))))

(define packus-spec ((total-size natp)
                     (chunk-size posp)
                     (x (unsigned-byte-p total-size x))
                     (y (unsigned-byte-p total-size y)))
  :guard (and (equal (mod total-size chunk-size) 0)
              (evenp chunk-size))
  :returns (result (unsigned-byte-p total-size result)
                   :hyp :guard
                   :hints (("Goal"
                            :do-not-induct t
                            :in-theory (e/d (pack-spec-lemma4
                                             packus-spec-one)
                                            (unsigned-byte-p)))))
  :parents (instruction-semantic-functions)
  :short "Specification of packing with unsigned saturation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the PACKUS... instructions.")
   (xdoc::p
    "Given @('x') and @('y'), each of size @('total-size') in bits,
     we use @(tsee packus-spec) to pack each operand into half bits,
     and then we join the two half results to obtain the full result.
     See Figure 4-6 in Intel manual Volume 2 (Feb 2026);
     here we generalize 64 to @('total-size') and 32 to @('chunk-size')."))
  (logapp (/ total-size 2)
          (packus-spec-one total-size chunk-size x)
          (packus-spec-one total-size chunk-size y))
  :guard-hints (("Goal" :in-theory (enable evenp pack-spec-lemma2))))

(define packss-spec ((total-size natp)
                     (chunk-size posp)
                     (x (unsigned-byte-p total-size x))
                     (y (unsigned-byte-p total-size y)))
  :guard (and (equal (mod total-size chunk-size) 0)
              (evenp chunk-size))
  :returns (result (unsigned-byte-p total-size result)
                   :hyp :guard
                   :hints (("Goal"
                            :do-not-induct t
                            :in-theory (e/d (pack-spec-lemma4
                                             packss-spec-one)
                                            (unsigned-byte-p)))))
  :parents (instruction-semantic-functions)
  :short "Specification of packing with signed saturation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the PACKSS... instructions.")
   (xdoc::p
    "This is similar to @(tsee packus-spec):
     see that function's documentation first.
     The difference is signed saturation instead of unsigned saturation."))
  (logapp (/ total-size 2)
          (packss-spec-one total-size chunk-size x)
          (packss-spec-one total-size chunk-size y))
  :guard-hints (("Goal" :in-theory (enable evenp pack-spec-lemma2))))

; The function packus-spec above generalizes the function packuswb below.
; The latter is for total-size = 128 and chunk-size = 16,
; and uses a recursive macro.
; We leave packuswb, and its use in x86-packuswb-sse, at least for now.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-packuswb-mmx

  :parents (two-byte-opcodes)

  :short "Pack words to bytes with unsigned saturation (MMX variant)."

  :long
  "<code>
  NP 0F 67 /r    PACKUSWB mm, mm/m64
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 64 bits, i.e. 8 bytes.
       (operand-size 8)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the MMX register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ((the (unsigned-byte 4) src1/dst-index) reg)
       ((the (unsigned-byte 64) src1) (mmx src1/dst-index x86))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 64) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*mmx-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result (chunk size = 16, i.e. word).
       (result (packus-spec 64 16 src1 src2))

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-packsswb-mmx

  :parents (two-byte-opcodes)

  :short "Pack words to bytes with signed saturation (MMX variant)."

  :long
  "<code>
  NP 0F 63 /r    PACKSSWB mm, mm/m64
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 64 bits, i.e. 8 bytes.
       (operand-size 8)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the MMX register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ;; Since there are only 8 MMX registers, the REX byte is not used.
       ((the (unsigned-byte 4) src1/dst-index) reg)
       ((the (unsigned-byte 64) src1) (mmx src1/dst-index x86))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the MMX register, or memory operand, specified in Mod and R/M.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 64) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*mmx-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result (chunk size = 16, i.e. word).
       (result (packss-spec 64 16 src1 src2))

       ;; Store the result into the destination register.
       (x86 (!mmx src1/dst-index result x86))
       (x86 (mmx-instruction-updates x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))

    x86)

  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define packuswb ((src1 :type (unsigned-byte 128))
                  (src2 :type (unsigned-byte 128)))
  :returns (result (unsigned-byte-p 128 result))
  :prepwork
  ((defmacro packuswb-helper (n src)
     (if (equal n 8)
       0
       `(logapp 8 (max 0 (min 255 (logext 16 (logtail ,(* n 16) ,src))))
                (packuswb-helper ,(1+ n) ,src)))))
  (b* ((src1 (n128 src1))
       (src2 (n128 src2)))
      (logapp 64 (packuswb-helper 0 src1)
              (packuswb-helper 0 src2))))

(def-inst x86-packuswb-sse
  :parents (two-byte-opcodes)
  :long
  "<code>
  PACKUSWB xmm1, xmm2/m128
  </code>"

  :modr/m t

  :returns (x86 x86p :hyp (x86p x86))
  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))

  :body

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (eql #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ;; The operand size is always 128 bits, i.e. 16 bytes.
       (operand-size 16)

       ;; The first source operand (Operand 1 in the Intel manual)
       ;; is the XMM register specified in Reg.
       ;; This is also the destination operand,
       ;; and thus we obtain the index for later use.
       ((the (unsigned-byte 4) src1/dst-index)
        (reg-index reg rex-byte #.*r*))
       ((the (unsigned-byte 128) src1)
        (xmmi-size operand-size src1/dst-index x86))

       ;; The second source operand (Operand 2 in the Intel manual)
       ;; is the XMM register, or memory operand, specified in Mod and R/M.
       (inst-ac? t) ; Intel Manual Volume 2 Table 2-21 (Dec 2023)
       ((mv flg
            (the (unsigned-byte 128) src2)
            (the (integer 0 4) increment-rip-by)
            ?addr
            x86)
        (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                               #.*xmm-access*
                                               operand-size
                                               inst-ac?
                                               nil ; not a memory operand
                                               seg-reg
                                               p4?
                                               temp-rip
                                               rex-byte
                                               r/m
                                               mod
                                               sib
                                               0 ; no immediate operand
                                               x86))
       ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))

       ;; Increment the instruction pointer in the temp-rip variable.
       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
        (add-to-*ip proc-mode temp-rip increment-rip-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error flg))

       ;; Ensure the instruction is not too long.
       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ;; Calculate the result.
       (result (packuswb src1 src2))

       ;; Store the result into the destination register.
       (x86 (!xmmi-size operand-size src1/dst-index result x86))

       ;; Update the instruction pointer.
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
