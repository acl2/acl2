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
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

;; This book contains the specification of the following instructions:
;; sal  sar  shl  shr
;; shld shrd

(in-package "X86ISA")

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "centaur/bitops/fast-rotate" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (in-theory (e/d ()
                       (bitops::logand-with-negated-bitmask
                        force (force)))))

;; Note: SRC (for SAL/SAR/SHL/SHR) or CNT (for SHRD) operand is either an
;; (unsigned-byte 6) or (unsigned-byte 5) since it is masked before the actual
;; rotate or shift operations.

;; ----------------------------------------------------------------------

;; Shifts:

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local
 (defthm logbitp-and-logtail-thm
   (implies (and (bind-free
                  (list (list (cons 'n ''8))
                        (list (cons 'n ''16))
                        (list (cons 'n ''32))
                        (list (cons 'n ''64)))
                  (n))
                 (natp dst)
                 (< dst (expt 2 n))
                 (natp n)
                 (natp m)
                 (< m n))
            (equal (bool->bit (logbitp m dst))
                   (logand 1 (logtail m dst))))
   :hints (("Goal" :in-theory (e/d* (bool->bit
                                     acl2::logtail**
                                     acl2::ihsext-inductions
                                     acl2::unsigned-byte-p**)
                                    (unsigned-byte-p))))))

(local (in-theory (e/d (loghead-to-logand
                        acl2::bitp)
                       (bitops::logand-with-bitmask))))

(defthm logand-2^32-1-rflagsbits
  (b* ((rflagsbits (rflagsbits cf res1 pf res2
                               af res3 zf sf tf intf df of iopl
                               nt res4 rf vm ac vif vip id res5)))
    (equal (logand #xFFFFFFFF rflagsbits)
           rflagsbits))
  :hints (("Goal"
           :use ((:instance rflagsbits-p-of-rflagsbits))
           :in-theory (e/d (rflagsbits-p) (rflagsbits-p-of-rflagsbits
                                           unsigned-byte-p)))))

;;;;;;;;;; SAL/SHR:

(define sal/shl-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (neg-size-1 (- size-1))
       (fn-name (mk-name "SAL/SHL-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte 6)
             "Note that @('src') is masked appropriately
              by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              (unsigned-byte-p
                                               (tau-system)))))
       :parents (sal/shl-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (raw-result (ash dst src))
            (result (the (unsigned-byte ,size) (n-size ,size raw-result)))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags affected.
                (mv input-rflags 0))

               (1
                ;; All flags, but AF, are changed accordingly. AF is
                ;; undefined.
                (b* ((cf
                      ;; CF contains the last bit shifted out of the operand.
                      (mbe
                       :logic (part-select
                               dst
                               :low ,size-1 ;; (- ,size src)
                               :width 1)
                       :exec
                       (the (unsigned-byte 1)
                            (logand 1
                                    (the (unsigned-byte ,size)
                                         (ash (the (unsigned-byte ,size) dst)
                                              ,neg-size-1))))))
                     (pf (general-pf-spec ,size result))
                     ;; AF is undefined.
                     (zf (zf-spec result))
                     (sf (general-sf-spec ,size result))
                     (of
                      ;; OF is set when the top two bits of the original
                      ;; operand are the same.
                      (b-xor cf
                             (mbe :logic (logbit ,size-1 result)
                                  :exec (the (unsigned-byte 1)
                                             (logand 1
                                                     (the (unsigned-byte 1)
                                                          (ash (the (unsigned-byte ,size)
                                                                    result)
                                                               ,neg-size-1)))))))

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

                     (undefined-flags (!rflagsBits->af 1 0)))

                  (mv output-rflags undefined-flags)))

               (otherwise
                (if (<= ,size src)
                    ;; CF is undefined for SHL and SHR where the src
                    ;; is >= the width of the destination operand. OF and
                    ;; AF are also undefined.  Other flags are affected as
                    ;; usual.
                    (b* ( ;; CF is undefined.
                         (pf (general-pf-spec ,size result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec ,size result))
                         ;; OF is undefined.

                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->pf
                                                   pf
                                                   (!rflagsBits->zf
                                                    zf
                                                    (!rflagsBits->sf
                                                     sf
                                                     input-rflags))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :cf 1
                                                :af 1
                                                :of 1)
                                               :exec
                                               (!rflagsBits->cf
                                                1
                                                (!rflagsBits->af
                                                 1
                                                 (!rflagsBits->of
                                                  1 0))))))
                      (mv output-rflags undefined-flags))

                  ;; OF and AF are undefined. Other flags are affected as
                  ;; usual.
                  (b* ((cf
                        ;; CF contains the last bit shifted out
                        ;; of the operand.
                        (part-select dst :low (- ,size src) :width 1))
                       (pf (general-pf-spec ,size result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec ,size result))
                       ;; OF is undefined.

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf)
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
                                                    input-rflags)))))))

                       (undefined-flags (mbe :logic
                                             (change-rflagsBits
                                              0
                                              :af 1
                                              :of 1)
                                             :exec
                                             (!rflagsBits->af
                                              1
                                              (!rflagsBits->of
                                               1
                                               0)))))
                    (mv output-rflags undefined-flags))))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags))

            (undefined-flags (mbe :logic (n32 undefined-flags)
                                  :exec undefined-flags)))

         (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
         :bound ,size
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
         :gen-linear t))))

(make-event (sal/shl-spec-gen  8))
(make-event (sal/shl-spec-gen 16))
(make-event (sal/shl-spec-gen 32))
(make-event (sal/shl-spec-gen 64))

(define sal/shl-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
              (case size
                (1  (n08p dst))
                (2  (n16p dst))
                (4  (n32p dst))
                (8  (n64p dst))
                (otherwise nil)))

  :inline t
  :no-function t

  :parents (instruction-semantic-functions)

  :short "Specification for the @('SAL/SHL') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference
\(N-Z\).</p>

<p>The shift arithmetic left \(SAL\) and shift logical left \(SHL\)
instructions perform the same operation; they shift the bits in the
destination operand to the left \(toward more significant bit
locations\). For each shift count, the most significant bit of the
destination operand is shifted into the CF flag, and the least
significant bit is cleared.  The OF flag is affected only on 1-bit
shifts. For left shifts, the OF flag is set to 0 if the
most-significant bit of the result is the same as the CF flag (that
is, the top two bits of the original operand were the same);
otherwise, it is set to 1.</p>"

  (case size
    (1 (sal/shl-spec-8  dst src input-rflags))
    (2 (sal/shl-spec-16 dst src input-rflags))
    (4 (sal/shl-spec-32 dst src input-rflags))
    (8 (sal/shl-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-sal/shl-spec
    (natp (mv-nth 0 (sal/shl-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-sal/shl-spec
    :bound 32
    :concl (mv-nth 1 (sal/shl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-sal/shl-spec
    :bound 32
    :concl (mv-nth 2 (sal/shl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;;;;;;;;;; SHR:

(define shr-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (size+1 (1+ size))
       (neg-size-1 (- size-1))
       (fn-name (mk-name "SHR-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte 6)
             "Note that @('src') is masked appropriately
              by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :parents (shr-spec)
       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              (unsigned-byte-p
                                               (tau-system)))))

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (neg-src (the (signed-byte ,size+1) (- src)))
            (raw-result (the (unsigned-byte ,size)
                             (ash
                              (the (unsigned-byte ,size) dst)
                              (the (signed-byte ,size+1) neg-src))))
            (result (the (unsigned-byte ,size) (n-size ,size raw-result)))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags affected.
                (mv input-rflags 0))

               (1
                (b*
                    ((cf (mbe :logic (part-select dst :low 0 :width 1)
                              :exec (the (unsigned-byte 1)
                                         (logand 1 (the (unsigned-byte ,size)
                                                        dst)))))
                     (pf (general-pf-spec ,size result))
                     ;; AF is undefined.
                     (zf (zf-spec result))
                     (sf (general-sf-spec ,size result))
                     (of (mbe :logic (part-select dst :low ,size-1 :width 1)
                              :exec  (the (unsigned-byte 1)
                                          (ash (the (unsigned-byte ,size) dst)
                                               ,neg-size-1))))

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
                     (undefined-flags (the (unsigned-byte 32)
                                           (!rflagsBits->af 1 0))))
                  (mv output-rflags undefined-flags)))

               (otherwise
                (if (<= ,size src)
                    (b* (
                         ;; CF is undefined.
                         (pf (general-pf-spec ,size result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec ,size result))
                         ;; OF is undefined.
                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->pf
                                                   pf
                                                   (!rflagsBits->zf
                                                    zf
                                                    (!rflagsBits->sf
                                                     sf
                                                     input-rflags))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :cf 1
                                                :af 1
                                                :of 1)
                                               :exec
                                               (the (unsigned-byte 32)
                                                    (!rflagsBits->cf
                                                     1
                                                     (!rflagsBits->af
                                                      1
                                                      (!rflagsBits->of
                                                       1
                                                       0)))))))

                      (mv output-rflags undefined-flags))

                  (b* ((cf (mbe :logic (part-select dst :low (1- src) :width 1)
                                :exec (let* ((shft
                                              (the (signed-byte ,size)
                                                   (- 1
                                                      (the (unsigned-byte ,size) src)))))
                                        (the (unsigned-byte 1)
                                             (logand
                                              1
                                              (the (unsigned-byte ,size)
                                                   (ash
                                                    (the (unsigned-byte ,size) dst)
                                                    (the (signed-byte ,size) shft))))))))
                       (pf (general-pf-spec ,size result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec ,size result))
                       ;; OF is undefined.

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf)
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
                                                    input-rflags)))))))

                       (undefined-flags (mbe :logic
                                             (change-rflagsBits
                                              0
                                              :af 1
                                              :of 1)
                                             :exec
                                             (!rflagsBits->af
                                              1
                                              (!rflagsBits->of
                                               1 0)))))
                    (mv output-rflags undefined-flags))))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags))

            (undefined-flags (mbe :logic (n32 undefined-flags)
                                  :exec undefined-flags)))

         (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
         :bound ,size
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
         :gen-linear t))))

(local
 (defthm logand-1-and-logtail-thm
   (implies (and (unsigned-byte-p (1+ n) dst)
                 (natp n))
            (equal (logand 1 (logtail n dst))
                   (logtail n dst)))
   :hints (("Goal" :in-theory (e/d* (bool->bit
                                     acl2::logtail**
                                     acl2::ihsext-inductions
                                     acl2::unsigned-byte-p**)
                                    (unsigned-byte-p))))))

(make-event (shr-spec-gen  8))
(make-event (shr-spec-gen 16))
(make-event (shr-spec-gen 32))
(make-event (shr-spec-gen 64))

(define shr-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (unsigned-byte-p 6 src)
              (case size
                (1 (n08p dst))
                (2 (n16p dst))
                (4 (n32p dst))
                (8 (n64p dst))
                (otherwise nil)))

  :inline t
  :no-function t

  :parents (instruction-semantic-functions)

  :short "Specification for the @('SHR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference \(N-Z\).</p>

<p>The shift arithmetic right \(SAR\) and shift logical right \(SHR\)
instructions shift the bits of the destination operand to the right
\(toward less significant bit locations\). For each shift count, the
least significant bit of the destination operand is shifted into the
CF flag, and the most significant bit is either set or cleared
depending on the instruction type. The SHR instruction clears the most
significant bit (see Figure 7-8 in the Intel 64 and IA-32
Architectures Software Developer s Manual, Volume 1)... The OF flag is
affected only on 1-bit shifts. For the SAR instruction, the OF flag is
cleared for all 1-bit shifts. For the SHR instruction, the OF flag is
set to the most-significant bit of the original operand.</p>"

  (case size
    (1 (shr-spec-8  dst src input-rflags))
    (2 (shr-spec-16 dst src input-rflags))
    (4 (shr-spec-32 dst src input-rflags))
    (8 (shr-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-shr-spec
    (natp (mv-nth 0 (shr-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-shr-spec
    :bound 32
    :concl (mv-nth 1 (shr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-shr-spec
    :bound 32
    :concl (mv-nth 2 (shr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;;;;;;;;;; SAR:

;; (local
;;  (defthm logand-identity
;;    (implies (and (equal 2^size-1 (1- (expt 2 size)))
;;                  (unsigned-byte-p size i))
;;             (equal (logand 2^size-1 i) i))
;;    :hints (("Goal" :in-theory (e/d ()
;;                                    (loghead-to-logand))
;;             :use ((:instance loghead-to-logand
;;                              (n size) (x i)))))))

(define sar-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size+1 (1+ size))
       (size-1 (1- size))
       (neg-size-1 (- size-1))
;       (size-mask (1- (expt 2 size)))
       (fn-name (mk-name "SAR-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte 6)
             "Note that @('src') is masked appropriately
              by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :parents (sar-spec)       
       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              (unsigned-byte-p
                                               (tau-system)))))
       :prepwork
       ((local
         (defthm sar-spec-helper
           (implies (unsigned-byte-p ,size dst)
                    (equal (logand ,(1- (expt 2 size)) (logtail src dst))
                           (logtail src dst)))
           :hints (("Goal"
                    :do-not-induct t
                    :use ((:instance unsigned-byte-p-of-logtail
                                     (size1 ,size)
                                     (size src)
                                     (i dst)))
                    :in-theory (e/d* ()
                                     (unsigned-byte-p
                                      unsigned-byte-p-of-logtail)))))))

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (neg-src (the (signed-byte ,size+1) (- src)))
            (raw-result-not-sign-extended
             (the (unsigned-byte ,size)
                  (ash
                   (the (unsigned-byte ,size) dst)
                   (the (signed-byte ,size+1) neg-src))))
            (raw-result
             (if (eql (mbe :logic (logbit ,size-1 dst)
                           :exec (logand 1
                                         (the (unsigned-byte 1)
                                              (ash (the (unsigned-byte ,size)
                                                        dst)
                                                   ,neg-size-1))))
                      1)
                 (loghead ,size
                          (ash
                           (mbe :logic (logext ,size dst)
                                :exec (bitops::fast-logext ,size dst))
                           neg-src))
;                   (the (unsigned-byte ,size)
;                     (logior ,size-mask raw-result-not-sign-extended))
               raw-result-not-sign-extended))
            (result (mbe :logic (n-size ,size raw-result)
                         :exec raw-result))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags affected.
                (mv input-rflags 0))

               (1
                (b* ((cf (mbe :logic (part-select dst :low 0 :width 1)
                              :exec (the (unsigned-byte 1)
                                         (logand 1 (the (unsigned-byte ,size)
                                                        dst)))))
                     (pf (general-pf-spec ,size result))
                     ;; AF is undefined.
                     (zf (zf-spec result))
                     (sf (general-sf-spec ,size result))
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

                     (undefined-flags
                      (the (unsigned-byte 32)
                           (!rflagsBits->af 1 0))))
                  (mv output-rflags undefined-flags)))

               (otherwise
                (if (<= ,size src)
                    (b* (
                         ;; CF is undefined.
                         (pf (general-pf-spec ,size result))
                         ;; AF is undefined.
                         (zf (zf-spec result))
                         (sf (general-sf-spec ,size result))
                         ;; OF is undefined.
                         (output-rflags (mbe :logic
                                             (change-rflagsBits
                                              input-rflags
                                              :pf pf
                                              :zf zf
                                              :sf sf)
                                             :exec
                                             (the (unsigned-byte 32)
                                                  (!rflagsBits->pf
                                                   pf
                                                   (!rflagsBits->zf
                                                    zf
                                                    (!rflagsBits->sf
                                                     sf
                                                     input-rflags))))))

                         (undefined-flags (mbe :logic
                                               (change-rflagsBits
                                                0
                                                :cf 1
                                                :af 1
                                                :of 1)
                                               :exec
                                               (the (unsigned-byte 32)
                                                    (!rflagsBits->cf
                                                     1
                                                     (!rflagsBits->af
                                                      1
                                                      (!rflagsBits->of
                                                       1
                                                       0)))))))
                      (mv output-rflags undefined-flags))

                  (b* ((cf (mbe :logic (part-select dst :low (1- src) :width 1)
                                :exec (let* ((shft
                                              (the (signed-byte ,size)
                                                   (- 1
                                                      (the (unsigned-byte ,size) src)))))
                                        (the (unsigned-byte 1)
                                             (logand
                                              1
                                              (the (unsigned-byte ,size)
                                                   (ash
                                                    (the (unsigned-byte ,size) dst)
                                                    (the (signed-byte ,size) shft))))))))
                       (pf (general-pf-spec ,size result))
                       ;; AF is undefined.
                       (zf (zf-spec result))
                       (sf (general-sf-spec ,size result))
                       ;; OF is undefined.

                       (output-rflags (mbe :logic
                                           (change-rflagsBits
                                            input-rflags
                                            :cf cf
                                            :pf pf
                                            :zf zf
                                            :sf sf)
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
                                                    input-rflags)))))))

                       (undefined-flags (mbe
                                         :logic
                                         (change-rflagsBits
                                          0
                                          :af 1
                                          :of 1)
                                         :exec
                                         (!rflagsBits->af
                                          1
                                          (!rflagsBits->of
                                           1 0)))))
                    (mv output-rflags undefined-flags))))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags))

            (undefined-flags (mbe :logic (n32 undefined-flags)
                                  :exec undefined-flags)))

         (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
         :bound ,size
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
         :gen-linear t))))

(make-event (sar-spec-gen  8))
(make-event (sar-spec-gen 16))
(make-event (sar-spec-gen 32))
(make-event (sar-spec-gen 64))

(define sar-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
              (case size
                (1 (n08p dst))
                (2 (n16p dst))
                (4 (n32p dst))
                (8 (n64p dst))
                (otherwise nil)))

  :inline t
  :no-function t

  :parents (instruction-semantic-functions)

  :short "Specification for the @('SAR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference \(N-Z\).</p>

<p>The shift arithmetic right \(SAR\) and shift logical right \(SHR\)
instructions shift the bits of the destination operand to the right
\(toward less significant bit locations\). For each shift count, the
least significant bit of the destination operand is shifted into the
CF flag, and the most significant bit is either set or cleared
depending on the instruction type.  The SAR instruction sets or clears
the most significant bit to correspond to the sign \(most significant
bit\) of the original value in the destination operand. In effect, the
SAR instruction fills the empty bit position s shifted value with the
sign of the unshifted value. ... The OF flag is affected only on 1-bit
shifts. For the SAR instruction, the OF flag is cleared for all 1-bit
shifts. For the SHR instruction, the OF flag is set to the
most-significant bit of the original operand.</p>"

  (case size
    (1 (sar-spec-8  dst src input-rflags))
    (2 (sar-spec-16 dst src input-rflags))
    (4 (sar-spec-32 dst src input-rflags))
    (8 (sar-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-sar-spec
    (natp (mv-nth 0 (sar-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-sar-spec
    :bound 32
    :concl (mv-nth 1 (sar-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-sar-spec
    :bound 32
    :concl (mv-nth 2 (sar-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;;;;;;;;;; SHLD:

(define shld-spec-gen ((size :type (member 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (neg-size-1 (- size-1))
       (size*2 (* 2 size))
       (fn-name (mk-name "SHLD-SPEC-" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte ,size))
        (cnt :type (unsigned-byte 6)
             "Note that @('cnt') is masked appropriately
              by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))
       :returns (mv output-dst ; result (irrelevant if undefined-dst? is t)
                    undefined-dst? ; true iff result of operation is undefined
                    output-rflags ; output flags, ignoring the undefined ones
                    undefined-flags) ; flags to set to undefined values

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              (unsigned-byte-p
                                               (tau-system)))))
       
       :parents (shld-spec)       

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size ,size src)
                      :exec src))
            (cnt (mbe :logic (n-size 6 cnt)
                      :exec cnt))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            ;; we juxtapose dst and srd,
            ;; by shifting dst to the left by size bits
            ;; and OR'ing that with src,
            ;; obtaining a 2*size bit value:
            (dst-src (the (unsigned-byte ,size*2)
                          (logior (the (unsigned-byte ,size*2)
                                       (ash (the (unsigned-byte ,size) dst)
                                            ,size))
                                  (the (unsigned-byte ,size) src))))
            ;; we shift the juxtaposed dst and src to the left by cnt bits,
            ;; so that the high bits of src go into the low bits of dst:
            (output-dst (the (unsigned-byte ,size)
                             (n-size ,size (ash (the (unsigned-byte ,size*2)
                                                     dst-src)
                                                (the (unsigned-byte ,size)
                                                     cnt)))))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case cnt

               (0
                ;; no flags affected
                (mv input-rflags 0))

               (1
                ;; all flags but AF changed accordingly, AF undefined:
                (b* ((cf ; last bit shifted out of dst, i.e. highest bit
                      (mbe :logic (part-select dst :low ,size-1 :width 1)
                           :exec (the (unsigned-byte 1)
                                      (logand (the (unsigned-byte ,size)
                                                   (ash
                                                    (the (unsigned-byte ,size)
                                                         dst)
                                                    ,neg-size-1))
                                              1))))
                     (of ; set iff a sign change occurred
                      (if (= (logbit ,size-1 dst)
                             (logbit ,size-1 output-dst))
                          0
                        1))
                     (pf (general-pf-spec ,size output-dst))
                     (zf (zf-spec output-dst))
                     (sf (general-sf-spec ,size output-dst))
                     (output-rflags (mbe
                                     :logic
                                     (change-rflagsBits
                                      input-rflags
                                      :cf cf
                                      :of of
                                      :pf pf
                                      :zf zf
                                      :sf sf)
                                     :exec
                                     (the (unsigned-byte 32)
                                          (!rflagsBits->cf
                                           cf
                                           (!rflagsBits->of
                                            of
                                            (!rflagsBits->pf
                                             pf
                                             (!rflagsBits->zf
                                              zf
                                              (!rflagsBits->sf
                                               sf
                                               input-rflags))))))))
                     (undefined-flags (the (unsigned-byte 32)
                                           (!rflagsBits->af 1 0))))
                  (mv output-rflags undefined-flags)))

               (otherwise

                (if (<= cnt ,size)
                    ;; all flags but OF and AF changed accordingly,
                    ;; OF and AF undefined:
                    (b* ((cf ; last bit shifted out of dst
                          (mbe :logic (part-select dst
                                                   :low (- ,size cnt)
                                                   :width 1)
                               :exec (logand
                                      1
                                      (the (unsigned-byte ,size)
                                           (ash (the (unsigned-byte ,size) dst)
                                                (the (signed-byte 7)
                                                     (- cnt ,size)))))))
                         (pf (general-pf-spec ,size output-dst))
                         (zf (zf-spec output-dst))
                         (sf (general-sf-spec ,size output-dst))
                         (output-rflags (mbe
                                         :logic
                                         (change-rflagsBits
                                          input-rflags
                                          :cf cf
                                          :pf pf
                                          :zf zf
                                          :sf sf)
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
                                                  input-rflags)))))))
                         (undefined-flags (mbe
                                           :logic
                                           (change-rflagsBits
                                            0
                                            :af 1
                                            :of 1)
                                           :exec
                                           (!rflagsBits->af
                                            1
                                            (!rflagsBits->of
                                             1 0)))))
                      (mv output-rflags undefined-flags))

                  ;; all flags undefined if cnt > size:
                  (b* ((output-rflags input-rflags)
                       (undefined-flags (the (unsigned-byte 32)
                                             (!rflagsBits->cf
                                              1
                                              (!rflagsBits->of
                                               1
                                               (!rflagsBits->pf
                                                1
                                                (!rflagsBits->zf
                                                 1
                                                 (!rflagsBits->sf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   input-rflags)))))))))
                    (mv output-rflags undefined-flags))))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags))

            (undefined-flags (mbe :logic (n32 undefined-flags)
                                  :exec undefined-flags)))

         (mv output-dst
             (> cnt ,size) ; result undefined if count exceeds operand size
             output-rflags
             undefined-flags))       

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" size "-MV-NTH-0-" fn-name)
         :bound ,size
         :concl (mv-nth 0 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t)

       (defthm ,(mk-name "BOOLEANP-MV-NTH-1-" fn-name)
         (booleanp (mv-nth 1 (,fn-name dst src cnt input-rflags))))

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
         :bound 32
         :concl (mv-nth 2 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t)

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-3-" fn-name)
         :bound 32
         :concl (mv-nth 3 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t))))

(make-event (shld-spec-gen 16))
(make-event (shld-spec-gen 32))
(make-event (shld-spec-gen 64))

(define shld-spec
  ((size :type (member 2 4 8))
   dst
   src
   cnt
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (unsigned-byte-p 6 cnt)
              (case size
                (2 (and (n16p dst) (n16p src)))
                (4 (and (n32p dst) (n32p src)))
                (8 (and (n64p dst) (n64p src)))
                (otherwise nil)))

  :inline t
  :no-function t

  :parents (instruction-semantic-functions)

  :short "Specification for the @('SHLD') instruction."

  (case size
    (2 (shld-spec-16 dst src cnt input-rflags))
    (4 (shld-spec-32 dst src cnt input-rflags))
    (8 (shld-spec-64 dst src cnt input-rflags))
    (otherwise (mv 0 nil 0 0)))

  ///

  (defthm natp-mv-nth-0-shld-spec
    (natp (mv-nth 0 (shld-spec size dst src cnt input-rflags)))
    :rule-classes :type-prescription)

  (defthm booleanp-of-mv-nth-1-shld-spec
    (booleanp (mv-nth 1 (shld-spec size dst src cnt input-rflags))))

  (defthm-unsigned-byte-p n32p-mv-nth-2-shld-spec
    :bound 32
    :concl (mv-nth 2 (shld-spec size dst src cnt input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-3-shld-spec
    :bound 32
    :concl (mv-nth 3 (shld-spec size dst src cnt input-rflags))
    :gen-type t
    :gen-linear t))

;;;;;;;;;; SHRD:

(define shrd-spec-gen ((size :type (member 16 32 64)))
  :verify-guards nil

  (b* ((size+1 (1+ size))
       (size-1 (1- size))
       (size*2 (* 2 size))
       (fn-name (mk-name "SHRD-SPEC-" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte ,size))
        (cnt :type (unsigned-byte 6)
             "Note that @('cnt') is masked appropriately
              by the caller of this function..")
        (input-rflags :type (unsigned-byte 32)))
       :returns (mv output-dst ; result (irrelevant if undefined-dst? is t)
                    undefined-dst? ; true iff result of operation is undefined
                    output-rflags ; output flags, ignoring the undefined ones
                    undefined-flags) ; flags to set to undefined values

       :parents (shrd-spec)

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              (unsigned-byte-p
                                               (tau-system)))))

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size ,size src)
                      :exec src))
            (cnt (mbe :logic (n-size 6 cnt)
                      :exec cnt))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            ;; we juxtapose src and dst,
            ;; by shifting src to the left by size bits
            ;; and OR'ing that with dst,
            ;; obtaining a 2*size bit value:
            (src-dst (the (unsigned-byte ,size*2)
                          (logior (the (unsigned-byte ,size*2)
                                       (ash (the (unsigned-byte ,size) src)
                                            ,size))
                                  (the (unsigned-byte ,size) dst))))
            ;; we shift the juxtaposed src and dst to the rigth by cnt bits,
            ;; so that the low bits of src go into the high bits of dst:
            (neg-cnt (the (signed-byte ,size+1) (- cnt)))
            (output-dst (the (unsigned-byte ,size)
                             (n-size ,size (ash (the (unsigned-byte ,size*2)
                                                     src-dst)
                                                (the (signed-byte ,size+1)
                                                     neg-cnt)))))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case cnt

               (0
                ;; no flags affected
                (mv input-rflags 0))

               (1
                ;; all flags but AF changed accordingly, AF undefined:
                (b* ((cf ; last bit shifted out of dst, i.e. lowest bit
                      (mbe :logic (part-select dst :low 0 :width 1)
                           :exec (the (unsigned-byte 1)
                                      (logand (the (unsigned-byte ,size) dst)
                                              1))))
                     (of ; set iff a sign change occurred
                      (if (= (logbit ,size-1 dst)
                             (logbit ,size-1 output-dst))
                          0
                        1))
                     (pf (general-pf-spec ,size output-dst))
                     (zf (zf-spec output-dst))
                     (sf (general-sf-spec ,size output-dst))
                     (output-rflags (mbe
                                     :logic
                                      (change-rflagsBits
                                       input-rflags
                                       :cf cf
                                       :of of
                                       :pf pf
                                       :zf zf
                                       :sf sf)
                                      :exec
                                      (the (unsigned-byte 32)
                                           (!rflagsBits->cf
                                            cf
                                            (!rflagsBits->of
                                             of
                                             (!rflagsBits->pf
                                              pf
                                              (!rflagsBits->zf
                                               zf
                                               (!rflagsBits->sf
                                                sf
                                                input-rflags))))))))
                     (undefined-flags (the (unsigned-byte 32)
                                           (!rflagsBits->af 1 0))))
                  (mv output-rflags undefined-flags)))

               (otherwise

                (if (<= cnt ,size)
                    ;; all flags but OF and AF changed accordingly,
                    ;; OF and AF undefined:
                    (b* ((cf ; last bit shifted out of dst
                          (mbe :logic (part-select dst :low (1- cnt) :width 1)
                               :exec (logand
                                      1
                                      (the (unsigned-byte ,size)
                                           (ash (the (unsigned-byte ,size) dst)
                                                (the (signed-byte ,size+1)
                                                     (1+ neg-cnt)))))))
                         (pf (general-pf-spec ,size output-dst))
                         (zf (zf-spec output-dst))
                         (sf (general-sf-spec ,size output-dst))
                         (output-rflags (mbe
                                         :logic
                                          (change-rflagsBits
                                           input-rflags
                                           :cf cf
                                           :pf pf
                                           :zf zf
                                           :sf sf)
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
                                                   input-rflags)))))))
                         (undefined-flags (mbe
                                           :logic
                                            (change-rflagsBits
                                             0
                                             :af 1
                                             :of 1)
                                            :exec
                                            (!rflagsBits->af
                                             1
                                             (!rflagsBits->of
                                              1 0)))))
                      (mv output-rflags undefined-flags))

                  ;; all flags undefined if cnt > size:
                  (b* ((output-rflags input-rflags)
                       (undefined-flags (the (unsigned-byte 32)
                                             (!rflagsBits->cf
                                              1
                                              (!rflagsBits->of
                                               1
                                               (!rflagsBits->pf
                                                1
                                                (!rflagsBits->zf
                                                 1
                                                 (!rflagsBits->sf
                                                  1
                                                  (!rflagsBits->af
                                                   1
                                                   input-rflags)))))))))
                    (mv output-rflags undefined-flags))))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags))

            (undefined-flags (mbe :logic (n32 undefined-flags)
                                  :exec undefined-flags)))

         (mv output-dst
             (> cnt ,size) ; result undefined if count exceeds operand size
             output-rflags
             undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" size "-MV-NTH-0-" fn-name)
         :bound ,size
         :concl (mv-nth 0 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t)

       (defthm ,(mk-name "BOOLEANP-MV-NTH-1-" fn-name)
         (booleanp (mv-nth 1 (,fn-name dst src cnt input-rflags))))

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
         :bound 32
         :concl (mv-nth 2 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t)

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-3-" fn-name)
         :bound 32
         :concl (mv-nth 3 (,fn-name dst src cnt input-rflags))
         :gen-type t
         :gen-linear t))))

(make-event (shrd-spec-gen 16))
(make-event (shrd-spec-gen 32))
(make-event (shrd-spec-gen 64))

(define shrd-spec
  ((size :type (member 2 4 8))
   dst
   src
   cnt
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (unsigned-byte-p 6 cnt)
              (case size
                (2 (and (n16p dst) (n16p src)))
                (4 (and (n32p dst) (n32p src)))
                (8 (and (n64p dst) (n64p src)))
                (otherwise nil)))

  :inline t
  :no-function t

  :parents (instruction-semantic-functions)

  :short "Specification for the @('SHRD') instruction."

  (case size
    (2 (shrd-spec-16 dst src cnt input-rflags))
    (4 (shrd-spec-32 dst src cnt input-rflags))
    (8 (shrd-spec-64 dst src cnt input-rflags))
    (otherwise (mv 0 nil 0 0)))

  ///

  (defthm natp-mv-nth-0-shrd-spec
    (natp (mv-nth 0 (shrd-spec size dst src cnt input-rflags)))
    :rule-classes :type-prescription)

  (defthm booleanp-of-mv-nth-1-shrd-spec
    (booleanp (mv-nth 1 (shrd-spec size dst src cnt input-rflags))))

  (defthm-unsigned-byte-p n32p-mv-nth-2-shrd-spec
    :bound 32
    :concl (mv-nth 2 (shrd-spec size dst src cnt input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-3-shrd-spec
    :bound 32
    :concl (mv-nth 3 (shrd-spec size dst src cnt input-rflags))
    :gen-type t
    :gen-linear t))

;; ----------------------------------------------------------------------
