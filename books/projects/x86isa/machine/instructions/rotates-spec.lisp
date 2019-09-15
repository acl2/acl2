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

;; This book contains the specification of the following instructions:
;; rcl  rcr  rol  ror

(in-package "X86ISA")

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(include-book "centaur/bitops/fast-rotate" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (in-theory (e/d ()
                       (bitops::logand-with-negated-bitmask
                        force (force)))))

;; Note: SRC operand is either an (unsigned-byte 6) or (unsigned-byte
;; 5) since it is masked before the actual rotate or shift
;; operations.

;; ======================================================================

;; Rotates:

(define rcl-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
         (size+1 (1+ size))
         (neg-size (- size))
         (neg-size-1 (- size-1))
         (fn-name (mk-name "RCL-SPEC-" size))
         (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
        (src :type (unsigned-byte 6)
             "Note that @('src') is masked appropriately
              by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              ((tau-system)
                                               unsigned-byte-p))))
       :parents (rcl-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))
            (old-cf (the (unsigned-byte 1)
                      (rflagsBits->cf input-rflags)))

            (new-dst     (mbe :logic (part-install old-cf dst
                                                   :low ,size :width 1)
                              :exec (the (unsigned-byte
                                          ,size+1)
                                      (logior (the (unsigned-byte ,size+1)
                                                (ash old-cf ,size))
                                              dst))))
            (raw-result  (the (unsigned-byte ,size+1)
                           (fast-rotate-left new-dst ,size+1 src)))
            (result      (the (unsigned-byte ,size) (n-size ,size raw-result)))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags affected
                (mv input-rflags 0))
               (1
                ;; CF and OF are the only affected flags.
                (b* ((cf
                      ;; CF = MSB of the raw-result.
                      (mbe :logic (logbit ,size raw-result)
                           :exec (logand 1
                                         (the (unsigned-byte 1)
                                           (ash (the (unsigned-byte ,size+1)
                                                  raw-result)
                                                ,neg-size)))))
                     (of
                      ;; OF = XOR of the CF bit after the rotate and the
                      ;; MSB of the result
                      (b-xor cf (mbe :logic (logbit ,size-1 result)
                                     :exec (logand 1
                                                   (the (unsigned-byte 1)
                                                     (ash (the (unsigned-byte ,size)
                                                            result)
                                                          ,neg-size-1))))))

                     (output-rflags (mbe :logic (change-rflagsBits
                                                 input-rflags
                                                 :cf cf
                                                 :of of)
                                         :exec
                                         (the (unsigned-byte 32)
                                           (!rflagsBits->cf
                                            cf
                                            (!rflagsBits->of
                                             of
                                             input-rflags))))))
                  (mv output-rflags 0)))
               (otherwise
                ;; CF is affected, OF is undefined.
                ;; All other flags are unaffected.
                (b* ((cf ;; CF = MSB of the raw-result.
                      (mbe :logic (logbit ,size raw-result)
                           :exec (logand 1
                                         (the (unsigned-byte 1)
                                           (ash (the (unsigned-byte ,size+1)
                                                  raw-result)
                                                ,neg-size)))))
                     (output-rflags
                      (the (unsigned-byte 32)
                        (!rflagsBits->cf cf input-rflags)))

                     (undefined-flags (the (unsigned-byte 32)
                                        (!rflagsBits->of 1 0))))
                  (mv output-rflags undefined-flags)))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags)))

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

(make-event (rcl-spec-gen  8))
(make-event (rcl-spec-gen 16))
(make-event (rcl-spec-gen 32))
(make-event (rcl-spec-gen 64))

(define rcl-spec
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
  :short "Specification for the @('RCL') instruction"
  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>The RCL instruction shifts the CF flag into the least-significant
bit and shifts the most-significant bit into the CF flag. ... The OF
flag is defined only for the 1-bit rotates; it is undefined in all
other cases \(except RCL and RCR instructions only: a zero-bit rotate
does nothing, that is affects no flags\). For left rotates, the OF
flag is set to the exclusive OR of the CF bit \(after the rotate\) and
the most-significant bit of the result.</p>"

  (case size
    (1 (rcl-spec-8  dst src input-rflags))
    (2 (rcl-spec-16 dst src input-rflags))
    (4 (rcl-spec-32 dst src input-rflags))
    (8 (rcl-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (local (in-theory (e/d () (unsigned-byte-p))))

  (defthm natp-mv-nth-0-rcl-spec
    (natp (mv-nth 0 (rcl-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-rcl-spec
    :bound 32
    :concl (mv-nth 1 (rcl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-rcl-spec
    :bound 32
    :concl (mv-nth 2 (rcl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define rol-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
         (size+1 (1+ size))
         (neg-size-1 (- (1- size)))
         (fn-name (mk-name "ROL-SPEC-" size))
         (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
        (src    :type (unsigned-byte 6)
                "Note that @('src') is masked appropriately
                 by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              ((tau-system)
                                               unsigned-byte-p))))
       :parents (rol-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (result  (mbe :logic
                          (n-size ,size (the (unsigned-byte ,size+1) (fast-rotate-left dst ,size src)))
                          :exec
                          (the (unsigned-byte ,size) (fast-rotate-left dst ,size src))))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags, except OF, affected. OF is undefined.
                (b* ((undefined-flags (the (unsigned-byte 32)
                                        (!rflagsBits->of 1 0))))
                  (mv input-rflags undefined-flags)))
               (1
                ;; CF and OF are the only affected flags.
                (b* ((cf
                      ;; CF = LSB of the  result.
                      (mbe :logic ;; (logbit 0 result)
                           (part-select result :low 0 :width 1)
                           :exec (the (unsigned-byte 1)
                                   (logand 1 (the (unsigned-byte ,size)
                                               result)))))
                     (of
                      ;; OF = XOR of the CF bit after the rotate and the
                      ;; MSB of the result
                      (b-xor cf (mbe :logic (logbit ,size-1 result)
                                     :exec (logand 1
                                                   (the (unsigned-byte 1)
                                                     (ash (the (unsigned-byte ,size)
                                                            result)
                                                          ,neg-size-1))))))

                     (output-rflags (mbe :logic
                                         (change-rflagsBits
                                          input-rflags
                                          :cf cf
                                          :of of)
                                         :exec
                                         (the (unsigned-byte 32)
                                           (!rflagsBits->cf
                                            cf
                                            (!rflagsBits->of
                                             of
                                             input-rflags))))))
                  (mv output-rflags 0)))

               (otherwise
                ;; CF is affected, OF is undefined.
                ;; All other flags are unaffected.

                (b* ((cf          ;; CF = LSB of the result.
                      (mbe :logic ;; (logbit 0 result)
                           (part-select result :low 0 :width 1)
                           :exec
                           (the (unsigned-byte 1)
                             (logand 1 (the (unsigned-byte ,size)
                                         result)))))
                     (output-rflags (the (unsigned-byte 32)
                                      (!rflagsBits->cf cf input-rflags)))
                     (undefined-flags
                      (the (unsigned-byte 32)
                        (!rflagsBits->of 1 0))))
                  (mv output-rflags undefined-flags)))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags)))

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

(make-event (rol-spec-gen  8))
(make-event (rol-spec-gen 16))
(make-event (rol-spec-gen 32))
(make-event (rol-spec-gen 64))

(define rol-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and
          (n06p src)
          (case size
            (1  (n08p dst))
            (2  (n16p dst))
            (4  (n32p dst))
            (8  (n64p dst))
            (otherwise nil)))

  :inline t
  :no-function t
  :parents (instruction-semantic-functions)
  :short "Specification for the @('ROL') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>For the ROL and ROR instructions, the original value of the CF flag
is not a part of the result, but the CF flag receives a copy of the
bit that was shifted from one end to the other. ... The OF flag is
defined only for the 1-bit rotates; it is undefined in all other cases
\(except ROL and RCR instructions only: a zero-bit rotate does
nothing, that is affects no flags\). For left rotates, the OF flag is
set to the exclusive OR of the CF bit \(after the rotate\) and the
most-significant bit of the result.</p>"

  (case size
    (1 (rol-spec-8  dst src input-rflags))
    (2 (rol-spec-16 dst src input-rflags))
    (4 (rol-spec-32 dst src input-rflags))
    (8 (rol-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-rol-spec
    (natp (mv-nth 0 (rol-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-rol-spec
    :bound 32
    :concl (mv-nth 1 (rol-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-rol-spec
    :bound 32
    :concl (mv-nth 2 (rol-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define rcr-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
         (size-2 (- size 2))
         (size+1 (1+ size))
         (neg-size (- size))
         (neg-size-1 (- size-1))
         (neg-size-2 (- size-2))
         (fn-name (mk-name "RCR-SPEC-" size))
         (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
        (src    :type (unsigned-byte 6)
                "Note that @('src') is masked appropriately
                 by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              ((tau-system)
                                               unsigned-byte-p))))
       :parents (rcr-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (input-cf (the (unsigned-byte 1)
                        (rflagsBits->cf input-rflags)))

            (new-dst     (mbe :logic (part-install input-cf dst
                                                   :low ,size :width 1)
                              :exec (the (unsigned-byte
                                          ,size+1)
                                      (logior (the (unsigned-byte ,size+1)
                                                (ash input-cf ,size))
                                              dst))))
            (raw-result  (the (unsigned-byte ,size+1) (fast-rotate-right new-dst ,size+1 src)))
            (result      (the (unsigned-byte ,size) (n-size ,size raw-result)))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags affected
                (mv input-rflags 0))

               (1
                ;; CF and OF are the only affected flags.
                (b* ((cf
                      ;; CF = MSB of the raw-result.
                      (mbe :logic (logbit ,size raw-result)
                           :exec (logand 1
                                         (the (unsigned-byte 1)
                                           (ash (the (unsigned-byte ,size+1)
                                                  raw-result)
                                                ,neg-size)))))
                     (of
                      ;; OF = XOR of the two most significant bits of
                      ;; the result.
                      (b-xor (mbe :logic (logbit ,size-1 result)
                                  :exec (logand 1
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte ,size)
                                                         result)
                                                       ,neg-size-1))))
                             (mbe :logic ;; (logbit ,size-2 result)
                                  (part-select result :low ,size-2 :width 1)
                                  :exec (logand 1
                                                (the (unsigned-byte 2)
                                                  (ash (the (unsigned-byte ,size)
                                                         result)
                                                       ,neg-size-2))))))

                     (output-rflags (mbe :logic
                                         (change-rflagsBits
                                          input-rflags
                                          :cf cf
                                          :of of)
                                         :exec
                                         (the (unsigned-byte 32)
                                           (!rflagsBits->cf
                                            cf
                                            (!rflagsBits->of
                                             of
                                             input-rflags))))))
                  (mv output-rflags 0)))

               (otherwise
                ;; CF is affected, OF is undefined.
                ;; All other flags are unaffected.
                (b* ((cf ;; CF = MSB of the raw-result.
                      (mbe :logic (logbit ,size raw-result)
                           :exec (the (unsigned-byte 1)
                                   (logand 1
                                           (the (unsigned-byte 1)
                                             (ash (the (unsigned-byte ,size+1)
                                                    raw-result)
                                                  ,neg-size))))))

                     (output-rflags (the (unsigned-byte 32)
                                      (!rflagsBits->cf cf input-rflags)))

                     (undefined-flags (the (unsigned-byte 32)
                                        (!rflagsBits->of 1 0))))
                  (mv output-rflags undefined-flags))))))

         (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
         :bound ,size
         :concl (mv-nth 0 (,fn-name dst src output-rflags))
         :gen-type t
         :gen-linear t)

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-1-" fn-name)
         :bound 32
         :concl (mv-nth 1 (,fn-name dst src output-rflags))
         :gen-type t
         :gen-linear t)

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
         :bound 32
         :concl (mv-nth 2 (,fn-name dst src output-rflags))
         :gen-type t
         :gen-linear t))))

(make-event (rcr-spec-gen  8))
(make-event (rcr-spec-gen 16))
(make-event (rcr-spec-gen 32))
(make-event (rcr-spec-gen 64))

(define rcr-spec
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
  :short "Specification for the @('RCR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>The RCR instruction shifts the CF flag into the most-significant
bit and shifts the least-significant bit into the CF flag. ... The OF
flag is defined only for the 1-bit rotates; it is undefined in all
other cases \(except RCL and RCR instructions only: a zero-bit rotate
does nothing, that is affects no flags\).  For right rotates, the OF
flag is set to the exclusive OR of the two most-significant bits of
the result.</p>"

  (case size
    (1 (rcr-spec-8  dst src input-rflags))
    (2 (rcr-spec-16 dst src input-rflags))
    (4 (rcr-spec-32 dst src input-rflags))
    (8 (rcr-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-rcr-spec
    (natp (mv-nth 0 (rcr-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-rcr-spec
    :bound 32
    :concl (mv-nth 1 (rcr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-rcr-spec
    :bound 32
    :concl (mv-nth 2 (rcr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define ror-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (size-2 (- size 2))
       (?size+1 (1+ size))
       (neg-size-1 (- size-1))
       (neg-size-2 (- size-2))
       (fn-name (mk-name "ROR-SPEC-" size))
       (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
        (src    :type (unsigned-byte 6)
                "Note that @('src') is masked appropriately
                 by the caller of this function.")
        (input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables)
                                              ((tau-system)
                                               unsigned-byte-p))))
       :parents (ror-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
                      :exec dst))
            (src (mbe :logic (n-size 6 src)
                      :exec src))
            (input-rflags (mbe :logic (n32 input-rflags)
                               :exec input-rflags))

            (result  (mbe :logic
                          (n-size ,size (the (unsigned-byte ,size) (fast-rotate-right dst ,size src)))
                          :exec
                          (the (unsigned-byte ,size) (fast-rotate-right dst ,size src))))

            ((mv (the (unsigned-byte 32) output-rflags)
                 (the (unsigned-byte 32) undefined-flags))

             (case src
               (0
                ;; No flags, except OF, affected.
                (b* ((undefined-flags (the (unsigned-byte 32)
                                        (!rflagsBits->of 1 0))))

                  (mv input-rflags undefined-flags)))

               (1
                ;; CF and OF are the only affected flags.
                (b* ((cf
                      ;; CF = MSB of the  result.
                      (mbe :logic (logbit ,size-1 result)
                           :exec (logand 1
                                         (the (unsigned-byte 1)
                                           (ash (the (unsigned-byte ,size)
                                                  result)
                                                ,neg-size-1)))))
                     (of
                      ;; OF = XOR of the two most significant bits of
                      ;; the result.
                      (b-xor (mbe :logic (logbit ,size-1 result)
                                  :exec (logand 1
                                                (the (unsigned-byte 1)
                                                  (ash (the (unsigned-byte ,size)
                                                         result)
                                                       ,neg-size-1))))
                             (mbe :logic ;; (logbit ,size-2 result)
                                  (part-select result :low ,size-2 :width 1)
                                  :exec (logand 1
                                                (the (unsigned-byte 2)
                                                  (ash (the (unsigned-byte ,size)
                                                         result)
                                                       ,neg-size-2))))))
                     (output-rflags (mbe :logic
                                         (change-rflagsBits
                                          input-rflags
                                          :cf cf
                                          :of of)
                                         :exec
                                         (the (unsigned-byte 32)
                                           (!rflagsBits->cf
                                            cf
                                            (!rflagsBits->of
                                             of
                                             input-rflags))))))
                  (mv output-rflags 0)))

               (otherwise
                ;; CF is affected, OF is undefined.
                ;; All other flags are unaffected.
                (b* ((cf ;; CF = MSB of the result.
                      (mbe :logic
                           (part-select result :low 0 :width 1)
                           :exec
                           (the (unsigned-byte 1)
                             (logand 1 (the (unsigned-byte ,size)
                                         result)))))
                     (output-rflags (the (unsigned-byte 32)
                                      (!rflagsBits->cf cf input-rflags)))
                     (undefined-flags (the (unsigned-byte 32)
                                        (!rflagsBits->of 1 0))))
                  (mv output-rflags undefined-flags)))))

            (output-rflags (mbe :logic (n32 output-rflags)
                                :exec output-rflags)))

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

(make-event (ror-spec-gen  8))
(make-event (ror-spec-gen 16))
(make-event (ror-spec-gen 32))
(make-event (ror-spec-gen 64))

(define ror-spec
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

  :short "Specification for the @('ROR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>For the ROR and ROR instructions, the orig- inal value of the CF
flag is not a part of the result, but the CF flag receives a copy of
the bit that was shifted from one end to the other. ... The OF flag is
defined only for the 1-bit rotates; it is undefined in all other cases
\(except RCL and RCR instructions only: a zero-bit rotate does
nothing, that is affects no flags\).  For right rotates, the OF flag
is set to the exclusive OR of the two most-significant bits of the
result.</p>"

  (case size
    (1 (ror-spec-8  dst src input-rflags))
    (2 (ror-spec-16 dst src input-rflags))
    (4 (ror-spec-32 dst src input-rflags))
    (8 (ror-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-ror-spec
    (natp (mv-nth 0 (ror-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p n32p-mv-nth-1-ror-spec
    :bound 32
    :concl (mv-nth 1 (ror-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-unsigned-byte-p n32p-mv-nth-2-ror-spec
    :bound 32
    :concl (mv-nth 2 (ror-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;; ======================================================================
