; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")

(include-book "instructions/top"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "prefix-modrm-sib-decoding")
(include-book "dispatch-macros")
(include-book "cpuid")
(include-book "std/strings/hexify" :dir :system)

(local (include-book "dispatch-creator"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d ()
                       (app-view-rml08-no-error
                        (:meta acl2::mv-nth-cons-meta)
                        rme08-value-when-error
                        member-equal))))

(local (xdoc::set-default-parents x86-decoder))

;; ----------------------------------------------------------------------

(local
 (defthm dumb-integerp-of-mv-nth-1-rme08-rule
   (implies (force (x86p x86))
            (integerp (mv-nth 1 (rme08 proc-mode eff-addr seg-reg r-x x86))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm unsigned-byte-p-24-of-vex-prefixes-rule
   (implies
    (unsigned-byte-p 8 byte)
    (and (unsigned-byte-p 24 (logior #xC400 (ash byte 16)))
         (unsigned-byte-p 24 (logior #xC500 (ash byte 16)))))))

(local
 (in-theory (e/d ()
                 (unsigned-byte-p
                  signed-byte-p
                  (:forward-chaining acl2::unsigned-byte-p-forward)
                  ash
                  (tau-system)))))

(make-event
 `(define vex-0F-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                              opcode byte")
     (prefixes               :type (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type (unsigned-byte 8))
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the two-byte opcode map"
    :guard (and (vex-prefixes-byte0-p vex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal" :do-not '(preprocess)))
    :returns (x86 x86p :hyp (x86p x86))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_00 256 :vex-0F (w state)))))

(make-event
 `(define vex-0F38-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                             opcode byte")
     (prefixes               :type (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type (unsigned-byte 8))
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the first
    three-byte opcode map"
    :guard (and (vex-prefixes-byte0-p vex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal" :do-not '(preprocess)))

    :returns (x86 x86p :hyp (x86p x86))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_38_00 256 :VEX-0F-38 (w state)))))

(make-event
 `(define vex-0F3A-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                            opcode byte")
     (prefixes               :type (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type (unsigned-byte 8))
     (vex-prefixes           :type (unsigned-byte 24)
                             "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for VEX-encoded instructions in the second
    three-byte opcode map"
    :guard (and (vex-prefixes-byte0-p vex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal" :do-not '(preprocess)))

    :returns (x86 x86p :hyp (x86p x86))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_3A_00 256 :vex-0f-3a (w state)))))


(define vex-decode-and-execute
  ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
   (start-rip              :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                           "@('temp-rip') points to the byte following the
                            first two VEX prefixes that were already read and
                            placed in the @('vex-prefixes') structure in @(tsee
                            x86-fetch-decode-execute).")
   (prefixes               :type (unsigned-byte #.*prefixes-width*))
   (rex-byte               :type (unsigned-byte 8))
   (vex-prefixes           :type (unsigned-byte 24)
                           "Only @('byte0') and @('byte1') fields are populated
                            when this function is called.")
   x86)

  :guard (and (prefixes-p prefixes)
              (vex-prefixes-byte0-p vex-prefixes))

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints
  (("Goal"
    :in-theory
    (e/d (modr/m-p
          vex-prefixes-byte0-p
          vex-prefixes-map-p add-to-*ip
          add-to-*ip-is-i48p-rewrite-rule)
         (bitops::logand-with-negated-bitmask not (tau-system)))))
  :prepwork
  ((local
    (defthm signed-byte-p-of-temp-rip-rule
      (implies (and (signed-byte-p 48 temp-rip)
                    (integerp n)
                    (<= 0 (+ n temp-rip))
                    (<= (+ n temp-rip) (xr :seg-hidden-limit i x86))
                    (x86p x86))
               (signed-byte-p 48 (+ n temp-rip)))
      :hints (("Goal" :in-theory (e/d (signed-byte-p
                                       unsigned-byte-p)
                                      (seg-hidden-limiti-is-n32p))
               :use ((:instance seg-hidden-limiti-is-n32p))))))

   ;; Enabling for RoW proofs of vex-prefixes->* and !vex-prefixes->*.
   (local (in-theory (e/d (!vex-prefixes->byte0-is-vex-prefixes
                           !vex-prefixes->byte1-is-vex-prefixes
                           !vex-prefixes->byte2-is-vex-prefixes)
                          ())))

   (local
    (defthm logtail-16-of-unsigned-byte-p-8
      (implies (unsigned-byte-p 8 byte)
               (equal (logtail 16 byte) 0))))

   (local
    (defthm loghead-ash-0
      (implies (and (natp i)
                    (natp j)
                    (natp x)
                    (<= i j))
               (equal (loghead i (ash x j))
                      0))
      :hints (("Goal"
               :in-theory (e/d* (acl2::ihsext-inductions
                                 acl2::ihsext-recursive-redefs)
                                ()))))))

  :parents (x86-decoder)

  :long "<p>@('vex-decode-and-execute') dispatches control to VEX-encoded
  instructions.</p>

  <p><i>Reference: Intel Vol. 2A, Section 2.3: Intel Advanced Vector
   Extensions (Intel AVX)</i></p>"

  (b* ((ctx 'vex-decode-and-execute)
       ;; Reference for the following checks that lead to #UD:
       ;; Intel Vol. 2,
       ;; Section 2.3.2 - VEX and the LOCK prefix
       ;; Section 2.3.3 - VEX and the 66H, F2H, and F3H prefixes
       ;; Section 2.3.4 - VEX and the REX prefix

       ;; Any VEX-encoded instruction with mandatory (SIMD) prefixes, lock
       ;; prefix, and REX prefixes (i.e., 66, F2, F3, F0, and 40-4F) preceding
       ;; VEX will #UD.  Therefore, we fetch VEX prefixes after the legacy
       ;; prefixes (function get-prefixes) and the REX prefix have been
       ;; detected and fetched in x86-fetch-decode-execute.

       ((when (not (equal rex-byte 0)))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :rex rex-byte))
       ;; TODO: Intel Vol. 2A Sections 2.3.2 and 2.3.3 say "Any VEX-encoded
       ;; instruction with a LOCK/66H/F2H/F3H prefix preceding VEX will #UD."
       ;; So, should I check :last-byte here instead?
       ((when (equal (the (unsigned-byte 8) (prefixes->lck prefixes)) #.*lock*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :lock-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->rep prefixes)) #.*mandatory-f2h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :F2-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->rep prefixes)) #.*mandatory-f3h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :F3-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->opr prefixes)) #.*mandatory-66h*))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :66-prefix))

       (vex2-prefix?
        (equal (vex-prefixes->byte0 vex-prefixes) #.*vex2-byte0*))
       (vex3-prefix?
        (equal (vex-prefixes->byte0 vex-prefixes) #.*vex3-byte0*))
       (vex-byte1 (vex-prefixes->byte1 vex-prefixes))
       ;; VEX3 Byte 1 #UD Checks for M-MMMM field:
       ;; References: Intel Vol. 2, Figure 2-9 and Section 2.3.6.1
       ((mv vex3-0F-map? vex3-0F38-map? vex3-0F3A-map?)
        (if vex3-prefix?
            (mv (equal (vex3-byte1->m-mmmm vex-byte1) #.*v0F*)
                (equal (vex3-byte1->m-mmmm vex-byte1) #.*v0F38*)
                (equal (vex3-byte1->m-mmmm vex-byte1) #.*v0F3A*))
          (mv nil nil nil)))
       ((when (and vex3-prefix?
                   (not (or vex3-0F-map? vex3-0F38-map? vex3-0F3A-map?))))
        (!!fault-fresh :ud :vex-prefixes vex-prefixes :m-mmmm vex-byte1))

       ;; Completely populating the vex-prefixes structure --- filling out only
       ;; next-byte for vex2-prefixes and both byte2 and next-byte for
       ;; vex3-prefix:
       ((mv flg0 (the (unsigned-byte 8) byte2/next-byte) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg0)
        (!!ms-fresh :vex-byte2/next-byte-read-error flg0))
       ((mv flg1 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg1)
        (!!ms-fresh :increment-error flg1))
       (vex-prefixes
        (if vex3-prefix?
            (!vex-prefixes->byte2 byte2/next-byte vex-prefixes)
          vex-prefixes))
       ((mv flg2 (the (unsigned-byte 8) next-byte) x86)
        (if vex3-prefix?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg2)
        (!!ms-fresh :next-byte-read-error flg2))
       ((mv flg3 temp-rip)
        (if vex3-prefix?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg3)
        (!!ms-fresh :increment-error flg3))

       (opcode
        (the (unsigned-byte 8)
          (if vex3-prefix? next-byte byte2/next-byte)))

       (modr/m? (vex-opcode-ModR/M-p vex-prefixes opcode))
       ((mv flg4 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg4)
        (!!ms-fresh :modr/m-byte-read-error flg4))
       ((mv flg5 temp-rip)
        (if modr/m?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg5) (!!ms-fresh :increment-error flg5))

       (sib? (and modr/m?
                  (b* ((p4? (eql #.*addr-size-override*
                                 (the (unsigned-byte 8) (prefixes->adr prefixes))))
                       (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
                    (x86-decode-SIB-p modr/m 16-bit-addressp))))
       ((mv flg6 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg6)
        (!!ms-fresh :sib-byte-read-error flg6))
       ((mv flg7 temp-rip)
        (if sib?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg7) (!!ms-fresh :increment-error flg7)))

    (cond
     ((mbe :logic (vex-prefixes-map-p #ux0F vex-prefixes)
           :exec (or vex2-prefix? (and vex3-prefix? vex3-0F-map?)))
      (vex-0F-execute proc-mode start-rip temp-rip prefixes rex-byte vex-prefixes opcode modr/m sib x86))
     ((mbe :logic (vex-prefixes-map-p #ux0F_38 vex-prefixes)
           :exec (and vex3-prefix? vex3-0F38-map?))
      (vex-0F38-execute proc-mode start-rip temp-rip prefixes rex-byte vex-prefixes opcode modr/m sib x86))
     ((mbe :logic (vex-prefixes-map-p #ux0F_3A vex-prefixes)
           :exec (and vex3-prefix? vex3-0F3A-map?))
      (vex-0F3A-execute proc-mode start-rip temp-rip prefixes rex-byte vex-prefixes opcode modr/m sib x86))
     (t
      ;; Unreachable.
      (!!ms-fresh :illegal-value-of-VEX-m-mmmm)))))

;; ----------------------------------------------------------------------
