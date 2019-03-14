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

;; EVEX-encoded instructions:

(local
 (defthm unsigned-byte-p-40-of-evex-prefixes-rule
   (implies
    (unsigned-byte-p 8 byte)
    (unsigned-byte-p 40 (logior #x6200 (ash byte 16))))))

(make-event
 `(define evex-0F-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                              opcode byte")
     (prefixes               :type  (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type  (unsigned-byte 8))
     (evex-prefixes           :type (unsigned-byte #.*evex-width*)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the two-byte opcode map"
    :guard (and (evex-prefixes-p evex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))
    :returns (x86 x86p :hyp (x86p x86)
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_00 256 :evex-0F (w state)))))

(make-event
 `(define evex-0F38-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                             opcode byte")
     (prefixes               :type (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type (unsigned-byte 8))
     (evex-prefixes           :type (unsigned-byte #.*evex-width*)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the first
    three-byte opcode map"
    :guard (and (evex-prefixes-p evex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (x86p x86)
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_38_00 256 :evex-0F-38 (w state)))))

(make-event
 `(define evex-0F3A-execute
    ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
     (start-rip              :type (signed-byte   #.*max-linear-address-size*))
     (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                             "@('temp-rip') points to the byte following the
                            opcode byte")
     (prefixes               :type (unsigned-byte #.*prefixes-width*))
     (rex-byte               :type (unsigned-byte 8))
     (evex-prefixes           :type (unsigned-byte #.*evex-width*)
                              "Completely populated when this function is
                              called")
     (opcode                 :type (unsigned-byte 8))
     (modr/m                 :type (unsigned-byte 8))
     (sib                    :type (unsigned-byte 8))
     x86)

    :ignore-ok t

    :parents (x86-decoder)
    :no-function t
    :short "Dispatch function for EVEX-encoded instructions in the second
    three-byte opcode map"
    :guard (and (evex-prefixes-p evex-prefixes)
                (modr/m-p modr/m)
                (sib-p sib))
    :guard-hints (("Goal"
                   :do-not '(preprocess)
                   :in-theory (e/d ()
                                   (unsigned-byte-p
                                    signed-byte-p
                                    (:forward-chaining acl2::unsigned-byte-p-forward)
                                    ash
                                    (tau-system)))))

    :returns (x86 x86p :hyp (x86p x86)
                  :hints (("Goal" :in-theory (e/d () ((tau-system)
                                                      signed-byte-p)))))

    (case opcode
      ,@(create-dispatch-for-opcodes
         #ux0F_3A_00 256 :evex-0F-3A (w state)))))

(define evex-decode-and-execute
  ((proc-mode              :type (integer 0 #.*num-proc-modes-1*))
   (start-rip              :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip               :type (signed-byte   #.*max-linear-address-size*)
                           "@('temp-rip') points to the byte following the
                            first two EVEX prefixes that were already read and
                            placed in the @('evex-prefixes') structure in @(tsee
                            x86-fetch-decode-execute).")
   (prefixes               :type (unsigned-byte #.*prefixes-width*))
   (rex-byte               :type (unsigned-byte 8))
   (evex-prefixes          :type (unsigned-byte #.*evex-width*)
                           "Only @('byte0') and @('byte1') fields are populated
                            when this function is called.")
   x86)

  :ignore-ok t

  :guard (and (evex-prefixes-p evex-prefixes)
              (prefixes-p prefixes))

  :guard-hints
  (("Goal"
    :in-theory
    (e/d (modr/m-p
          add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
         (bitops::logand-with-negated-bitmask))))

  :parents (x86-decoder)

  :long "<p>@('evex-decode-and-execute') dispatches control to EVEX-encoded
  instructions.</p>

  <p><i>Reference: Intel Vol. 2A, Section 2.6: Intel(R) AVX-512
  Encoding</i></p>"

  (b* ((ctx 'evex-decode-and-execute)

       ;; Though I can't find it anywhere explicitly in the Intel manuals, it
       ;; seems reasonable to expect that like the VEX-encoded instructions,
       ;; the use of mandatory and REX prefixes should cause a #UD here too.

       ((when (not (equal rex-byte 0)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :rex rex-byte))
       ((when (equal (the (unsigned-byte 8) (prefixes->lck prefixes)) #.*lock*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :lock-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->rep prefixes)) #.*mandatory-f2h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :F2-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->rep prefixes)) #.*mandatory-f3h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :F3-prefix))
       ((when (equal (the (unsigned-byte 8) (prefixes->opr prefixes)) #.*mandatory-66h*))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :66-prefix))

       ;; EVEX Byte 1:
       (evex-byte1 (evex-prefixes->byte1 evex-prefixes))
       ;; EVEX Byte 1 #UD Checks
       ;; Reference: Intel Vol. 2, Section 2.6.11.2 (Opcode Independent #UD)
       ((when (not (equal (evex-byte1->res evex-byte1) 0)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :byte1-reserved-bits))
       ((mv evex-0F-map? evex-0F38-map? evex-0F3A-map?)
        (mv (equal (evex-byte1->mm evex-byte1) #.*v0F*)
            (equal (evex-byte1->mm evex-byte1) #.*v0F38*)
            (equal (evex-byte1->mm evex-byte1) #.*v0F3A*)))
       ((when (not (or evex-0F-map? evex-0F38-map? evex-0F3A-map?)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :mm evex-byte1))

       ;; EVEX Byte 2:
       ((mv flg0 (the (unsigned-byte 8) evex-byte2) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg0)
        (!!ms-fresh :evex-byte2-read-error flg0))
       ((mv flg1 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg1)
        (!!ms-fresh :increment-error flg1))
       (evex-prefixes
        (!evex-prefixes->byte2 evex-byte2 evex-prefixes))
       ;; EVEX Byte 2 #UD Check
       ;; Reference: Intel Vol. 2, Section 2.6.11.2 (Opcode Independent #UD)
       ((when (not (equal (evex-byte2->res evex-byte2) 1)))
        (!!fault-fresh :ud :evex-prefixes evex-prefixes :byte2-reserved-bit))

       ;; EVEX Byte 3:
       ((mv flg2 (the (unsigned-byte 8) evex-byte3) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg2)
        (!!ms-fresh :evex-byte3-read-error flg2))
       ((mv flg3 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg3)
        (!!ms-fresh :increment-error flg3))

       ;; Opcode:
       ((mv flg4 (the (unsigned-byte 8) opcode) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg4)
        (!!ms-fresh :opcode-read-error flg4))
       ((mv flg5 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg5)
        (!!ms-fresh :increment-error flg5))

       ;; All VEX- and EVEX-encoded instructions require a ModR/M byte.
       ;; Reference: Intel Manual, Vol. 2, Figure 2-8 (Instruction Encoding
       ;; Format with VEX Prefix) and Figure 2-10 (AVX-512 Instruction Format
       ;; and the EVEX Prefix)
       ((mv flg6 (the (unsigned-byte 8) modr/m) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg6)
        (!!ms-fresh :modr/m-byte-read-error flg6))
       ((mv flg7 temp-rip)
        (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg7) (!!ms-fresh :increment-error flg7))

       (sib? (b* ((p4? (eql #.*addr-size-override*
                            (the (unsigned-byte 8) (prefixes->adr prefixes))))
                  (16-bit-addressp
                   (eql 2 (select-address-size proc-mode p4? x86))))
               (x86-decode-SIB-p modr/m 16-bit-addressp)))
       ((mv flg8 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg8)
        (!!ms-fresh :sib-byte-read-error flg8))
       ((mv flg9 temp-rip)
        (if sib?
            (add-to-*ip proc-mode temp-rip 1 x86)
          (mv nil temp-rip)))
       ((when flg9) (!!ms-fresh :increment-error flg9)))

    (cond
     (evex-0F-map?
      (evex-0F-execute
       proc-mode start-rip temp-rip prefixes rex-byte evex-prefixes opcode modr/m sib x86))
     (evex-0F38-map?
      (evex-0F38-execute
       proc-mode start-rip temp-rip prefixes rex-byte evex-prefixes opcode modr/m sib x86))
     (evex-0F3A-map?
      (evex-0F3A-execute
       proc-mode start-rip temp-rip prefixes rex-byte evex-prefixes opcode modr/m sib x86))
     (t
      ;; Unreachable.
      (!!ms-fresh :illegal-value-of-EVEX-mm))))

  ///

  (defthm x86p-evex-decode-and-execute
    (implies (x86p x86)
             (x86p
              (evex-decode-and-execute
               proc-mode
               start-rip temp-rip prefixes rex-byte evex-prefixes x86)))
    :hints (("Goal" :in-theory (e/d () ((tau-system)))))))

;; ----------------------------------------------------------------------
