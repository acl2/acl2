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
              :ttags (:syscall-exec :other-non-det :undef-flg))
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

(make-event
 (b* ((dispatch
       (create-dispatch-for-opcodes
        #ux0F_38_00 256 :0F-38-three-byte (w state))))

   `(define first-three-byte-opcode-execute
      ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
       (start-rip        :type (signed-byte   #.*max-linear-address-size*))
       (temp-rip         :type (signed-byte   #.*max-linear-address-size*))
       (prefixes         :type (unsigned-byte #.*prefixes-width*))
       (mandatory-prefix :type (unsigned-byte 8))
       (rex-byte         :type (unsigned-byte 8))
       (opcode           :type (unsigned-byte 8))
       (modr/m           :type (unsigned-byte 8))
       (sib              :type (unsigned-byte 8))
       x86)

      ;; #x0F #x38 are the first two opcode bytes.

      :parents (x86-decoder)
      ;; The following arg will avoid binding __function__ to
      ;; first-three-byte-opcode-execute. The automatic __function__ binding
      ;; that comes with define causes stack overflows during the guard proof
      ;; of this function.
      :no-function t
      :ignore-ok t
      :short "First three-byte opcode dispatch function."
      :long "<p>@('first-three-byte-opcode-execute') is the doorway to the
     first three-byte opcode map, i.e., to all three-byte opcodes whose first
     two opcode bytes are @('0F 38').</p>"
      :guard-hints (("Goal"
                     :do-not '(preprocess)
                     :in-theory
                     (e/d
                      ()
                      (unsigned-byte-p signed-byte-p))))

      (case opcode ,@dispatch)

      ///

      (defthm x86p-first-three-byte-opcode-execute
        (implies (x86p x86)
                 (x86p
                  (first-three-byte-opcode-execute
                   proc-mode start-rip temp-rip prefixes
                   mandatory-prefix rex-byte opcode modr/m sib x86)))))))

(make-event
 (b* ((dispatch
       (create-dispatch-for-opcodes
        #ux0F_3A_00 256 :0F-3A-three-byte (w state))))

   `(define second-three-byte-opcode-execute
      ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
       (start-rip        :type (signed-byte   #.*max-linear-address-size*))
       (temp-rip         :type (signed-byte   #.*max-linear-address-size*))
       (prefixes         :type (unsigned-byte #.*prefixes-width*))
       (mandatory-prefix :type (unsigned-byte 8))
       (rex-byte         :type (unsigned-byte 8))
       (opcode           :type (unsigned-byte 8))
       (modr/m           :type (unsigned-byte 8))
       (sib              :type (unsigned-byte 8))
       x86)

      ;; #x0F #x3A are the first two opcode bytes.

      :parents (x86-decoder)
      ;; The following arg will avoid binding __function__ to
      ;; second-three-byte-opcode-execute. The automatic __function__ binding that
      ;; comes with define causes stack overflows during the guard proof of this
      ;; function.
      :no-function t
      :ignore-ok t
      :short "Second three-byte opcode dispatch function."
      :long "<p>@('second-three-byte-opcode-execute') is the doorway to the second
     three-byte opcode map, i.e., to all three-byte opcodes whose second two
     opcode bytes are @('0F 3A').</p>"
      :guard-hints (("Goal"
                     :do-not '(preprocess)
                     :in-theory (e/d () (unsigned-byte-p signed-byte-p))))

      (case opcode ,@dispatch)

      ///

      (defthm x86p-second-three-byte-opcode-execute
        (implies (x86p x86)
                 (x86p (second-three-byte-opcode-execute
                        proc-mode start-rip temp-rip prefixes
                        mandatory-prefix rex-byte opcode modr/m sib x86)))))))

(define three-byte-opcode-decode-and-execute
  ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
   (start-rip          :type (signed-byte #.*max-linear-address-size*))
   (temp-rip           :type (signed-byte #.*max-linear-address-size*))
   (prefixes           :type (unsigned-byte #.*prefixes-width*))
   (rex-byte           :type (unsigned-byte 8))
   (second-escape-byte :type (unsigned-byte 8))
   x86)

  :ignore-ok t
  :guard (or (equal second-escape-byte #x38)
             (equal second-escape-byte #x3A))
  :guard-hints (("Goal" :do-not '(preprocess)
                 :in-theory (e/d*
                             (add-to-*ip add-to-*ip-is-i48p-rewrite-rule)
                             (unsigned-byte-p
                              (:type-prescription bitops::logand-natp-type-2)
                              (:type-prescription bitops::ash-natp-type)
                              acl2::loghead-identity
                              not
                              tau-system
                              (tau-system)))))
  :parents (x86-decoder)
  :short "Decoder and dispatch function for three-byte opcodes, where @('0x0F
  0x38') are the first two opcode bytes"
  :long "<p>Source: Intel Manual, Volume 2, Appendix A-2</p>"

  (b* ((ctx 'three-byte-opcode-decode-and-execute)

       ((mv flg0 (the (unsigned-byte 8) opcode) x86)
        (rme08 proc-mode temp-rip #.*cs* :x x86))
       ((when flg0)
        (!!ms-fresh :opcode-byte-access-error flg0))

       ;; Possible values of opcode: all values denote opcodes of the first or
       ;; second three-byte map, depending on the value of second-escape-byte.
       ;; The function first-three-byte-opcode-execute or
       ;; second-three-byte-opcode-execute case-splits on this opcode byte and
       ;; calls the appropriate instruction semantic function.

       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :increment-error flg))

       ;; ((mv msg (the (unsigned-byte 8) mandatory-prefix))
       ;;  (compute-mandatory-prefix-for-three-byte-opcode
       ;;   proc-mode second-escape-byte opcode prefixes))
       ;; ((when msg)
       ;;  (x86-illegal-instruction msg start-rip temp-rip x86))

       ((the (unsigned-byte 8) mandatory-prefix)
        (compute-mandatory-prefix-for-three-byte-opcode
         proc-mode second-escape-byte opcode prefixes))
       (modr/m?
        (three-byte-opcode-ModR/M-p
         proc-mode mandatory-prefix second-escape-byte opcode))
       ((mv flg1 (the (unsigned-byte 8) modr/m) x86)
        (if modr/m?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg1) (!!ms-fresh :modr/m-byte-read-error flg1))

       ((mv flg temp-rip) (if modr/m?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg))

       (sib? (and modr/m?
                  (b* ((p4? (eql #.*addr-size-override*
                                 (prefixes->adr prefixes)))
                       (16-bit-addressp (eql 2 (select-address-size proc-mode p4? x86))))
                    (x86-decode-SIB-p modr/m 16-bit-addressp))))
       ((mv flg2 (the (unsigned-byte 8) sib) x86)
        (if sib?
            (rme08 proc-mode temp-rip #.*cs* :x x86)
          (mv nil 0 x86)))
       ((when flg2)
        (!!ms-fresh :sib-byte-read-error flg2))

       ((mv flg temp-rip) (if sib?
                              (add-to-*ip proc-mode temp-rip 1 x86)
                            (mv nil temp-rip)))
       ((when flg) (!!ms-fresh :increment-error flg)))

    (case second-escape-byte
      (#x38
       (first-three-byte-opcode-execute
        proc-mode start-rip temp-rip prefixes rex-byte
        mandatory-prefix opcode modr/m sib x86))
      (#x3A
       (second-three-byte-opcode-execute
        proc-mode start-rip temp-rip prefixes rex-byte
        mandatory-prefix opcode modr/m sib x86))
      (otherwise
       ;; Unreachable.
       (!!ms-fresh :illegal-value-of-second-escape-byte second-escape-byte))))

  ///

  (defrule x86p-three-byte-opcode-decode-and-execute
    (implies (x86p x86)
             (x86p (three-byte-opcode-decode-and-execute
                    proc-mode start-rip temp-rip prefixes rex-byte escape-byte x86)))
    :enable add-to-*ip-is-i48p-rewrite-rule
    :disable signed-byte-p))

;; ----------------------------------------------------------------------
