; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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

(in-package "X86ISA")

(include-book "../utils/structures")
(include-book "top-level-memory")
(include-book "dispatch-macros")
(include-book "inst-structs")
(local (include-book "inst-listing"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ----------------------------------------------------------------------

(defsection prefix-modrm-sib-decoding
  :parents (decoding-and-spec-utils)
  :short "<b>Decoding utilities for the prefixes, ModR/M, and SIB bytes</b>"

  :long "<h3>Legacy Prefix Decoding</h3>

 <p>Array @('*one-byte-prefixes-group-code-info-ar*') is used for the efficient
  lookup of prefix group code information from the one-byte opcode map; see
  @(see legacy-prefixes-decoding) and @(see opcode-maps).</p>

 <h3>Picking Mandatory Prefixes</h3>

 <p>See @(see mandatory-prefixes-computation) and @(see
 instructions-with-mandatory-prefixes) for details.</p>

 <h3>ModR/M and VEX Decoding</h3>

 <p>Arrays are created for the efficient lookup of modr/m-related information
 from the opcode maps.  See @(see ModR/M-decoding).</p>

 <h3>SIB Detecting and Decoding</h3>

 <p>See @(see SIB-decoding) for details.</p>")

(local (xdoc::set-default-parents prefix-modrm-sib-decoding))

;; ----------------------------------------------------------------------

(defsection legacy-prefixes-decoding

  :short "Functions to detect and decode legacy prefixes"

  (local (xdoc::set-default-parents legacy-prefixes-decoding))

  (define inst-prefix-byte-group-code ((inst inst-p))

    :short "Takes in a single instruction and figures out if it is a prefix
  byte; if so, the prefix group number is returned."

    :long "<p>The return value @('0') corresponds to \"not a prefix\" and
  @('1'), @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>

   <p>Note that legacy prefixes are a part of the one-byte opcode map.</p>"

    (b* (((inst inst)))
      (cond
       ((keywordp inst.mnemonic)
        (case inst.mnemonic
          (:prefix-Lock       1) ;; #xF0
          (:prefix-REPNE      1) ;; #xF2
          (:prefix-REP/REPE   1) ;; #xF3

          (:prefix-ES         2) ;; #x26
          (:prefix-CS         2) ;; #x2E
          (:prefix-SS         2) ;; #x36
          (:prefix-DS         2) ;; #x3E
          (:prefix-FS         2) ;; #x64
          (:prefix-GS         2) ;; #x65

          (:prefix-OpSize     3) ;; #x66

          (:prefix-AddrSize   4) ;; #x67

          (t 0)))

       (t 0))))

  (local
   (defthm inst-p-of-car-of-inst-list-p
     (implies (and (equal (len xs) 1)
                   (inst-list-p xs))
              (inst-p (car xs)))))

  (define inst-list-prefix-byte-group-code ((first-opcode 24bits-p)
                                            (num-opcodes natp)
                                            (inst-lst inst-list-p))
    :short "Takes in a list of instructions and returns prefix byte group code
  for each of the constituent instructions"

    :long "<p>Source: Intel Manuals, Vol. 2, Section 2.1.1.</p>

 <p>The value @('0') corresponds to \"not a prefix\" and @('1'),
  @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>"

    (b* (((when (zp num-opcodes)) nil)
         (rest (if (24bits-p (1+ first-opcode))
                   (inst-list-prefix-byte-group-code
                    (1+ first-opcode) (1- num-opcodes) inst-lst)
                 (er hard? 'inst-list-prefix-byte-group-code
                     "Illegal opcode ~s0.~%" (str::hexify (1+ first-opcode)))))
         (same-opcode-insts (select-insts inst-lst :opcode first-opcode))
         ((when (equal (len same-opcode-insts) 1))
          (cons (inst-prefix-byte-group-code (car same-opcode-insts)) rest)))
      (cons 0 rest)))

  (make-event
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 2 0 0 0 0 0 0 0 2 0
           0 0 0 0 0 0 2 0 0 0 0 0 0 0 2 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 2 2 3 4 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (computed-table
         (inst-list-prefix-byte-group-code
          #x0 256 *one-byte-opcode-map*))
        ((unless (equal precomputed-table computed-table))
         (er hard 'one-byte-prefixes-group-code-info
             "Error: Incorrect legacy prefix info computed!")))
     `(defconst *one-byte-prefixes-group-code-info-ar*
        (list-to-array 'one-byte-prefixes-group-code-info
                       (quote ,computed-table)))))

  (define get-one-byte-prefix-array-code
    ((byte :type (unsigned-byte 8)))
    :returns (code natp :rule-classes (:rewrite :type-prescription))
    (aref1 'one-byte-prefixes-group-code-info
           *one-byte-prefixes-group-code-info-ar*
           (mbe :logic (loghead 8 byte)
                :exec byte))
    ///
    (defthm upper-bound-get-one-byte-prefix-array-code
      (<= (get-one-byte-prefix-array-code x) 4))))

;; ----------------------------------------------------------------------

(defsection instructions-with-mandatory-prefixes

  :short "Based off @(see opcode-maps), pre-computing the opcodes that have a
  valid instruction corresponding to the following prefixes:
  @(':NO-PREFIX :66 :F3 :F2')."

  (local (xdoc::set-default-parents instructions-with-mandatory-prefixes))

  (define opcode-present? ((first-opcode 24bits-p)
                           (num-opcodes natp)
                           (inst-lst inst-list-p))
    :short "Returns a 256-element list, where a @('1') at a position @('i')
  denotes that at least one instruction with opcode @('i') exists in
  @('inst-lst'); @('0') denotes no such instruction is present."

    :returns (lst true-listp)
    (b* (((when (zp num-opcodes)) nil)
         (rest (if (24bits-p (1+ first-opcode))
                   (opcode-present?
                    (1+ first-opcode) (1- num-opcodes) inst-lst)
                 (er hard? 'opcode-present?
                     "Illegal opcode ~s0.~%" (str::hexify (1+ first-opcode)))))
         (same-opcode-insts (select-insts inst-lst :opcode first-opcode))
         ((when (endp same-opcode-insts))
          (cons 0 rest)))
      (cons 1 rest)))

  (make-event
   (b* ((64-insts (select-insts *two-byte-opcode-map*
                                ;; All instructions valid in 64-bit mode.
                                :get/rem :rem
                                :mode :i64))

        (NP-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :NO-PREFIX))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_00 256 F3-pfx-insts)))
     `(progn

        (defconst *64-bit-mode-two-byte-no-prefix-ok-ar*
          (list-to-array '64-bit-mode-two-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *64-bit-mode-two-byte-66-ok-ar*
          (list-to-array '64-bit-mode-two-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *64-bit-mode-two-byte-F2-ok-ar*
          (list-to-array '64-bit-mode-two-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))

        (defconst *64-bit-mode-two-byte-F3-ok-ar*
          (list-to-array '64-bit-mode-two-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table)))))))

  (make-event
   (b* ((32-insts (select-insts *two-byte-opcode-map*
                                ;; All instructions valid in 32-bit mode.
                                :get/rem :rem
                                :mode :o64))

        (NP-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :NO-PREFIX))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_00 256 F3-pfx-insts)))
     `(progn

        (defconst *32-bit-mode-two-byte-no-prefix-ok-ar*
          (list-to-array '32-bit-mode-two-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *32-bit-mode-two-byte-66-ok-ar*
          (list-to-array '32-bit-mode-two-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *32-bit-mode-two-byte-F2-ok-ar*
          (list-to-array '32-bit-mode-two-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))

        (defconst *32-bit-mode-two-byte-F3-ok-ar*
          (list-to-array '32-bit-mode-two-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table)))))))

  (make-event
   (b* ((64-insts (select-insts *0F-38-three-byte-opcode-map*
                                ;; All instructions valid in 64-bit mode.
                                :get/rem :rem
                                :mode :i64))

        (NP-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :NO-PREFIX))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_38_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_38_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_38_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_38_00 256 F3-pfx-insts)))
     `(progn

        (defconst *64-bit-mode-0f-38-three-byte-no-prefix-ok-ar*
          (list-to-array '64-bit-mode-0f-38-three-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *64-bit-mode-0f-38-three-byte-66-ok-ar*
          (list-to-array '64-bit-mode-0f-38-three-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *64-bit-mode-0f-38-three-byte-F2-ok-ar*
          (list-to-array '64-bit-mode-0f-38-three-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))

        (defconst *64-bit-mode-0f-38-three-byte-F3-ok-ar*
          (list-to-array '64-bit-mode-0f-38-three-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table)))))))

  (make-event
   (b* ((32-insts (select-insts *0F-38-three-byte-opcode-map*
                                ;; All instructions valid in 32-bit mode.
                                :get/rem :rem
                                :mode :o64))

        (NP-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :no-prefix))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_38_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_38_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_38_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_38_00 256 F3-pfx-insts)))
     `(progn

        (defconst *32-bit-mode-0f-38-three-byte-no-prefix-ok-ar*
          (list-to-array '32-bit-mode-0f-38-three-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *32-bit-mode-0f-38-three-byte-66-ok-ar*
          (list-to-array '32-bit-mode-0f-38-three-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *32-bit-mode-0f-38-three-byte-F2-ok-ar*
          (list-to-array '32-bit-mode-0f-38-three-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))
        (defconst *32-bit-mode-0f-38-three-byte-F3-ok-ar*
          (list-to-array '32-bit-mode-0f-38-three-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table)))))))

  (make-event
   (b* ((64-insts (select-insts *0F-3A-three-byte-opcode-map*
                                ;; All instructions valid in 64-bit mode.
                                :get/rem :rem
                                :mode :i64))

        (NP-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :no-prefix))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_38_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_38_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_38_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 64-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_38_00 256 F3-pfx-insts)))
     `(progn

        (defconst *64-bit-mode-0f-3A-three-byte-no-prefix-ok-ar*
          (list-to-array '64-bit-mode-0f-3A-three-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *64-bit-mode-0f-3A-three-byte-66-ok-ar*
          (list-to-array '64-bit-mode-0f-3A-three-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *64-bit-mode-0f-3A-three-byte-F2-ok-ar*
          (list-to-array '64-bit-mode-0f-3A-three-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))
        (defconst *64-bit-mode-0f-3A-three-byte-F3-ok-ar*
          (list-to-array '64-bit-mode-0f-3A-three-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table)))))))

  (make-event
   (b* ((32-insts (select-insts *0F-3A-three-byte-opcode-map*
                                ;; All instructions valid in 32-bit mode.
                                :get/rem :rem
                                :mode :o64))

        (NP-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :no-prefix))
        (NP-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       NP-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (NP-computed-table (opcode-present? #ux0F_38_00 256 NP-pfx-insts))

        (66-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :66))
        (66-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       66-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (66-computed-table (opcode-present? #ux0F_38_00 256 66-pfx-insts))

        (F2-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F2))
        (F2-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F2-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F2-computed-table (opcode-present? #ux0F_38_00 256 F2-pfx-insts))

        (F3-pfx-insts (select-insts 32-insts
                                    ;; All instructions with the appropriate
                                    ;; prefix.
                                    :get/rem :get :prefix :F3))
        (F3-pfx-insts (remove-insts-with-feat
                       ;; All non-AVX instructions.
                       F3-pfx-insts
                       (append (list :avx :avx2 :bmi1 :bmi2)
                               *avx512-feature-flags*)))
        (F3-computed-table (opcode-present? #ux0F_38_00 256 F3-pfx-insts)))
     `(progn

        (defconst *32-bit-mode-0f-3A-three-byte-no-prefix-ok-ar*
          (list-to-array '32-bit-mode-0f-3A-three-byte-no-prefix-ok
                         (ints-to-booleans
                          (quote ,NP-computed-table))))

        (defconst *32-bit-mode-0f-3A-three-byte-66-ok-ar*
          (list-to-array '32-bit-mode-0f-3A-three-byte-66-ok
                         (ints-to-booleans
                          (quote ,66-computed-table))))

        (defconst *32-bit-mode-0f-3A-three-byte-F2-ok-ar*
          (list-to-array '32-bit-mode-0f-3A-three-byte-F2-ok
                         (ints-to-booleans
                          (quote ,F2-computed-table))))
        (defconst *32-bit-mode-0f-3A-three-byte-F3-ok-ar*
          (list-to-array '32-bit-mode-0f-3A-three-byte-F3-ok
                         (ints-to-booleans
                          (quote ,F3-computed-table))))))))

(defsection mandatory-prefixes-computation

  :short "Picking a mandatory prefix"

  :long "<p><b>When should we interpret a SIMD prefix (@('66'), @('F2'),
 @('F3')) as the mandatory prefix for a given opcode in the two- and three-byte
 opcode maps?</b></p>

 <p>Here are some decoding rules for SIMD mandatory prefixes; note that these
 do NOT apply for VEX/EVEX-encoded instructions because the mandatory prefixes
 are explicitly stated there.  All the examples listed below are from Intel's
 XED (x86 Encoder Decoder: @('https://intelxed.github.io/')).</p>

 <ol>

 <li> <p> For opcodes that can take mandatory prefixes, @('66') is ignored when
 @('F2')/@('F3') are present. Also, a mandatory prefix does not have to
 <b>immediately</b> precede the opcode byte --- see (4) below.</p>

 <p> <b> Examples: </b> </p>

 <code>

 (1) xed -64 -d   660f6f00     ;; movdqa xmm0, xmmword ptr [rax]
 (2) xed -64 -d   f30f6f00     ;; movdqu xmm0, xmmword ptr [rax]
 (3) xed -64 -d 66f30f6f00     ;; movdqu xmm0, xmmword ptr [rax] (same as (2))
 (4) xed -64 -d f3660f6f00     ;; movdqu xmm0, xmmword ptr [rax] (same as (2))

 </code>

 </li>

 <li> <p> For opcodes that can take mandatory prefixes, the presence of an
 unsupported SIMD prefix translates to a reserved instruction; such a prefix
 does NOT act as a modifier prefix. </p>

 <p> <b> Examples: </b> Opcode @('0f 6b') has a no-prefix form and @('66')
 mandatory prefix form.  When used with @('f3'), it leads to an error; see (3)
 below.</p>

 <code>

 (1) xed -64 -d     0f6b00     ;; packssdw mmx0, qword ptr [rax]
 (2) xed -64 -d   660f6b00     ;; packssdw xmm0, xmmword ptr [rax]
 (3) xed -64 -d f3660f6b00     ;; GENERAL_ERROR Could not decode...

 </code>

 </li>

 </ol>"

  (local (include-book "std/strings/decimal" :dir :system))

  (local
   (define gen-compute-mandatory-prefix-fn
     ((map (member-equal map '(#ux0F #ux0F_38 #ux0F_3A)))
      (mode (member-equal mode '(32 64))))

     (b* ((mode-name (str::cat (str::nat-to-dec-string mode) "-BIT"))
          (pre-name (str::cat mode-name "-COMPUTE-MANDATORY-PREFIX-FOR-"))
          (map-name (case map
                      (#ux0F    "TWO-BYTE")
                      (#ux0F_38 "0F-38-THREE-BYTE")
                      (#ux0F_3A "0F-3A-THREE-BYTE")))
          (name (intern$ (str::cat pre-name map-name "-OPCODE") "X86ISA"))

          (F3-ok-crux
           (str::cat mode-name "-MODE-" map-name "-F3-OK"))
          (F3-ok (intern$ F3-ok-crux "X86ISA"))
          (F3-ok-const (intern$ (str::cat "*" F3-ok-crux "-AR*") "X86ISA"))

          (F2-ok-crux
           (str::cat mode-name "-MODE-" map-name "-F2-OK"))
          (F2-ok (intern$ F2-ok-crux "X86ISA"))
          (F2-ok-const (intern$ (str::cat "*" F2-ok-crux "-AR*") "X86ISA"))

          (66-ok-crux
           (str::cat mode-name "-MODE-" map-name "-66-OK"))
          (66-ok (intern$ 66-ok-crux "X86ISA"))
          (66-ok-const (intern$ (str::cat "*" 66-ok-crux "-AR*") "X86ISA")))

       `(define ,name
          ((opcode        :type (unsigned-byte 8)
                          "Relevant opcode byte")
           (prefixes      :type (unsigned-byte #.*prefixes-width*)))
          :guard (prefixes-p prefixes)
          :guard-hints
          (("Goal" :in-theory (disable aref1 assoc-equal (tau-system))))
          :inline t

          :returns (mandatory-prefix
                    (unsigned-byte-p 8 mandatory-prefix)
                    :hints
                    (("goal"
                      :use ((:instance 8bits-p-of-prefixes->opr (x prefixes))
                            (:instance 8bits-p-of-prefixes->rep (x prefixes)))
                      :in-theory (e/d (8bits-p)
                                      (8bits-p-of-prefixes->opr
                                       8bits-p-of-prefixes->rep)))))

          (let ((rep-pfx (the (unsigned-byte 8) (prefixes->rep prefixes))))

            ;; We first check for F2/F3 prefixes, because they have precedence over
            ;; 66.
            (if (not (eql rep-pfx 0))

                (if (or (and (equal rep-pfx  #.*mandatory-f3h*)
                             (aref1 ',F3-ok ,F3-ok-const opcode))
                        (and
                         (equal rep-pfx #.*mandatory-f2h*)
                         (aref1 ',F2-ok ,F2-ok-const opcode)))

                    ;; If the opcode is allowed to have F2/F3, then rep-pfx is the
                    ;; mandatory-prefix.

                    rep-pfx

                  ;; If F2/F3 is used with an opcode that does not support
                  ;; these prefixes as mandatory prefixes, then either F2/F3
                  ;; are used as modifier prefixes or the instruction throws a
                  ;; #UD (which ought to be handled in the dispatch or in the
                  ;; instruction's semantic function).  However, even if 66 is
                  ;; present, we return 0 as the mandatory prefix because F2/F3
                  ;; override 66.

                  0)

              ;; If F2/F3 are not present, then we check for 66 prefix.
              (let ((opr-pfx  (the (unsigned-byte 8) (prefixes->opr prefixes))))

                (if (not (eql opr-pfx 0))

                    (if (aref1 ',66-ok ,66-ok-const opcode)

                        opr-pfx

                      ;; If 66 is used with an opcode that does not support it
                      ;; as a mandatory prefix, then again, either it is used
                      ;; as a modifier prefix or the instruction throws a #UD
                      ;; (handled either in dispatch or in the instruction's
                      ;; semantic function).
                      0)

                  ;; No mandatory prefixes present.
                  0))))))))

  (make-event
   `(progn
      ,(gen-compute-mandatory-prefix-fn #ux0F    64)
      ,(gen-compute-mandatory-prefix-fn #ux0F    32)
      ,(gen-compute-mandatory-prefix-fn #ux0F_38 64)
      ,(gen-compute-mandatory-prefix-fn #ux0F_38 32)
      ,(gen-compute-mandatory-prefix-fn #ux0F_3A 64)
      ,(gen-compute-mandatory-prefix-fn #ux0F_3A 32)))

  (define compute-mandatory-prefix-for-two-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte #.*prefixes-width*)))
    :inline t
    :no-function t
    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d ()
                                              (unsigned-byte-p)))))

    (case proc-mode
      (#.*64-bit-mode*
       (64-bit-compute-mandatory-prefix-for-two-byte-opcode
	opcode prefixes))
      (otherwise
       (32-bit-compute-mandatory-prefix-for-two-byte-opcode
	opcode prefixes))))

  (define compute-mandatory-prefix-for-0F-38-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte #.*prefixes-width*)))
    :inline t
    :no-function t
    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d ()
                                              (unsigned-byte-p)))))

    (case proc-mode
      (#.*64-bit-mode*
       (64-bit-compute-mandatory-prefix-for-0F-38-three-byte-opcode
	opcode prefixes))
      (otherwise
       (32-bit-compute-mandatory-prefix-for-0F-38-three-byte-opcode
	opcode prefixes))))

  (define compute-mandatory-prefix-for-0F-3A-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte #.*prefixes-width*)))

    :inline t
    :no-function t
    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d ()
                                              (unsigned-byte-p)))))

    (case proc-mode
      (#.*64-bit-mode*
       (64-bit-compute-mandatory-prefix-for-0F-3A-three-byte-opcode
	opcode prefixes))
      (otherwise
       (32-bit-compute-mandatory-prefix-for-0F-3A-three-byte-opcode
	opcode prefixes))))

  (define compute-mandatory-prefix-for-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (second-escape-byte :type (unsigned-byte 8)
                         "Second byte of the three-byte opcode; either
                         @('0x38') or @('0x3A')")
     (opcode             :type (unsigned-byte 8)
                         "Third byte of the three-byte opcode")
     (prefixes           :type (unsigned-byte #.*prefixes-width*)))

    :inline t
    :no-function t
    :guard (or (equal second-escape-byte #x38)
	       (equal second-escape-byte #x3A))

    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d () (unsigned-byte-p)))))

    :short "Three-byte opcodes: picks the appropriate SIMD prefix as the
    mandatory prefix, if applicable"

    (case second-escape-byte
      (#x38
       (compute-mandatory-prefix-for-0F-38-three-byte-opcode
	proc-mode opcode prefixes))
      (#x3A
       (compute-mandatory-prefix-for-0F-3A-three-byte-opcode
	proc-mode opcode prefixes))
      (otherwise 0))))

;; ----------------------------------------------------------------------

(defsection ModR/M-detection

  :short "Utilities to detect which opcodes need a ModR/M byte"

  (local (xdoc::set-default-parents ModR/M-detection))

  (define operand-needs-modr/m-p ((operand operand-type-p))
    :short "True if operand needs a modr/m byte"
    (b* (((when (null operand)) nil)
         (Zop (car operand)))
      (cdr (assoc-equal :modr/m?
                        (cdr (assoc-equal Zop *Z-addressing-method-info*))))))

  (define inst-needs-modr/m-p ((inst inst-p))
    :short "Given an @(tsee inst-p), determine whether it requires a ModR/M
    byte or not."
    (b* (((inst inst))
         (opcode inst.opcode)
         ((opcode opcode))
         ((when (or (member-equal :1a opcode.superscripts)
                    (member-equal :1c opcode.superscripts)))
          ;; If :1a or :1c are present, then we don't even need to look at the
          ;; operand info. --- this instruction definitely needs a ModR/M
          ;; byte. See *opcode-map-superscripts* for details.
          t)
         (operands inst.operands)
         ((unless operands)
          ;; When no operand info. is present, then no ModR/M byte is needed.
          nil)
         ((operands operands)))
      ;; Return t if any operand needs a ModR/M byte, and nil if none of them
      ;; do.
      (or (operand-needs-modr/m-p operands.op1)
          (operand-needs-modr/m-p operands.op2)
          (operand-needs-modr/m-p operands.op3)
          (operand-needs-modr/m-p operands.op4))))

  (define any-inst-needs-modr/m-p ((inst-lst inst-list-p))
    :short "Does any instruction in @('inst-lst') require a ModR/M byte?"
    (if (endp inst-lst)
        nil
      (or (inst-needs-modr/m-p (car inst-lst))
          (any-inst-needs-modr/m-p (cdr inst-lst)))))

  (define compute-modr/m-for-opcodes ((first-opcode 24bits-p)
                                      (num-opcodes  natp)
                                      (inst-lst inst-list-p))
    :returns (computed-table true-listp)

    ;; Given a list of instructions with the same opcode, if any of them
    ;; require a ModR/M byte, then all of them must --- i.e., these
    ;; instructions must be a set of "group" instructions belonging to the
    ;; opcode extensions map.  Otherwise, differentiating between them wouldn't
    ;; be possible.

    (b* (((when (zp num-opcodes)) nil)
         (rest (if (24bits-p (1+ first-opcode))
                   (compute-modr/m-for-opcodes
                    (1+ first-opcode) (1- num-opcodes) inst-lst)
                 (er hard? 'compute-modr/m-for-opcodes
                     "Illegal opcode ~s0.~%" (str::hexify (1+ first-opcode)))))
         (same-opcode-insts (select-insts inst-lst :opcode first-opcode))
         ((when (endp same-opcode-insts))
          (cons 0 rest)))
      (cons (if (any-inst-needs-modr/m-p same-opcode-insts) 1 0)
            rest))))

(defsection ModR/M-decoding

  :short "Functions to detect and decode ModR/M bytes"

  (local (xdoc::set-default-parents ModR/M-decoding))

  (local
   (define first-mismatch? ((x true-listp)
                            (y true-listp)
                            (cnt natp))
     ;; For debugging any precomputed-table and computed-table mismatches.
     (if (endp x)
         (list :x x :y y :cnt cnt)
       (if (equal (car x) (car y))
           (first-mismatch? (cdr x) (cdr y) (1+ cnt))
         (list :x (car x) :y (car y) :cnt cnt)))))

  (make-event
   ;; For 64-bit mode:
   (b* ((precomputed-table
         '(
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 1 0 0 0 0 0 1 0 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 1 1 0 0 0 0 0 0 0 0
           1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 1 0 0 0 0 0 0 1 1
           ))
        (computed-table (compute-modr/m-for-opcodes
                         #x0 256
                         (select-insts *one-byte-opcode-map*
                                       :get/rem :rem
                                       :mode :i64)))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-one-byte-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-one-byte-has-modr/m-ar*
        (list-to-array '64-bit-mode-one-byte-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit/Compatibility Modes:
   (b* ((precomputed-table
         '(
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 1 1 0 0 0 0 0 1 0 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 1 1 1 1 0 0 0 0 0 0 0 0
           1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 1 0 0 0 0 0 0 1 1
           ))
        (computed-table (compute-modr/m-for-opcodes
                         #x0 256
                         (select-insts *one-byte-opcode-map*
                                       :get/rem :rem
                                       :mode :o64)))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-one-byte-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-one-byte-has-modr/m-ar*
        (list-to-array '32-bit-mode-one-byte-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  ;;  ModR/M Arrays for Two-byte Opcode Map:
  (make-event
   ;; For 64-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         '(
           1 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0
           1 1 1 1 1 1 1 1 1 0 1 1 0 0 0 1
           1 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 1 1
           1 1 1 1 1 1 1 0 1 1 0 0 0 0 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 0 0 1 1 1 0 0 0 0 0 1 1 1 1 1
           1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0
           0 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0
           ))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-two-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-two-byte-no-prefix-has-modr/m-ar*
        (list-to-array '64-bit-mode-two-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  ;; The older precomputed tables below (commented out) were a bit misleading
  ;; because they also had results for prefixes not equal to the relevant one.

  (make-event
   ;; For 64-bit mode: (:66)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0
         ;;   0 0 1 0 1 1 1 1 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 1 0 1 1 1 1 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-two-byte-66-has-modr/m-ar
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-two-byte-66-has-modr/m-ar*
        (list-to-array '64-bit-mode-two-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F2)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 0 0 0 0 0 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 1 0 0 0 0 0 0 1 1 1 0 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 0 0 0 0 0 0 0 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0
         ;;   0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
         ;;   1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 1 0 0 0 0 0 0 1 1 1 0 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-two-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-two-byte-F2-has-modr/m-ar*
        (list-to-array '64-bit-mode-two-byte-F2-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F3)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 0 0 0 1 0 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
         ;;   1 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 1 1 1 0 1 1 0 0
         ;;   0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 1 0 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
           0 0 0 0 0 0 0 0 1 0 0 0 1 1 0 0
           0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-two-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-two-byte-F3-has-modr/m-ar*
        (list-to-array '64-bit-mode-two-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0
         ;;   1 1 1 1 1 1 1 1 1 0 1 1 0 0 0 1
         ;;   1 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 0 0 1 1
         ;;   1 1 1 1 1 1 1 0 1 1 0 0 0 0 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   0 0 0 1 1 1 0 0 0 0 0 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0
         ;;   0 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
         ;;   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0
         ;;   )
         '(
           1 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0
           1 1 1 1 1 1 1 1 1 0 1 1 0 0 0 1
           1 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 1 1
           1 1 1 1 1 1 1 0 1 1 0 0 0 0 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 0 0 1 1 1 0 0 0 0 0 1 1 1 1 1
           1 1 1 1 1 1 1 1 0 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0
           0 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-two-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-two-byte-no-prefix-has-modr/m-ar*
        (list-to-array '32-bit-mode-two-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:66)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0
         ;;   0 0 1 0 1 1 1 1 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
         ;;   0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 0 0 0 0 0 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 1 0 1 1 1 1 0 0 0 0 0 0 0 0
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
           0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-two-byte-66-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-two-byte-66-has-modr/m-ar*
        (list-to-array '32-bit-mode-two-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F2)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 0 0 0 0 0 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 1 0 0 0 0 0 0 1 1 1 0 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 1 0 0 0 0 0 0 0 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0
         ;;   0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
         ;;   1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 1 0 0 0 0 0 0 1 1 1 0 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-two-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-two-byte-F2-has-modr/m-ar*
        (list-to-array '32-bit-mode-two-byte-F2-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F3)
   (b* ((precomputed-table
         ;; '(
         ;;   1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   1 1 1 0 0 0 1 0 1 0 1 1 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
         ;;   1 1 1 1 0 0 0 0 0 0 0 0 0 0 1 1
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0
         ;;   0 0 0 0 0 0 0 0 1 1 1 0 1 1 0 0
         ;;   0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
         ;;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
         ;;   )
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 1 0 0 0 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 1 1 1 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 1 0 0 0 1 1 0 0
           0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *two-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-two-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-two-byte-F3-has-modr/m-ar*
        (list-to-array '32-bit-mode-two-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  ;;  ModR/M Arrays for the first Three-byte Opcode Map:
  (make-event
   ;; For 64-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         '(
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-38-three-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-38-three-byte-no-prefix-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-38-three-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:66)
   (b* ((precomputed-table
         '(
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
           1 0 0 0 1 1 0 1 0 0 0 0 1 1 1 0
           1 1 1 1 1 1 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-38-three-byte-66-has-modr/m-ar
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-38-three-byte-66-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-38-three-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F2)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-38-three-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-38-three-byte-F2-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-38-three-byte-F2-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F3)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-38-three-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-38-three-byte-F3-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-38-three-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         '(
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-38-three-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-38-three-byte-no-prefix-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-38-three-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:66)
   (b* ((precomputed-table
         '(
           1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
           1 0 0 0 1 1 0 1 0 0 0 0 1 1 1 0
           1 1 1 1 1 1 0 0 1 1 1 1 0 0 0 0
           1 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-38-three-byte-66-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-38-three-byte-66-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-38-three-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F2)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-38-three-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-38-three-byte-F2-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-38-three-byte-F2-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F3)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-38-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_38_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-38-three-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-38-three-byte-F3-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-38-three-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  ;;  ModR/M Arrays for the second Three-byte Opcode Map:
  (make-event
   ;; For 64-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:66)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 1 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-3A-three-byte-66-has-modr/m-ar
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-3A-three-byte-66-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-3A-three-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F2)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-3A-three-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-3A-three-byte-F2-has-modr/m-ar*
        (list-to-array
         '64-bit-mode-0f-3A-three-byte-F2-has-modr/m
         (ints-to-booleans (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:F3)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 64-bit mode.
                             :get/rem :rem
                             :mode :i64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-0f-3A-three-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-0f-3A-three-byte-F3-has-modr/m-ar*
        (list-to-array '64-bit-mode-0f-3A-three-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:NO-PREFIX)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :no-prefix))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-3A-three-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:66)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
           0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0
           1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 0 1 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :66))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-3A-three-byte-66-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-3A-three-byte-66-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-3A-three-byte-66-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F2)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F2))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-3A-three-byte-F2-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-3A-three-byte-F2-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-3A-three-byte-F2-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 32-bit mode: (:F3)
   (b* ((precomputed-table
         '(
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
           ))
        (insts (select-insts *0F-3A-three-byte-opcode-map*
                             ;; All instructions valid in 32-bit mode.
                             :get/rem :rem
                             :mode :o64))
        (insts (select-insts insts
                             ;; All instructions with the appropriate prefix.
                             :get/rem :get :prefix :F3))
        (insts (remove-insts-with-feat
                ;; All non-AVX instructions.
                insts
                (append (list :avx :avx2 :bmi1 :bmi2)
                        *avx512-feature-flags*)))
        (computed-table (compute-modr/m-for-opcodes #ux0F_3A_00 256 insts))
        ((unless (equal precomputed-table computed-table))
         (er hard '32-bit-mode-0f-3A-three-byte-F3-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *32-bit-mode-0f-3A-three-byte-F3-has-modr/m-ar*
        (list-to-array '32-bit-mode-0f-3A-three-byte-F3-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (with-output
    :off :all
    :gag-mode nil

    (progn

      (define 64-bit-mode-one-byte-opcode-ModR/M-p
        ((opcode :type (unsigned-byte 8)))
        :inline t
        :no-function t
        :short "Returns a boolean saying whether, in 64-bit mode,
            the given opcode in the one-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))
        (aref1 '64-bit-mode-one-byte-has-modr/m
               *64-bit-mode-one-byte-has-modr/m-ar* opcode))

      (define 32-bit-mode-one-byte-opcode-ModR/M-p
        ((opcode :type (unsigned-byte 8)))
        :inline t
        :no-function t
        :short "Returns a boolean saying whether, in 32-bit mode,
            the given opcode in the one-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))
        (aref1 '32-bit-mode-one-byte-has-modr/m
               *32-bit-mode-one-byte-has-modr/m-ar* opcode))

      (define one-byte-opcode-ModR/M-p
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (opcode           :type (unsigned-byte 8)))
        :short "Returns @('t') if a one-byte opcode requires a ModR/M byte;
        @('nil') otherwise"
        :inline t
        :no-function t
        :returns (bool booleanp :hyp (n08p opcode))
        (if (equal proc-mode #.*64-bit-mode*)
            (64-bit-mode-one-byte-opcode-ModR/M-p opcode)
          ;; TODO: Other modes eventually.
          (32-bit-mode-one-byte-opcode-ModR/M-p opcode)))

      (define 64-bit-mode-two-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8)
                           "Second byte of the two-byte opcode"))
        :short "Returns a boolean saying whether, in 64-bit mode,
            the given opcode in the two-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '64-bit-mode-two-byte-66-has-modr/m
                  *64-bit-mode-two-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '64-bit-mode-two-byte-F3-has-modr/m
                  *64-bit-mode-two-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '64-bit-mode-two-byte-F2-has-modr/m
                  *64-bit-mode-two-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '64-bit-mode-two-byte-no-prefix-has-modr/m
                  *64-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode))))

      (define 32-bit-mode-two-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8)
                           "Second byte of the two-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode,
            the given opcode in the two-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '32-bit-mode-two-byte-66-has-modr/m
                  *32-bit-mode-two-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '32-bit-mode-two-byte-F3-has-modr/m
                  *32-bit-mode-two-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '32-bit-mode-two-byte-F2-has-modr/m
                  *32-bit-mode-two-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '32-bit-mode-two-byte-no-prefix-has-modr/m
                  *32-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode))))

      (define two-byte-opcode-ModR/M-p
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (mandatory-prefix :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8)
                           "Second byte of the two-byte opcode"))
        :short "Returns @('t') if a two-byte opcode requires a ModR/M byte;
        @('nil') otherwise. Doesn't account for AVX/AVX2/AVX512 instructions."
        :inline t
        :no-function t
        :returns (bool booleanp :hyp (n08p opcode))

        (cond ((equal proc-mode #.*64-bit-mode*)
               (64-bit-mode-two-byte-opcode-ModR/M-p
                mandatory-prefix opcode))
              (t
               ;; TODO: Other modes here eventually.
               (32-bit-mode-two-byte-opcode-ModR/M-p
                mandatory-prefix opcode))))


      (define 64-bit-mode-0F-38-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 38 three-byte opcode"))
        :short "Returns a boolean saying whether, in 64-bit mode, the given
            opcode in the first three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '64-bit-mode-0F-38-three-byte-66-has-modr/m
                  *64-bit-mode-0F-38-three-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '64-bit-mode-0F-38-three-byte-F3-has-modr/m
                  *64-bit-mode-0F-38-three-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '64-bit-mode-0F-38-three-byte-F2-has-modr/m
                  *64-bit-mode-0F-38-three-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                  *64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                  opcode))))

      (define 32-bit-mode-0F-38-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 38 three-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode, the given
            opcode in the first three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '32-bit-mode-0F-38-three-byte-66-has-modr/m
                  *32-bit-mode-0F-38-three-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '32-bit-mode-0F-38-three-byte-F3-has-modr/m
                  *32-bit-mode-0F-38-three-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '32-bit-mode-0F-38-three-byte-F2-has-modr/m
                  *32-bit-mode-0F-38-three-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                  *32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                  opcode))))

      (define 64-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 3A three-byte opcode"))
        :short "Returns a boolean saying whether, in 64-bit mode, the given
            opcode in the second three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '64-bit-mode-0F-3A-three-byte-66-has-modr/m
                  *64-bit-mode-0F-3A-three-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '64-bit-mode-0F-3A-three-byte-F3-has-modr/m
                  *64-bit-mode-0F-3A-three-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '64-bit-mode-0F-3A-three-byte-F2-has-modr/m
                  *64-bit-mode-0F-3A-three-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                  *64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                  opcode))))

      (define 32-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 3A three-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode, the given
            opcode in the second three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (case mandatory-prefix

          (#.*mandatory-66h*
           (aref1 '32-bit-mode-0F-3A-three-byte-66-has-modr/m
                  *32-bit-mode-0F-3A-three-byte-66-has-modr/m-ar* opcode))

          (#.*mandatory-F3h*
           (aref1 '32-bit-mode-0F-3A-three-byte-F3-has-modr/m
                  *32-bit-mode-0F-3A-three-byte-F3-has-modr/m-ar* opcode))

          (#.*mandatory-F2h*
           (aref1 '32-bit-mode-0F-3A-three-byte-F2-has-modr/m
                  *32-bit-mode-0F-3A-three-byte-F2-has-modr/m-ar* opcode))

          (t
           ;; Applies to simple cells as well as NP compound cells.
           (aref1 '32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                  *32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                  opcode))))

      (define three-byte-opcode-ModR/M-p
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (mandatory-prefix :type (unsigned-byte 8))
         (escape-byte      :type (unsigned-byte 8)
                           "Second byte of the three-byte opcode --- either
                           @('#x38') or @('#x3A')")
         (opcode           :type (unsigned-byte 8)
                           "Third byte of the three-byte opcode"))
        :short "Returns @('t') if a three-byte opcode requires a ModR/M byte;
        @('nil') otherwise. Doesn't account for AVX/AVX2/AVX512 instructions."
        :inline t
        :no-function t
        :guard (or (equal escape-byte #x38)
                   (equal escape-byte #x3A))
        :returns (bool booleanp :hyp (n08p opcode))

        (cond ((equal escape-byte #x38)
               (if (equal proc-mode #.*64-bit-mode*)
                   (64-bit-mode-0F-38-three-byte-opcode-ModR/M-p
                    mandatory-prefix opcode)
                 ;; TODO: Other modes here eventually.
                 (32-bit-mode-0F-38-three-byte-opcode-ModR/M-p
                  mandatory-prefix opcode)))
              (t
               (if (equal proc-mode #.*64-bit-mode*)
                   (64-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
                    mandatory-prefix opcode)
                 ;; TODO: Other modes here eventually.
                 (32-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
                  mandatory-prefix opcode)))))))

  (define show-no-modr/m-insts ((inst-lst inst-list-p))
    :returns (no-modr/m-insts inst-list-p
                              :hyp (inst-list-p inst-lst))
    :short "Show all the instructions in @('inst-lst') which don't require a
    ModR/M byte"

    (b* (((when (endp inst-lst)) nil)
         (inst (car inst-lst))
         (rest (show-no-modr/m-insts (cdr inst-lst))))
      (if (inst-needs-modr/m-p inst)
          rest
        (cons inst rest))))

  (assert-event
   (b* ((insts (append *one-byte-opcode-map*
                       *two-byte-opcode-map*
                       *0F-38-three-byte-opcode-map*
                       *0F-3A-three-byte-opcode-map*))
        (insts (select-insts insts :vex? t))
        (no-modr/m-opcodes (show-no-modr/m-insts insts))
        ((unless (equal (len no-modr/m-opcodes) 2)) nil)
        (inst1 (nth 0 no-modr/m-opcodes))
        (inst2 (nth 1 no-modr/m-opcodes))
        ((inst inst1)) ((opcode inst1.opcode))
        ((inst inst2)) ((opcode inst2.opcode)))
     (and (equal inst1.opcode.op #ux0F_77)
          (equal inst2.opcode.op #ux0F_77))))

  (define vex-opcode-ModR/M-p
    ((vex-prefixes     :type (unsigned-byte 24))
     (opcode           :type (unsigned-byte 8)))
    :short "Returns @('t') if a VEX-encoded opcode requires a ModR/M byte;
        @('nil') otherwise."
    :inline t
    :no-function t
    :returns (bool booleanp)
    :guard (vex-prefixes-byte0-p vex-prefixes)
    (if (not (equal opcode #x77))
        t
      ;; VZEROALL/VZEROUPPER are the only two VEX-encoded instructions that do
      ;; not require a ModR/M byte.  These have the opcode #ux0F_77.  See the
      ;; assert-event above.
      (not (vex-prefixes-map-p #x0F vex-prefixes)))))

;; ----------------------------------------------------------------------

(defsection SIB-decoding
  :parents (decoding-and-spec-utils)
  :short "Functions to detect and decode SIB bytes"

  (local (xdoc::set-default-parents SIB-decoding))

  (define x86-decode-SIB-p
    ((ModR/M :type (unsigned-byte 8))
     (16-bit-addressp booleanp))
    :returns (bool booleanp :hyp (n08p ModR/M))
    :short "Returns a boolean saying whether a SIB byte is expected to follow a
    ModR/M byte or not."
    :long
    "<p>
     This is based on Intel manual, Jan'19, Volume 2, Tables 2-1 and 2-2,
     as well as AMD manual, Dec'17, Volume 3, Tables A-33 and A-35.
     When the address size is 32 or 64 bits,
     Intel Table 2-2 and AMD Table A-35 apply:
     a SIB byte is expected exactly when
     ModR/M.mod is not #b11 and ModR/M.r/m is #b100.
     When the address size is 16 bits, no SIB byte is expected.
     </p>
     <p>
     Intel Table 2-3 applies to 32-bit addresses,
     but Section 2.2.1.3 says that it also applies to 64-bit addresses.
     AMD Table A-35 mentions both 32-bit and 64-bit addressing.
     </p>
     <p>
     Intel manual, Jan'19, Volume 2, Table 2-7 is not very clear,
     giving the impression that a SIB byte may be required
     when Mod = 00 and R/M = 101 (last column of first row).
     But AMD manual, Dec'17, Volume 3, Table 1-16
     (which corresponds to Intel Table 2-7) clearly says that
     no SIB byte is present in the first row.
     Intel's last column of first row means that,
     in order to use @('Disp32') instead of @('RIP+Disp32'),
     64-bit mode must use the encoding with SIB in the second row.
     </p>
     <p>
     The second argument of this function says whether
     the address size is 16 bits or not (i.e. 32 or 64 bits).
     In 64-bit mode, this argument is always @('nil').
     In 32-bit mode, this argument may be @('t') or @('nil').
     </p>"
    (and (not 16-bit-addressp)
         (b* ((r/m (modr/m->r/m ModR/M))
              (mod (modr/m->mod ModR/M)))
           (and (int= r/m 4)
                (not (int= mod 3)))))))

;; ----------------------------------------------------------------------
