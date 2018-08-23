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

(include-book "../utils/constants")
(include-book "opcode-maps")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ----------------------------------------------------------------------

(defsection prefix-modrm-sib-decoding
  :parents (decoding-and-spec-utils)
  :short "<b>Decoding utilities for the prefixes, ModR/M, and SIB bytes</b>"

  :long "<h3>Legacy Prefix Decoding</h3>

<p>Array @('*one-byte-prefixes-group-code-info-ar*') is created by the function
 @(tsee compute-prefix-byte-group-code) for the efficient lookup of prefix
 group code information from @('*one-byte-opcode-map-lst*'); see @(see
 legacy-prefixes-decoding) and @(see opcode-maps).</p>

 <h3>ModR/M and VEX Decoding</h3>

 <p>Arrays are created by the function @(tsee compute-prop-for-an-opcode-map)
 for the efficient lookup of modr/m-related information from the opcode maps.
 See @(see ModR/M-decoding).</p>

 <h3>SIB Decoding</h3>

 <p>The function @(tsee x86-decode-SIB-p) determines whether a SIB byte ought
 to follow a ModR/M byte or not.</p>")

(local (xdoc::set-default-parents prefix-modrm-sib-decoding))

;; ----------------------------------------------------------------------

;; Addressing Info:

(defconst *Z-addressing-method-info*

  ;; See Intel Vol. 2, Appendix A.2.1
  ;; Also see AMD Vol. 3, Appendix A

  ;; The information in this constant definition comes not only from the
  ;; aforementioned Appendices, but also from an examination of the involved
  ;; instructions. However, the accuracy of this information has been so far
  ;; confirmed only for the instructions covered by the current formal model;
  ;; for unimplemented instructions, it is possible that the information may
  ;; need to be changed.

  ;; (assoc :modr/m? (cdr (assoc 'A *Z-addressing-method-info*)))

  (list

   ;; A Direct address: the instruction has no ModR/M byte; the
   ;; address of the operand is encoded in the instruction. No base
   ;; register, index register, or scaling factor can be applied (for
   ;; example far JMP (EA)).

   '(A (:modr/m? . nil) (:vex? . nil))

   ;; B The VEX.vvvv field of the VEX prefix selects a general purpose
   ;; register.

   '(B (:modr/m? . nil) (:vex? . t))

   ;; C The reg field of the ModR/M byte selects a control register
   ;; (for example MOV (0F20, 0F22)).

   '(C (:modr/m? . t) (:vex? . nil))

   ;; D The reg field of the ModR/M byte selects a debug register (for
   ;; example MOV (0F21,0F23)).

   '(D (:modr/m? . t) (:vex? . nil))

   ;; E A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a general-purpose register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register, an index register, a scaling factor, a
   ;; displacement.

   '(E (:modr/m? . t) (:vex? . nil))

   ;; F EFLAGS/RFLAGS Register.

   '(F (:modr/m? . nil) (:vex? . nil))

   ;; G The reg field of the ModR/M byte selects a general register
   ;; (for example AX (000)).

   '(G (:modr/m? . t) (:vex? . nil))

   ;; H The VEX.vvvv field of the VEX prefix selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. For legacy SSE encodings this operand does not exist,
   ;; changing the instruction to destructive form.

   '(H (:modr/m? . nil) (:vex? . t))

   ;; I Immediate data: the operand value is encoded in subsequent
   ;; bytes of the instruction.

   '(I (:modr/m? . nil) (:vex? . nil))

   ;; J The instruction contains a relative offset to be added to the
   ;; instruction pointer register (for example JMP (0E9), LOOP).

   '(J (:modr/m? . nil) (:vex? . nil))

   ;; Important: Addressing info with "K-" prefix below does not appear in the
   ;; Intel Manuals (dated May, 2018).  The Intel manuals do not define a Z
   ;; addressing method for AVX512 instructions yet, so until they do, I am
   ;; going to use my own encoding for specifying opmask registers.

   ;; Source: Section 2.6.3 (Opmask Register Encoding), specifically, Table
   ;; 2-33 (Opmask Register Specifier Encoding), Intel Vol. 2

   ;; K-reg: modr/m.reg is used to access opmask registers k0-k7 (common
   ;; usages: source).

   '(K-reg (:modr/m? . t) (:vex? . nil))

   ;; K-vex: VEX.vvvv is used to access opmask registers k0-k7 (common usages:
   ;; 2nd source).

   '(K-vex (:modr/m? . nil) (:vex? . t))

   ;; K-r/m: modr/m.r/m is used to access opmask registers k0-k7 (common
   ;; usages: 1st source).

   '(K-r/m (:modr/m? . t) (:vex? . nil))

   ;; K-evex: EVEX.aaa is used to access opmask registers k0-k4 (common usages:
   ;; Opmask).

   '(K-evex (:modr/m? . nil) (:vex? . nil) (:evex? . t))

   ;; L The upper 4 bits of the 8-bit immediate selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. (the MSB is ignored in 32-bit mode)

   '(L (:modr/m? . nil) (:vex? . t))

   ;; M The ModR/M byte may refer only to memory (for example BOUND,
   ;; LES, LDS, LSS, LFS, LGS, CMPXCHG8B).

   '(M (:modr/m? . t) (:vex? . nil))

   ;; N The R/M field of the ModR/M byte selects a packed-quadword MMX
   ;; technology register.

   '(N (:modr/m? . t) (:vex? . nil))

   ;; O The instruction has no ModR/M byte. The offset of the operand
   ;; is coded as a word or double word (depending on address size
   ;; attribute) in the instruction. No base register index register
   ;; or scaling factor can be applied (for example MOV (A0-A3)).

   '(O (:modr/m? . nil) (:vex? . nil))

   ;; P The reg field of the ModR/M byte selects a packed quadword MMX
   ;; technology register.

   '(P (:modr/m? . t) (:vex? . nil))

   ;; Q A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either an MMX technology register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register, an index register, a scaling factor, and a
   ;; displacement.

   '(Q (:modr/m? . t) (:vex? . nil))

   ;; R The R/M field of the ModR/M byte may refer only to a general
   ;; register (for example MOV (0F20-0F23)).

   '(R (:modr/m? . t) (:vex? . nil))

   ;; S The reg field of the ModR/M byte selects a segment register
   ;; (for example MOV (8C,8E)).

   '(S (:modr/m? . t) (:vex? . nil))

   ;; U The R/M field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(U (:modr/m? . t) (:vex? . t))

   ;; V The reg field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(V (:modr/m? . t) (:vex? . t))

   ;; W A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a 128-bit XMM register, a 256-bit
   ;; YMM register (determined by operand type), or a memory
   ;; address. If it is a memory address the address is computed from
   ;; a segment register and any of the following values: a base
   ;; register, an index register, a scaling factor, and a displacement.

   '(W (:modr/m? . t) (:vex? . t))

   ;; X Memory addressed by the DS:rSI register pair (for example MOVS,
   ;; CMPS, OUTS, or LODS).

   '(X (:modr/m? . nil) (:vex? . nil))

   ;; Y Memory addressed by the ES:rDI register pair (for example MOVS,
   ;; CMPS, INS, STOS, or SCAS).

   '(Y (:modr/m? . nil) (:vex? . nil))

   ))

(local
 (defthm delete-assoc-equal-returns-an-alistp
   (implies (alistp y)
            (alistp (delete-assoc-equal x y)))
   :hints (("Goal" :in-theory (e/d (delete-assoc-equal) ())))))

(local
 (defthmd not-consp-not-assoc-equal
   (implies (and (alistp cell)
                 (not (consp (assoc-equal key cell))))
            (not (assoc-equal key cell)))))

;; ----------------------------------------------------------------------

(defsection detecting-compound-cells-and-legal-mandatory-prefixes

  :short "Functions to detect whether a cell in an opcode map satisfies @(tsee
  compound-cell-p) or not, and if it does, which SIMD prefixes are legal
  mandatory prefixes"

  (local (xdoc::set-default-parents
          detecting-compound-cells-and-legal-mandatory-prefixes))

  (define compute-compound-cell-for-an-opcode-row
    ((row          true-list-listp)
     (64-bit-modep booleanp)
     &key
     (k ':no-prefix))
    :guard (member-equal k (cons :no-prefix *mandatory-prefixes*))

    :guard-hints (("Goal" :in-theory (e/d (not-consp-not-assoc-equal
                                           opcode-row-p
                                           opcode-cell-p)
                                          ())))
    :returns (mv (compound-info true-listp)
                 (pfx-info true-listp))

    (if (opcode-row-p row)

        (if (endp row)

            (mv nil nil)

          (b* ((cell (car row))
               ((if (simple-cell-p cell))
                (b* (((mv compound? pfx-ok?)
                      (compute-compound-cell-for-an-opcode-row
                       (cdr row)
                       64-bit-modep :k k)))
                  (mv (cons '0 compound?) (cons '0 pfx-ok?))))
               (stripped-cell
                ;; In 64-bit mode, we ignore the opcode information
                ;; that is invalid in 64-bit mode, while in 32-bit
                ;; mode, we ignore the opcode information that is valid
                ;; only in 64-bit mode.

                ;; If the resulting stripped cell is compound, then it can only
                ;; have the following legal keys now:
                ;; (*compound-cells-legal-keys* - '(:i64 :o64))
                (if 64-bit-modep
                    (b* ((no-i64-cell (delete-assoc-equal :i64 cell))
                         (o64-cell    (cdr (assoc-equal :o64 no-i64-cell))))
                      (or o64-cell no-i64-cell))
                  (b* ((no-o64-cell (delete-assoc-equal :o64 cell))
                       (i64-cell    (cdr (assoc-equal :i64 no-o64-cell))))
                    (or i64-cell no-o64-cell))))
               (this-computed-val  (cond
                                    ((eq stripped-cell 'nil) '0)
                                    ((compound-cell-p stripped-cell) '1)
                                    (t '0)))
               (this-pfx-val (bool->bit
                              (if (eql this-computed-val 1)
                                  ;; Compound Cell
                                  (member-equal k (strip-cars stripped-cell))
                                nil)))
               ((mv compound? pfx-ok?)
                (compute-compound-cell-for-an-opcode-row
                 (cdr row)
                 64-bit-modep :k k)))
            (mv (cons this-computed-val compound?)
                (cons this-pfx-val pfx-ok?))))

      (b* ((- (cw "~%compute-compound-cell-for-an-opcode-row:~% ~
 Ill-formed opcode row: ~x0~%" row)))
        (mv nil nil))))

  (define compute-compound-cell-for-an-opcode-map ((map true-listp)
                                                   (64-bit-modep booleanp)
                                                   &key
                                                   (k ':no-prefix))
    :guard (member-equal k (cons :no-prefix *mandatory-prefixes*))

    :guard-hints (("Goal" :in-theory (e/d (opcode-map-p) ())))

    (if (opcode-map-p map)

        (if (endp map)
            (mv nil nil)
          (b* ((row (car map))
               ((mv row-compound-p row-pfx)
                (compute-compound-cell-for-an-opcode-row
                 row 64-bit-modep :k k))
               ((mv rest-compound-p rest-pfx)
                (compute-compound-cell-for-an-opcode-map
                 (cdr map) 64-bit-modep :k k)))
            (mv (append row-compound-p rest-compound-p)
                (append row-pfx rest-pfx))))

      (b* ((- (cw "~%compute-compound-cell-for-an-opcode-map:~% ~
 Ill-formed opcode map: ~x0~%" map)))
        (mv nil nil))))

  (assert-event
   ;; Sanity check: one-byte opcode map has no compound opcodes in both 32- and
   ;; 64-bit modes.
   (b* (((mv 64-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *one-byte-opcode-map-lst* t))
        ((mv 32-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *one-byte-opcode-map-lst* nil)))
     (and
      (equal 64-bit-compound-info 32-bit-compound-info)
      (equal 64-bit-compound-info
             '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))))

  (make-event
   (b* (((mv 64-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* t))
        ((mv & 64-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* t :k :66))
        ((mv & 64-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* t :k :f3))
        ((mv & 64-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* t :k :f2))
        ((mv 32-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* nil))
        ((mv & 32-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* nil :k :66))
        ((mv & 32-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* nil :k :f3))
        ((mv & 32-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *two-byte-opcode-map-lst* nil :k :f2)))
     `(progn

        (defconst *64-bit-mode-two-byte-compound-opcodes-ar*
          (list-to-array
           '64-bit-mode-two-byte-compound-opcodes
           (ints-to-booleans (quote ,64-bit-compound-info))))

        (defconst *64-bit-mode-two-byte-66-ok-ar*
          (list-to-array
           '64-bit-mode-two-byte-66-ok
           (ints-to-booleans (quote ,64-bit-66-ok))))

        (defconst *64-bit-mode-two-byte-f3-ok-ar*
          (list-to-array
           '64-bit-mode-two-byte-f3-ok
           (ints-to-booleans (quote ,64-bit-f3-ok))))

        (defconst *64-bit-mode-two-byte-f2-ok-ar*
          (list-to-array
           '64-bit-mode-two-byte-f2-ok
           (ints-to-booleans (quote ,64-bit-f2-ok))))

        (defconst *32-bit-mode-two-byte-compound-opcodes-ar*
          (list-to-array
           '32-bit-mode-two-byte-compound-opcodes
           (ints-to-booleans (quote ,32-bit-compound-info))))

        (defconst *32-bit-mode-two-byte-66-ok-ar*
          (list-to-array
           '32-bit-mode-two-byte-66-ok
           (ints-to-booleans (quote ,32-bit-66-ok))))

        (defconst *32-bit-mode-two-byte-f3-ok-ar*
          (list-to-array
           '32-bit-mode-two-byte-f3-ok
           (ints-to-booleans (quote ,32-bit-f3-ok))))

        (defconst *32-bit-mode-two-byte-f2-ok-ar*
          (list-to-array
           '32-bit-mode-two-byte-f2-ok
           (ints-to-booleans (quote ,32-bit-f2-ok)))))))

  (make-event
   (b* (((mv 64-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* t))
        ((mv & 64-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* t :k :66))
        ((mv & 64-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* t :k :f3))
        ((mv & 64-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* t :k :f2))
        ((mv 32-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* nil))
        ((mv & 32-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* nil :k :66))
        ((mv & 32-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* nil :k :f3))
        ((mv & 32-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-38-three-byte-opcode-map-lst* nil :k :f2)))
     `(progn

        (defconst *64-bit-mode-0f-38-three-byte-compound-opcodes-ar*
          (list-to-array
           '64-bit-mode-0f-38-three-byte-compound-opcodes
           (ints-to-booleans (quote ,64-bit-compound-info))))

        (defconst *64-bit-mode-0f-38-three-byte-66-ok-ar*
          (list-to-array
           '64-bit-mode-0f-38-three-byte-66-ok
           (ints-to-booleans (quote ,64-bit-66-ok))))

        (defconst *64-bit-mode-0f-38-three-byte-f3-ok-ar*
          (list-to-array
           '64-bit-mode-0f-38-three-byte-f3-ok
           (ints-to-booleans (quote ,64-bit-f3-ok))))

        (defconst *64-bit-mode-0f-38-three-byte-f2-ok-ar*
          (list-to-array
           '64-bit-mode-0f-38-three-byte-f2-ok
           (ints-to-booleans (quote ,64-bit-f2-ok))))

        (defconst *32-bit-mode-0f-38-three-byte-compound-opcodes-ar*
          (list-to-array
           '32-bit-mode-0f-38-three-byte-compound-opcodes
           (ints-to-booleans (quote ,32-bit-compound-info))))

        (defconst *32-bit-mode-0f-38-three-byte-66-ok-ar*
          (list-to-array
           '32-bit-mode-0f-38-three-byte-66-ok
           (ints-to-booleans (quote ,32-bit-66-ok))))

        (defconst *32-bit-mode-0f-38-three-byte-f3-ok-ar*
          (list-to-array
           '32-bit-mode-0f-38-three-byte-f3-ok
           (ints-to-booleans (quote ,32-bit-f3-ok))))

        (defconst *32-bit-mode-0f-38-three-byte-f2-ok-ar*
          (list-to-array
           '32-bit-mode-0f-38-three-byte-f2-ok
           (ints-to-booleans (quote ,32-bit-f2-ok)))))))

  (make-event
   (b* (((mv 64-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* t))
        ((mv & 64-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* t :k :66))
        ((mv & 64-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* t :k :f3))
        ((mv & 64-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* t :k :f2))
        ((mv 32-bit-compound-info &)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* nil))
        ((mv & 32-bit-66-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* nil :k :66))
        ((mv & 32-bit-f3-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* nil :k :f3))
        ((mv & 32-bit-f2-ok)
         (compute-compound-cell-for-an-opcode-map
          *0F-3A-three-byte-opcode-map-lst* nil :k :f2)))
     `(progn

        (defconst *64-bit-mode-0f-3A-three-byte-compound-opcodes-ar*
          (list-to-array
           '64-bit-mode-0f-3A-three-byte-compound-opcodes
           (ints-to-booleans (quote ,64-bit-compound-info))))

        (defconst *64-bit-mode-0f-3A-three-byte-66-ok-ar*
          (list-to-array
           '64-bit-mode-0f-3A-three-byte-66-ok
           (ints-to-booleans (quote ,64-bit-66-ok))))

        (defconst *64-bit-mode-0f-3A-three-byte-f3-ok-ar*
          (list-to-array
           '64-bit-mode-0f-3A-three-byte-f3-ok
           (ints-to-booleans (quote ,64-bit-f3-ok))))

        (defconst *64-bit-mode-0f-3A-three-byte-f2-ok-ar*
          (list-to-array
           '64-bit-mode-0f-3A-three-byte-f2-ok
           (ints-to-booleans (quote ,64-bit-f2-ok))))

        (defconst *32-bit-mode-0f-3A-three-byte-compound-opcodes-ar*
          (list-to-array
           '32-bit-mode-0f-3A-three-byte-compound-opcodes
           (ints-to-booleans (quote ,32-bit-compound-info))))

        (defconst *32-bit-mode-0f-3A-three-byte-66-ok-ar*
          (list-to-array
           '32-bit-mode-0f-3A-three-byte-66-ok
           (ints-to-booleans (quote ,32-bit-66-ok))))

        (defconst *32-bit-mode-0f-3A-three-byte-f3-ok-ar*
          (list-to-array
           '32-bit-mode-0f-3A-three-byte-f3-ok
           (ints-to-booleans (quote ,32-bit-f3-ok))))

        (defconst *32-bit-mode-0f-3A-three-byte-f2-ok-ar*
          (list-to-array
           '32-bit-mode-0f-3A-three-byte-f2-ok
           (ints-to-booleans (quote ,32-bit-f2-ok))))))))

;; ----------------------------------------------------------------------

(defsection legacy-prefixes-decoding

  :short "Functions to detect and decode legacy prefixes"

  (local (xdoc::set-default-parents legacy-prefixes-decoding))

  ;; Legacy Prefix Byte Decoding (present only in the one-byte opcode map):
  (define compute-prefix-byte-group-code-of-one-opcode ((cell opcode-cell-p))

    :short "Takes in information of a single opcode from an opcode map and
  figures out if it is a prefix byte; if so, the prefix group number
  is returned."

    :long "<p>The return value @('0') corresponds to \"not a prefix\" and
  @('1'), @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>

   <p>Note that legacy prefixes are a part of the one-byte opcode map.</p>"

    (if (or (not (true-listp cell))
            (endp cell))

        0

      (b* ((first-elem (car cell)))
        (cond
         ((keywordp first-elem)
          (case first-elem
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

         (t 0)))))

  (define compute-prefix-byte-group-code-from-opcode-row ((row opcode-row-p)
                                                          (prefix true-listp))
    :short "Takes in a single opcode row from an opcode map and returns
  prefix byte info for each of the opcodes in that row"

    ;; The output list is reversed w.r.t. the input list,
    ;; but the results of all the rows are appended together
    ;; (in compute-prefix-byte-group-code-1),
    ;; and eventually reversed to be in the right order
    ;; (in compute-prefix-byte-group-code)

    (if (mbt (and (opcode-row-p row)
                  (true-listp prefix)))

        (if (atom row)
            prefix
          (let ((cell (car row)))
            (compute-prefix-byte-group-code-from-opcode-row
             (cdr row)
             (cons (compute-prefix-byte-group-code-of-one-opcode cell)
                   prefix))))

      nil))

  (define compute-prefix-byte-group-code-1 ((row-number natp)
                                            (map opcode-map-p))
    (if (mbt (and (natp row-number)
                  (opcode-map-p map)))

        (if (zp row-number)
            nil
          (b* ((row (nth (1- row-number) map))
               ((when (not (opcode-row-p row)))
                (er hard? "Expected: opcode-row-p: ~x0" row))
               (row-column-info
                (compute-prefix-byte-group-code-from-opcode-row row nil)))
            (append row-column-info
                    (compute-prefix-byte-group-code-1 (1- row-number) map))))
      nil))

  (define compute-prefix-byte-group-code ((map opcode-map-p))
    :short "Returns prefix byte information for an input opcode map"

    :long "<p>Source: Intel Manuals, Vol. 2, Section 2.1.1.</p>

 <p>The value @('0') corresponds to \"not a prefix\" and @('1'),
  @('2'), @('3') and @('4') correspond to the prefix group of
  byte.</p>"

    (reverse (compute-prefix-byte-group-code-1 (len map) map)))

  (make-event
   (b* ((precomputed-table
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             1 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table
         (compute-prefix-byte-group-code *one-byte-opcode-map-lst*))
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


(defsection mandatory-prefixes-computation

  :short "Functions to compute legal mandatory prefixes"

  :long "<p><b>When should we interpret a SIMD prefix (@('66'), @('F2'), and
 @('F3')) as a mandatory prefix for a given opcode in the two- and three-byte
 opcode maps?</b></p>

 <p>Suppose an opcode has @('F2') as the @('last-prefix') byte (see @(see
 legacy-prefixes-layout-structure)), but this opcode only has the following
 allowed variants: @('NP') (no prefix) and @('66').  Then @('F2') should be
 interpreted as a modifier to the @('NP') case and the instruction should not
 @('#UD').</p>

 <p>Example: @('F2 0F 6B') maps to the @('NP') variant of @('0F 6B (PACKSSDW)')
 because this opcode only has the @('NP') variant and @('66') as the allowed
 mandatory prefix.</p>

 <p>What if an opcode does not have the @('NP') variant but has a SIMD prefix
 that is not a supported variant as its @('last-prefix')?  Then the instruction
 should @('#UD').</p>

 <p>Example: @('F2 0F 6C') will @('#UD') because @('0F 6C') has no @('NP')
 variant and only has @('66') as the allowed mandatory prefix.</p>"

  (local (xdoc::set-default-parents mandatory-prefixes-computation))

  (define 64-bit-compute-mandatory-prefix-for-two-byte-opcode
    ((opcode        :type (unsigned-byte 8))
     (prefixes      :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '64-bit-mode-two-byte-F3-ok
                           *64-bit-mode-two-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '64-bit-mode-two-byte-F2-ok
                       *64-bit-mode-two-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '64-bit-mode-two-byte-66-ok
                  *64-bit-mode-two-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define 32-bit-compute-mandatory-prefix-for-two-byte-opcode
    ((opcode        :type (unsigned-byte 8))
     (prefixes      :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '32-bit-mode-two-byte-F3-ok
                           *32-bit-mode-two-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '32-bit-mode-two-byte-F2-ok
                       *32-bit-mode-two-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '32-bit-mode-two-byte-66-ok
                  *32-bit-mode-two-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define compute-mandatory-prefix-for-two-byte-opcode
    ((proc-mode     :type (integer 0 #.*num-proc-modes-1*))
     (opcode        :type (unsigned-byte 8))
     (prefixes      :type (unsigned-byte 55)))

    :inline t
    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d () (unsigned-byte-p)))))

    (case proc-mode
      (#.*64-bit-mode*
       (64-bit-compute-mandatory-prefix-for-two-byte-opcode
        opcode prefixes))
      (otherwise
       ;; TODO: Other modes.
       (32-bit-compute-mandatory-prefix-for-two-byte-opcode
        opcode prefixes))))

  (define 64-bit-compute-mandatory-prefix-for-0F-38-three-byte-opcode
    ((opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '64-bit-mode-0f-38-three-byte-F3-ok
                           *64-bit-mode-0f-38-three-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '64-bit-mode-0f-38-three-byte-F2-ok
                       *64-bit-mode-0f-38-three-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '64-bit-mode-0f-38-three-byte-66-ok
                  *64-bit-mode-0f-38-three-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define 32-bit-compute-mandatory-prefix-for-0F-38-three-byte-opcode
    ((opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '32-bit-mode-0f-38-three-byte-F3-ok
                           *32-bit-mode-0f-38-three-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '32-bit-mode-0f-38-three-byte-F2-ok
                       *32-bit-mode-0f-38-three-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '32-bit-mode-0f-38-three-byte-66-ok
                  *32-bit-mode-0f-38-three-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define compute-mandatory-prefix-for-0F-38-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))
    :inline t
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

  (define 64-bit-compute-mandatory-prefix-for-0F-3A-three-byte-opcode
    ((opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '64-bit-mode-0f-3A-three-byte-F3-ok
                           *64-bit-mode-0f-3A-three-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '64-bit-mode-0f-3A-three-byte-F2-ok
                       *64-bit-mode-0f-3A-three-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '64-bit-mode-0f-3A-three-byte-66-ok
                  *64-bit-mode-0f-3A-three-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define 32-bit-compute-mandatory-prefix-for-0F-3A-three-byte-opcode
    ((opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :returns (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix))

    (case (prefixes-slice :last-prefix prefixes)
      (#.*rep-pfx*
       (let ((rep-pfx (prefixes-slice :rep prefixes)))
         (cond
          ((or (and (equal rep-pfx  #.*mandatory-f3h*)
                    (aref1 '32-bit-mode-0f-3A-three-byte-F3-ok
                           *32-bit-mode-0f-3A-three-byte-F3-ok-ar* opcode))
               (and
                (equal rep-pfx #.*mandatory-f2h*)
                (aref1 '32-bit-mode-0f-3A-three-byte-F2-ok
                       *32-bit-mode-0f-3A-three-byte-F2-ok-ar* opcode)))
           rep-pfx)
          (t 0))))
      (#.*opr-pfx*
       (if (aref1 '32-bit-mode-0f-3A-three-byte-66-ok
                  *32-bit-mode-0f-3A-three-byte-66-ok-ar* opcode)
           (prefixes-slice :opr prefixes)
         0))
      (otherwise 0)))

  (define compute-mandatory-prefix-for-0F-3A-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :inline t
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
     (second-escape-byte :type (unsigned-byte 8))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte 55)))

    :inline t
    :guard (or (equal second-escape-byte #x38)
               (equal second-escape-byte #x3A))

    :returns (mandatory-prefix
              (unsigned-byte-p 8 mandatory-prefix)
              :hints (("Goal" :in-theory (e/d () (unsigned-byte-p)))))

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

  (define any-operand-with-prop?-aux ((prop   keywordp)
                                      (op_num :type (integer 0 *))
                                      (op_list alistp))
    :guard (or (equal prop :modr/m?)
               (equal prop :vex?))

    :short "Returns @('t') if at least one operand of a basic simple
  opcode (see @(see basic-simple-cell-p)) requires a @('ModR/M') byte or a
  @('VEX') prefix, depending on the value of @('prop')"
    ;; Example inputs are PROP = :MODR/M?, OP_NUM = 2, and OP_LIST = '((E b) (G
    ;; b)), extracted from '("ADD" 2 (E b) (G b)) entry in the
    ;; *ONE-BYTE-OPCODE-MAP-LST* table.  Note that only the uppercase letters
    ;; are used here (e.g. E and G in the example inputs just above), while the
    ;; lowercase letters are ignored.
    (b* (((when (not (equal (len op_list) op_num)))
          (er hard? "Expected length of ~x0 was ~x1." op_list op_num)))
      (if (zp op_num)
          nil
        (b* ((char (caar op_list))
             (this-opcode-prop?
              (cdr (assoc-equal prop
                                (cdr (assoc-equal
                                      char
                                      *Z-addressing-method-info*)))))
             ((when this-opcode-prop?)
              ;; Early out if this operand requires a ModR/M byte or VEX
              ;; prefix.
              t))
          (any-operand-with-prop?-aux prop (1- op_num) (cdr op_list))))))

  (define any-operand-with-prop? ((prop keywordp)
                                  (cell true-listp))

    :guard (or (equal prop :modr/m?)
               (equal prop :vex?))

    :short "Returns @('t') if at least one operand of a basic simple
  opcode requires a @('ModR/M') byte or a @('VEX') prefix"
    (b* (((when (not (basic-simple-cell-p cell)))
          (er hard? 'any-operand-with-prop?
              "Cell expected to be a basic-simple-cell-p: ~x0."
              cell))
         ((when (member-equal (car cell)
                              *simple-cells-standalone-legal-keywords*))
          0)
         ((when (< (len cell) 2))
          (er hard? 'any-operand-with-prop?
              "Len of column info field is < 2: ~x0."
              cell))
         (op_num (nth 1 cell))
         ((when (not (natp op_num)))
          (er hard? 'any-operand-with-prop?
              "We expected an op_num: ~x0." cell))
         ((when (and (eq prop :modr/m?)
                     (member-eq :1a cell)))
          ;; [Rob Sumners] modr/m byte is used in this case for processing
          ;; opcode extensions.
          1)
         (op_list
          ;; Need the "take" here to throw out superscripts like :1a,
          ;; etc.
          (take op_num (nthcdr 2 cell)))
         ((when (not (alistp op_list)))
          (er hard? 'any-operand-with-prop?
              "We expected an op_list: ~x0." cell))
         (prop? (any-operand-with-prop?-aux prop op_num op_list)))
      (acl2::bool->bit prop?)))

  (define any-operand-with-prop-for-simple-cells? ((prop  keywordp)
                                                   (cells true-list-listp))

    :guard (or (equal prop :modr/m?)
               (equal prop :vex?))

    :short "Returns @('t') if at least cell of a @(see
  basic-simple-cells-p) requires a @('ModR/M') byte or a @('VEX') prefix"
    ;; This function is only called by compute-prop-for-a-simple-cell.
    (if (or (not (basic-simple-cells-p cells))
            (endp cells))
        nil
      (or (any-operand-with-prop? prop (car cells))
          (any-operand-with-prop-for-simple-cells? prop (cdr cells)))))

  (define compute-prop-for-a-simple-cell ((prop keywordp)
                                          (cell true-listp))
    :short "Returns @('1') if a <i>simple</i> opcode requires a
  @('ModR/M') byte or a @('VEX') prefix"
    :long "<p>We call an opcode <i>simple</i> if it satisfies @(see
  simple-cell-p).</p>"

    :guard (or (equal prop :modr/m?)
               (equal prop :vex?))

    :guard-hints (("Goal" :in-theory (e/d (simple-cell-p) ())))

    ;; Example invocations:
    ;; (compute-prop-for-a-simple-cell :modr/m? '("ADD" 2 (E b)  (G b)))
    ;; (compute-prop-for-a-simple-cell :modr/m? '(:2-byte-escape))
    ;; (compute-prop-for-a-simple-cell :modr/m? '(:ALT
    ;;                                            (("VPMOVZXBW" 2 (V x)  (U x))
    ;;                                             ("VPMOVZXBW" 2 (V x)  (M q)))))

    (cond ((not (simple-cell-p cell))
           (er hard? 'compute-prop-for-a-simple-cell
               "Use this function for a simple cell only.~%~x0 is not simple!~%" cell))
          ((basic-simple-cell-p cell)
           (any-operand-with-prop? prop cell))
          ((and (equal (car cell) :ALT)
                (true-listp (cdr cell))
                (true-list-listp (car (cdr cell))))
           ;; See comment in *simple-cells-legal-keywords* for a
           ;; description of :ALT.
           (any-operand-with-prop-for-simple-cells? prop (car (cdr cell))))
          (t
           ;; We shouldn't reach here.
           (er hard? 'compute-prop-for-a-simple-cell
               "Cell info.: ~x0~%" cell))))

  (define compute-prop-for-an-opcode-cell ((prop keywordp)
                                           (cell true-listp)
                                           (64-bit-modep booleanp)
                                           &key
                                           ((k) ':NO-PREFIX))
    :guard (and (or (equal prop :modr/m?)
                    (equal prop :vex?))
                (compound-cells-legal-key-p k))
    :short "Returns @('1') if an opcode requires a @('ModR/M') byte or a
    @('VEX') prefix"

    :guard-hints (("Goal"
                   :do-not-induct t
                   :in-theory (e/d (not-consp-not-assoc-equal
                                    compound-cells-legal-key-p opcode-cell-p)
                                   (member-equal not))))

    (cond ((not (opcode-cell-p cell))
           (er hard? 'compute-prop-for-an-opcode-cell
               "Ill-formed opcode cell: ~x0~%" cell))
          ((simple-cell-p cell)
           (if (equal k ':NO-PREFIX)
               (compute-prop-for-a-simple-cell prop cell)
             0))
          (t ;; Compound cell
           (b* ((stripped-cell
                 ;; In 64-bit mode, we ignore the opcode information
                 ;; that is invalid in 64-bit mode, while in 32-bit
                 ;; mode, we ignore the opcode information that is valid
                 ;; only in 64-bit mode.
                 (if 64-bit-modep
                     (b* ((no-i64-cell (delete-assoc-equal :i64 cell))
                          (o64-cell    (cdr (assoc-equal :o64 no-i64-cell))))
                       (or o64-cell no-i64-cell))
                   (b* ((no-o64-cell (delete-assoc-equal :o64 cell))
                        (i64-cell    (cdr (assoc-equal :i64 no-o64-cell))))
                     (or i64-cell no-o64-cell))))
                ;; If a stripped cell is compound, then it can only have
                ;; the following legal keys now:
                ;; *compound-cells-legal-keys* - '(:i64 :o64)
                (relevant-simple-cell
                 (cond
                  ((compound-cell-p stripped-cell)
                   ;; The following should produce a simple-cell-p.
                   (cdr (assoc-equal k stripped-cell)))
                  (t
                   ;; Ignore k if stripped-cell is, e.g., a simple-cell-p or nil.
                   stripped-cell)))
                (computed-prop
                 ;; relevant-simple-cell may be nil.  E.g., for
                 ;; '((:no-prefix . ("PSHUFB"          2 (P q) (Q q)))
                 ;;   (:66        . ("VPSHUFB"         3 (V x) (H x) (W x))))
                 ;; looking for :F2 should return 0.

                 ;; Also: in 64-bit mode, for
                 ;; ((:i64 . ("PUSH ES" 0)))
                 ;; relevant-simple-cell will be nil.
                 (if (simple-cell-p relevant-simple-cell)
                     (compute-prop-for-a-simple-cell prop relevant-simple-cell)
                   0)))
             computed-prop))))

  (define compute-prop-for-an-opcode-row ((prop keywordp)
                                          (row true-list-listp)
                                          (64-bit-modep booleanp)
                                          &key
                                          ((k) ':NO-PREFIX))
    :guard (and (or (equal prop :modr/m?)
                    (equal prop :vex?))
                (compound-cells-legal-key-p k))

    :short "ModR/M byte or VEX prefix detection for an opcode row"
    :long "<p>This function simply calls @(see compute-prop-for-an-opcode-cell)
  recursively. It returns a list of 1s and 0s corresponding to the presence or
  absence of ModR/M byte or VEX prefix (depending on the value of @('prop'),
  for each opcode in an opcode row of the Intel opcode maps.</p>"

    (if (opcode-row-p row)
        (if (endp row)
            nil
          (b* ((cell (car row))
               (cell-prop
                (compute-prop-for-an-opcode-cell prop cell 64-bit-modep :k k)))
            (cons cell-prop
                  (compute-prop-for-an-opcode-row
                   prop (cdr row) 64-bit-modep :k k))))
      (er hard? 'compute-prop-for-an-opcode-row
          "Ill-formed opcode row: ~x0~%" row)))

  (define compute-prop-for-an-opcode-map ((prop keywordp)
                                          (map true-listp)
                                          (64-bit-modep booleanp)
                                          &key
                                          ((k) ':NO-PREFIX))
    :guard (and (or (equal prop :modr/m?)
                    (equal prop :vex?))
                (compound-cells-legal-key-p k))

    :guard-hints (("Goal" :in-theory (e/d (opcode-map-p) ())))

    :short "ModR/M byte or VEX prefix detection for an opcode map"
    :long "<p>This function simply calls @(see compute-prop-for-an-opcode-row)
  recursively. It returns a list of 1s and 0s corresponding to the presence or
  absence of ModR/M byte or VEX prefix, depending on the value of @('prop'),
  for each opcode in an opcode map.</p>"

    (if (opcode-map-p map)
        (if (endp map)
            nil
          (b* ((row (car map))
               (row-prop
                (compute-prop-for-an-opcode-row prop row 64-bit-modep :k k)))
            (append
             row-prop
             (compute-prop-for-an-opcode-map prop (cdr map) 64-bit-modep :k k))))
      (er hard? 'compute-prop-for-an-opcode-map
          "Ill-formed opcode map: ~x0~%" map)))

  (define compute-modr/m-for-vex-encoded-instructions-1
    ((vex-opcodes true-list-listp)
     (64-bit-modep booleanp))

    (if (endp vex-opcodes)
        nil
      (b* ((cell (car vex-opcodes)))
        (cons
         (compute-prop-for-an-opcode-cell :modr/m? cell 64-bit-modep)
         (compute-modr/m-for-vex-encoded-instructions-1
          (cdr vex-opcodes) 64-bit-modep)))))

  (define compute-modr/m-for-vex-encoded-instructions
    ((vex-map (avx-maps-well-formed-p vex-map t))
     (64-bit-modep booleanp))
    :guard-hints (("Goal" :in-theory (e/d (avx-maps-well-formed-p) ())))

    (if (atom vex-map)
        nil
      (b* ((row (car vex-map))
           (opcode (car row))
           (cells-pre (cdr row))
           ((unless (alistp cells-pre))
            (er hard? 'compute-modr/m-for-vex-encoded-instructions
                "Ill-formed VEX opcode row (it's not alistp): ~x0~%" row))
           (cells (acl2::flatten (strip-cdrs cells-pre)))
           ((unless (true-list-listp cells))
            (er hard? 'compute-modr/m-for-vex-encoded-instructions
                "Ill-formed VEX opcode row (it's not true-list-listp): ~x0~%" row))
           ;; (- (cw "~% Cells: ~p0 ~%" cells))
           )
        (cons
         (cons opcode
               (list (compute-modr/m-for-vex-encoded-instructions-1 cells 64-bit-modep)))
         (compute-modr/m-for-vex-encoded-instructions
          (cdr vex-map) 64-bit-modep))))))

;; ----------------------------------------------------------------------

(defsection ModR/M-decoding

  :short "Functions to detect and decode ModR/M bytes"

  (local (xdoc::set-default-parents ModR/M-decoding))

  ;;  ModR/M Arrays for One-byte Opcode Map:
  (make-event
   ;; For 64-bit mode:
   (b* ((precomputed-table
         '(1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
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
             0 0 0 0 0 0 1 1 0 0 0 0 0 0 1 1))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *one-byte-opcode-map-lst* t :k :NO-PREFIX))
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
         '(1 1 1 1 0 0 0 0 1 1 1 1 0 0 0 0
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
             0 0 0 0 0 0 1 1 0 0 0 0 0 0 1 1))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *one-byte-opcode-map-lst* nil :k :NO-PREFIX))
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
         '(1 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0
             1 1 1 1 1 1 1 1 1 0 0 0 0 0 0 1
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* t :k :NO-PREFIX))
        ((unless (equal precomputed-table computed-table))
         (er hard '64-bit-mode-two-byte-no-prefix-has-modr/m
             "Error: Incorrect ModR/M info computed!")))
     `(defconst *64-bit-mode-two-byte-no-prefix-has-modr/m-ar*
        (list-to-array '64-bit-mode-two-byte-no-prefix-has-modr/m
                       (ints-to-booleans
                        (quote ,computed-table))))))

  (make-event
   ;; For 64-bit mode: (:66)
   (b* ((precomputed-table
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             1 0 0 0 1 1 1 0 0 0 0 0 1 1 1 1
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 1 0 1 1 1 0 0 0 0 0 0 0 0 0
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* t :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* t :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0
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
             0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* t :k :F3))
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
         '(1 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0
             1 1 1 1 1 1 1 1 1 0 0 0 0 0 0 1
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* nil :k :NO-PREFIX))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             1 0 0 0 1 1 1 0 0 0 0 0 1 1 1 1
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 1 0 1 1 1 0 0 0 0 0 0 0 0 0
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
             0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* nil :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* nil :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             1 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0
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
             0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *two-byte-opcode-map-lst* nil :k :F3))
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
         '(1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
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
             1 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table
         (compute-prop-for-an-opcode-map
          :modr/m?
          *0F-38-three-byte-opcode-map-lst* t :k :NO-PREFIX))
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
         '(1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* t :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* t :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* t :k :F3))
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
         '(1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
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
             1 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* nil :k :NO-PREFIX))
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
         '(1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* nil :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* nil :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-38-three-byte-opcode-map-lst* nil :k :F3))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* t :k :NO-PREFIX))
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
         '(0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* t :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table
         (compute-prop-for-an-opcode-map
          :modr/m?
          *0F-3A-three-byte-opcode-map-lst* t :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* t :k :F3))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* nil :k :NO-PREFIX))
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
         '(0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* nil :k :66))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* nil :k :F2))
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
         '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
        (computed-table (compute-prop-for-an-opcode-map
                         :modr/m?
                         *0F-3A-three-byte-opcode-map-lst* nil :k :F3))
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
        :short "Returns a boolean saying whether, in 64-bit mode,
            the given opcode in the one-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))
        (aref1 '64-bit-mode-one-byte-has-modr/m
               *64-bit-mode-one-byte-has-modr/m-ar* opcode))

      (define 32-bit-mode-one-byte-opcode-ModR/M-p
        ((opcode :type (unsigned-byte 8)))
        :inline t
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

        (b* ((compound-opcode?
              (aref1 '64-bit-mode-two-byte-compound-opcodes
                     *64-bit-mode-two-byte-compound-opcodes-ar* opcode))
             ((unless compound-opcode?)
              (aref1 '64-bit-mode-two-byte-no-prefix-has-modr/m
                     *64-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode)))

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
             (aref1 '64-bit-mode-two-byte-no-prefix-has-modr/m
                    *64-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode)))))

      (define 32-bit-mode-two-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode           :type (unsigned-byte 8)
                           "Second byte of the two-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode,
            the given opcode in the two-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (b* ((compound-opcode?
              (aref1 '32-bit-mode-two-byte-compound-opcodes
                     *32-bit-mode-two-byte-compound-opcodes-ar* opcode))
             ((unless compound-opcode?)
              (aref1 '32-bit-mode-two-byte-no-prefix-has-modr/m
                     *32-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode)))

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
             (aref1 '32-bit-mode-two-byte-no-prefix-has-modr/m
                    *32-bit-mode-two-byte-no-prefix-has-modr/m-ar* opcode)))))

      (define two-byte-opcode-ModR/M-p
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (mandatory-prefix :type (unsigned-byte 8)
                           "As computed by @(tsee
                           compute-mandatory-prefix-for-two-byte-opcode)")
         (opcode           :type (unsigned-byte 8)
                           "Second byte of the two-byte opcode"))
        :short "Returns @('t') if a two-byte opcode requires a ModR/M byte;
        @('nil') otherwise. Doesn't account for AVX/AVX2/AVX512 instructions."
        :inline t
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

        (b* ((compound-opcode?
              (aref1 '64-bit-mode-0F-38-three-byte-compound-opcodes
                     *64-bit-mode-0F-38-three-byte-compound-opcodes-ar*
                     opcode))
             ((unless compound-opcode?)
              (aref1 '64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                     *64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                     opcode)))

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
             (aref1 '64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                    *64-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                    opcode)))))

      (define 32-bit-mode-0F-38-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 38 three-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode, the given
            opcode in the first three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (b* ((compound-opcode?
              (aref1 '32-bit-mode-0F-38-three-byte-compound-opcodes
                     *32-bit-mode-0F-38-three-byte-compound-opcodes-ar*
                     opcode))
             ((unless compound-opcode?)
              (aref1 '32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                     *32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                     opcode)))

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
             (aref1 '32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m
                    *32-bit-mode-0F-38-three-byte-no-prefix-has-modr/m-ar*
                    opcode)))))

      (define 64-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 3A three-byte opcode"))
        :short "Returns a boolean saying whether, in 64-bit mode, the given
            opcode in the second three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (b* ((compound-opcode?
              (aref1 '64-bit-mode-0F-3A-three-byte-compound-opcodes
                     *64-bit-mode-0F-3A-three-byte-compound-opcodes-ar*
                     opcode))
             ((unless compound-opcode?)
              (aref1 '64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                     *64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                     opcode)))

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
             (aref1 '64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                    *64-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                    opcode)))))

      (define 32-bit-mode-0F-3A-three-byte-opcode-ModR/M-p
        ((mandatory-prefix :type (unsigned-byte 8))
         (opcode   :type (unsigned-byte 8)
                   "Third byte of the 3A three-byte opcode"))
        :short "Returns a boolean saying whether, in 32-bit mode, the given
            opcode in the second three-byte opcode map expects a ModR/M byte."
        :returns (bool booleanp :hyp (n08p opcode))

        (b* ((compound-opcode?
              (aref1 '32-bit-mode-0F-3A-three-byte-compound-opcodes
                     *32-bit-mode-0F-3A-three-byte-compound-opcodes-ar*
                     opcode))
             ((unless compound-opcode?)
              (aref1 '32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                     *32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                     opcode)))

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
             (aref1 '32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m
                    *32-bit-mode-0F-3A-three-byte-no-prefix-has-modr/m-ar*
                    opcode)))))

      (define three-byte-opcode-ModR/M-p
        ((proc-mode        :type (integer 0 #.*num-proc-modes-1*))
         (mandatory-prefix :type (unsigned-byte 8)
                           "As computed by @(tsee
                           compute-mandatory-prefix-for-three-byte-opcode)")
         (escape-byte      :type (unsigned-byte 8)
                           "Second byte of the three-byte opcode --- either
                           @('#x38') or @('#x3A')")
         (opcode           :type (unsigned-byte 8)
                           "Third byte of the three-byte opcode"))
        :short "Returns @('t') if a three-byte opcode requires a ModR/M byte;
        @('nil') otherwise. Doesn't account for AVX/AVX2/AVX512 instructions."
        :inline t
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

  ;; ModR/M Detection Check for VEX-encoded instructions:

  (local
   (encapsulate
     ()

     (local
      (defun all-ones-p (lst)
        (if (atom lst)
            (equal lst nil)
          (and (equal (car lst) 1)
               (all-ones-p (cdr lst))))))

     (local
      (defun check-vex-map-modr/m-detection (lst 0f-map?)
        ;; lst: output of compute-modr/m-for-vex-encoded-instructions
        (if (atom lst)
            (equal lst nil)
          (b* ((opcode-info (car lst))
               ((unless (true-listp opcode-info))
                nil)
               (opcode (car opcode-info))
               (cells  (acl2::flatten (cdr opcode-info))))
            (if (all-ones-p cells)
                (check-vex-map-modr/m-detection (cdr lst) 0f-map?)
              (if 0f-map?
                  (and (equal opcode #x77)
                       ;; VZEROALL/VZEROUPPER don't expect a ModR/M.  Everything
                       ;; else that's VEX-encoded does.
                       (check-vex-map-modr/m-detection (cdr lst) 0f-map?))
                nil))))))

     (assert-event
      ;; Check: VZEROALL/VZEROUPPER are the only VEX-encoded opcodes that do NOT
      ;; expect a ModR/M byte.
      (and
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F-opcodes*   t)
        t)
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F38-opcodes*   t)
        nil)
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F3A-opcodes*   t)
        nil)
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F-opcodes*   nil)
        t)
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F38-opcodes*   nil)
        nil)
       (check-vex-map-modr/m-detection
        (compute-modr/m-for-vex-encoded-instructions *vex-0F3A-opcodes*   nil)
        nil)))))

  (define vex-opcode-ModR/M-p
    ((vex-prefixes     :type (unsigned-byte 24))
     (opcode           :type (unsigned-byte 8)))
    :short "Returns @('t') if a VEX-encoded opcode requires a ModR/M byte;
        @('nil') otherwise."
    :inline t
    :returns (bool booleanp)
    :guard (vex-prefixes-byte0-p vex-prefixes)
    (if (not (equal opcode #x77))
        t
      ;; VZEROALL/VZEROUPPER are the only two VEX-encoded instructions that do
      ;; not require a ModR/M byte.  These have the opcode #ux0F_77.
      ;; Also see compute-modr/m-for-vex-encoded-instructions above for more
      ;; details.
      (not (vex-prefixes-map-p #x0F vex-prefixes))))

  ;; We assume ModR/M is an unsigned-byte 8.
  (defmacro mrm-r/m (ModR/M)
    `(n03 ,ModR/M))

  (defmacro mrm-reg (ModR/M)
    `(mbe :logic (part-select ,ModR/M :low 3 :width 3)
          :exec (logand 7 (ash ,ModR/M -3))))

  (defmacro mrm-mod (ModR/M)
    `(mbe :logic (part-select ,ModR/M :low 6 :width 2)
          :exec (ash ,ModR/M -6))))

;; ----------------------------------------------------------------------

(defsection SIB-decoding

  :short "Functions to detect and decode SIB bytes"

  (local (xdoc::set-default-parents SIB-decoding))

  (define x86-decode-SIB-p
    ((ModR/M :type (unsigned-byte 8))
     (16-bit-addressp booleanp))
    :returns (bool booleanp :hyp (n08p ModR/M))
    :short "Returns a boolean saying whether a SIB byte is expected."
    :long
    "<p>
     This is based on Intel manual, Mar'17, Volume 2, Tables 2-1 and 2-2,
     as well as AMD manual, Dec'17, Volume 3, Tables A-33 and A-35.
     When the address size is 32 or 64 bits,
     Intel Table 2-2 and AMD Table A-35 apply:
     a SIB byte is expected exactly when
     ModR/M.mod is not #b11 and ModR/M.r/m is #b100.
     When the address size is 16 bits, no SIB byte is expected.
     </p>
     <p>
     The second argument of this function says whether
     the address size is 16 bits or not (i.e. 32 or 64 bits).
     In 64-bit mode, this argument is always @('nil').
     In 32-bit mode, this argument may be @('t') or @('nil').
     </p>"
    (and (not 16-bit-addressp)
         (let* ((r/m (mrm-r/m ModR/M))
                (mod (mrm-mod ModR/M)))
           (declare (type (unsigned-byte 8) r/m mod))
           (and (int= r/m 4)
                (not (int= mod 3))))))

  ;; We assume sib is an unsigned-byte 8.
  (defmacro sib-base (sib)
    `(n03 ,sib))

  (defmacro sib-index (sib)
    `(mbe :logic (part-select ,sib :low 3 :width 3)
          :exec (logand 7 (ash ,sib -3))))

  (defmacro sib-scale (sib)
    `(mbe :logic (part-select ,sib :low 6 :width 2)
          :exec (ash ,sib -6))))

;; ----------------------------------------------------------------------
