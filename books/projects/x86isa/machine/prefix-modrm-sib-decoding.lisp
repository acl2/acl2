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

  :short "Functions to pick legal mandatory prefixes"

  :long "<p><b>When should we interpret (@('66'), @('F2'), and @('F3')) as a
 mandatory prefix for a given opcode in the two- and three-byte opcode
 maps?</b></p>

 <p>Here are some decoding rules for SIMD mandatory prefixes; note that these
 don't apply for VEX/EVEX-encoded instructions because the mandatory prefixes
 are explicitly stated there.  All the examples listed below are from Intel's
 XED (x86 Encoder Decoder: https://intelxed.github.io/).</p>

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

  (local (xdoc::set-default-parents mandatory-prefixes-computation))

  ;; The following *error-** constants have been obtained by exhaustive testing
  ;; using Intel's XED (x86 Encoder Decoder: https://intelxed.github.io/).
  ;; That is, for every opcode in the two- and three-byte maps, we checked
  ;; XED's decoding output with all three SIMD prefixes.  A value of 1
  ;; associated with an opcode indicates that XED reported a decode error.
  ;; These constants are only really relevant for compound opcodes (as can be
  ;; seen in the compute-mandatory-prefix-* functions).  Also, they are the
  ;; same in the 32- and 64-bit modes of operation.

  (defconst *error-66-with-two-byte-opcode-alist*
    '((#ux00 . 0) (#ux01 . 0) (#ux02 . 0) (#ux03 . 0)
      (#ux04 . 1) (#ux05 . 0) (#ux06 . 0) (#ux07 . 0)
      (#ux08 . 0) (#ux09 . 0) (#ux0A . 1) (#ux0B . 0)
      (#ux0C . 1) (#ux0D . 0) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 0) (#ux11 . 0) (#ux12 . 0) (#ux13 . 0)
      (#ux14 . 0) (#ux15 . 0) (#ux16 . 0) (#ux17 . 0)
      (#ux18 . 0) (#ux19 . 0) (#ux1A . 0) (#ux1B . 0)
      (#ux1C . 0) (#ux1D . 0) (#ux1E . 0) (#ux1F . 0)
      (#ux20 . 0) (#ux21 . 0) (#ux22 . 0) (#ux23 . 0)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 0) (#ux29 . 0) (#ux2A . 0) (#ux2B . 0)
      (#ux2C . 0) (#ux2D . 0) (#ux2E . 0) (#ux2F . 0)
      (#ux30 . 0) (#ux31 . 0) (#ux32 . 0) (#ux33 . 0)
      (#ux34 . 0) (#ux35 . 0) (#ux36 . 1) (#ux37 . 0)
      (#ux38 . 0) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 0) (#ux41 . 0) (#ux42 . 0) (#ux43 . 0)
      (#ux44 . 0) (#ux45 . 0) (#ux46 . 0) (#ux47 . 0)
      (#ux48 . 0) (#ux49 . 0) (#ux4A . 0) (#ux4B . 0)
      (#ux4C . 0) (#ux4D . 0) (#ux4E . 0) (#ux4F . 0)
      (#ux50 . 1) (#ux51 . 0) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 0) (#ux55 . 0) (#ux56 . 0) (#ux57 . 0)
      (#ux58 . 0) (#ux59 . 0) (#ux5A . 0) (#ux5B . 0)
      (#ux5C . 0) (#ux5D . 0) (#ux5E . 0) (#ux5F . 0)
      (#ux60 . 0) (#ux61 . 0) (#ux62 . 0) (#ux63 . 0)
      (#ux64 . 0) (#ux65 . 0) (#ux66 . 0) (#ux67 . 0)
      (#ux68 . 0) (#ux69 . 0) (#ux6A . 0) (#ux6B . 0)
      (#ux6C . 0) (#ux6D . 0) (#ux6E . 0) (#ux6F . 0)
      (#ux70 . 0) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 0) (#ux75 . 0) (#ux76 . 0) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 0) (#ux7D . 0) (#ux7E . 0) (#ux7F . 0)
      (#ux80 . 0) (#ux81 . 0) (#ux82 . 0) (#ux83 . 0)
      (#ux84 . 0) (#ux85 . 0) (#ux86 . 0) (#ux87 . 0)
      (#ux88 . 0) (#ux89 . 0) (#ux8A . 0) (#ux8B . 0)
      (#ux8C . 0) (#ux8D . 0) (#ux8E . 0) (#ux8F . 0)
      (#ux90 . 0) (#ux91 . 0) (#ux92 . 0) (#ux93 . 0)
      (#ux94 . 0) (#ux95 . 0) (#ux96 . 0) (#ux97 . 0)
      (#ux98 . 0) (#ux99 . 0) (#ux9A . 0) (#ux9B . 0)
      (#ux9C . 0) (#ux9D . 0) (#ux9E . 0) (#ux9F . 0)
      (#uxA0 . 0) (#uxA1 . 0) (#uxA2 . 0) (#uxA3 . 0)
      (#uxA4 . 0) (#uxA5 . 0) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 0) (#uxA9 . 0) (#uxAA . 0) (#uxAB . 0)
      (#uxAC . 0) (#uxAD . 0) (#uxAE . 1) (#uxAF . 0)
      (#uxB0 . 0) (#uxB1 . 0) (#uxB2 . 0) (#uxB3 . 0)
      (#uxB4 . 0) (#uxB5 . 0) (#uxB6 . 0) (#uxB7 . 0)
      (#uxB8 . 1) (#uxB9 . 0) (#uxBA . 1) (#uxBB . 0)
      (#uxBC . 0) (#uxBD . 0) (#uxBE . 0) (#uxBF . 0)
      (#uxC0 . 0) (#uxC1 . 0) (#uxC2 . 0) (#uxC3 . 1)
      (#uxC4 . 0) (#uxC5 . 1) (#uxC6 . 0) (#uxC7 . 1)
      (#uxC8 . 0) (#uxC9 . 0) (#uxCA . 0) (#uxCB . 0)
      (#uxCC . 0) (#uxCD . 0) (#uxCE . 0) (#uxCF . 0)
      (#uxD0 . 0) (#uxD1 . 0) (#uxD2 . 0) (#uxD3 . 0)
      (#uxD4 . 0) (#uxD5 . 0) (#uxD6 . 0) (#uxD7 . 1)
      (#uxD8 . 0) (#uxD9 . 0) (#uxDA . 0) (#uxDB . 0)
      (#uxDC . 0) (#uxDD . 0) (#uxDE . 0) (#uxDF . 0)
      (#uxE0 . 0) (#uxE1 . 0) (#uxE2 . 0) (#uxE3 . 0)
      (#uxE4 . 0) (#uxE5 . 0) (#uxE6 . 0) (#uxE7 . 0)
      (#uxE8 . 0) (#uxE9 . 0) (#uxEA . 0) (#uxEB . 0)
      (#uxEC . 0) (#uxED . 0) (#uxEE . 0) (#uxEF . 0)
      (#uxF0 . 1) (#uxF1 . 0) (#uxF2 . 0) (#uxF3 . 0)
      (#uxF4 . 0) (#uxF5 . 0) (#uxF6 . 0) (#uxF7 . 1)
      (#uxF8 . 0) (#uxF9 . 0) (#uxFA . 0) (#uxFB . 0)
      (#uxFC . 0) (#uxFD . 0) (#uxFE . 0) (#uxFF . 0)))

  (local
   (defthm len-of-error-66-with-two-byte-opcode
     (equal (len *error-66-with-two-byte-opcode-alist*) 256)))

  (defconst *error-66-with-two-byte-opcode-ar*
    (list-to-array
     'error-66-with-two-byte-opcode
     (ints-to-booleans (strip-cdrs *error-66-with-two-byte-opcode-alist*))))

  (defconst *error-F2-with-two-byte-opcode-alist*
    '((#ux00 . 0) (#ux01 . 0) (#ux02 . 0) (#ux03 . 0)
      (#ux04 . 1) (#ux05 . 0) (#ux06 . 0) (#ux07 . 0)
      (#ux08 . 0) (#ux09 . 0) (#ux0A . 1) (#ux0B . 0)
      (#ux0C . 1) (#ux0D . 0) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 0) (#ux11 . 0) (#ux12 . 0) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 1) (#ux17 . 1)
      (#ux18 . 0) (#ux19 . 0) (#ux1A . 0) (#ux1B . 0)
      (#ux1C . 0) (#ux1D . 0) (#ux1E . 0) (#ux1F . 0)
      (#ux20 . 0) (#ux21 . 0) (#ux22 . 0) (#ux23 . 0)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 0) (#ux2B . 1)
      (#ux2C . 0) (#ux2D . 0) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 0) (#ux31 . 0) (#ux32 . 0) (#ux33 . 0)
      (#ux34 . 0) (#ux35 . 0) (#ux36 . 1) (#ux37 . 0)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 0) (#ux41 . 0) (#ux42 . 0) (#ux43 . 0)
      (#ux44 . 0) (#ux45 . 0) (#ux46 . 0) (#ux47 . 0)
      (#ux48 . 0) (#ux49 . 0) (#ux4A . 0) (#ux4B . 0)
      (#ux4C . 0) (#ux4D . 0) (#ux4E . 0) (#ux4F . 0)
      (#ux50 . 1) (#ux51 . 0) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 0) (#ux59 . 0) (#ux5A . 0) (#ux5B . 1)
      (#ux5C . 0) (#ux5D . 0) (#ux5E . 0) (#ux5F . 0)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 0) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 0) (#ux7D . 0) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 0) (#ux81 . 0) (#ux82 . 0) (#ux83 . 0)
      (#ux84 . 0) (#ux85 . 0) (#ux86 . 0) (#ux87 . 0)
      (#ux88 . 0) (#ux89 . 0) (#ux8A . 0) (#ux8B . 0)
      (#ux8C . 0) (#ux8D . 0) (#ux8E . 0) (#ux8F . 0)
      (#ux90 . 0) (#ux91 . 0) (#ux92 . 0) (#ux93 . 0)
      (#ux94 . 0) (#ux95 . 0) (#ux96 . 0) (#ux97 . 0)
      (#ux98 . 0) (#ux99 . 0) (#ux9A . 0) (#ux9B . 0)
      (#ux9C . 0) (#ux9D . 0) (#ux9E . 0) (#ux9F . 0)
      (#uxA0 . 0) (#uxA1 . 0) (#uxA2 . 0) (#uxA3 . 0)
      (#uxA4 . 0) (#uxA5 . 0) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 0) (#uxA9 . 0) (#uxAA . 0) (#uxAB . 0)
      (#uxAC . 0) (#uxAD . 0) (#uxAE . 1) (#uxAF . 0)
      (#uxB0 . 0) (#uxB1 . 0) (#uxB2 . 0) (#uxB3 . 0)
      (#uxB4 . 0) (#uxB5 . 0) (#uxB6 . 0) (#uxB7 . 0)
      (#uxB8 . 1) (#uxB9 . 0) (#uxBA . 1) (#uxBB . 0)
      (#uxBC . 0) (#uxBD . 0) (#uxBE . 0) (#uxBF . 0)
      (#uxC0 . 0) (#uxC1 . 0) (#uxC2 . 0) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 0) (#uxC9 . 0) (#uxCA . 0) (#uxCB . 0)
      (#uxCC . 0) (#uxCD . 0) (#uxCE . 0) (#uxCF . 0)
      (#uxD0 . 0) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 0) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 0) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 0)))

  (local
   (defthm len-of-error-F2-with-two-byte-opcode
     (equal (len *error-F2-with-two-byte-opcode-alist*) 256)))

  (defconst *error-F2-with-two-byte-opcode-ar*
    (list-to-array
     'error-F2-with-two-byte-opcode
     (ints-to-booleans (strip-cdrs *error-F2-with-two-byte-opcode-alist*))))

  (defconst *error-F3-with-two-byte-opcode-alist*
    '((#ux00 . 0) (#ux01 . 0) (#ux02 . 0) (#ux03 . 0)
      (#ux04 . 1) (#ux05 . 0) (#ux06 . 0) (#ux07 . 0)
      (#ux08 . 0) (#ux09 . 0) (#ux0A . 1) (#ux0B . 0)
      (#ux0C . 1) (#ux0D . 0) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 0) (#ux11 . 0) (#ux12 . 0) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 0) (#ux17 . 1)
      (#ux18 . 0) (#ux19 . 0) (#ux1A . 0) (#ux1B . 0)
      (#ux1C . 0) (#ux1D . 0) (#ux1E . 0) (#ux1F . 0)
      (#ux20 . 0) (#ux21 . 0) (#ux22 . 0) (#ux23 . 0)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 0) (#ux2B . 1)
      (#ux2C . 0) (#ux2D . 0) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 0) (#ux31 . 0) (#ux32 . 0) (#ux33 . 0)
      (#ux34 . 0) (#ux35 . 0) (#ux36 . 1) (#ux37 . 0)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 0) (#ux41 . 0) (#ux42 . 0) (#ux43 . 0)
      (#ux44 . 0) (#ux45 . 0) (#ux46 . 0) (#ux47 . 0)
      (#ux48 . 0) (#ux49 . 0) (#ux4A . 0) (#ux4B . 0)
      (#ux4C . 0) (#ux4D . 0) (#ux4E . 0) (#ux4F . 0)
      (#ux50 . 1) (#ux51 . 0) (#ux52 . 0) (#ux53 . 0)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 0) (#ux59 . 0) (#ux5A . 0) (#ux5B . 0)
      (#ux5C . 0) (#ux5D . 0) (#ux5E . 0) (#ux5F . 0)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 0)
      (#ux70 . 0) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 0) (#ux7F . 0)
      (#ux80 . 0) (#ux81 . 0) (#ux82 . 0) (#ux83 . 0)
      (#ux84 . 0) (#ux85 . 0) (#ux86 . 0) (#ux87 . 0)
      (#ux88 . 0) (#ux89 . 0) (#ux8A . 0) (#ux8B . 0)
      (#ux8C . 0) (#ux8D . 0) (#ux8E . 0) (#ux8F . 0)
      (#ux90 . 0) (#ux91 . 0) (#ux92 . 0) (#ux93 . 0)
      (#ux94 . 0) (#ux95 . 0) (#ux96 . 0) (#ux97 . 0)
      (#ux98 . 0) (#ux99 . 0) (#ux9A . 0) (#ux9B . 0)
      (#ux9C . 0) (#ux9D . 0) (#ux9E . 0) (#ux9F . 0)
      (#uxA0 . 0) (#uxA1 . 0) (#uxA2 . 0) (#uxA3 . 0)
      (#uxA4 . 0) (#uxA5 . 0) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 0) (#uxA9 . 0) (#uxAA . 0) (#uxAB . 0)
      (#uxAC . 0) (#uxAD . 0) (#uxAE . 1) (#uxAF . 0)
      (#uxB0 . 0) (#uxB1 . 0) (#uxB2 . 0) (#uxB3 . 0)
      (#uxB4 . 0) (#uxB5 . 0) (#uxB6 . 0) (#uxB7 . 0)
      (#uxB8 . 0) (#uxB9 . 0) (#uxBA . 1) (#uxBB . 0)
      (#uxBC . 0) (#uxBD . 0) (#uxBE . 0) (#uxBF . 0)
      (#uxC0 . 0) (#uxC1 . 0) (#uxC2 . 0) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 0) (#uxC9 . 0) (#uxCA . 0) (#uxCB . 0)
      (#uxCC . 0) (#uxCD . 0) (#uxCE . 0) (#uxCF . 0)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 0) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 1) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 0)))

  (local
   (defthm len-of-error-F3-with-two-byte-opcode
     (equal (len *error-F3-with-two-byte-opcode-alist*) 256)))

  (defconst *error-F3-with-two-byte-opcode-ar*
    (list-to-array
     'error-F3-with-two-byte-opcode
     (ints-to-booleans (strip-cdrs *error-F3-with-two-byte-opcode-alist*))))

  (defconst *error-66-with-0F-38-three-byte-opcode-alist*
    '((#ux00 . 0) (#ux01 . 0) (#ux02 . 0) (#ux03 . 0)
      (#ux04 . 0) (#ux05 . 0) (#ux06 . 0) (#ux07 . 0)
      (#ux08 . 0) (#ux09 . 0) (#ux0A . 0) (#ux0B . 0)
      (#ux0C . 1) (#ux0D . 1) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 0) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 0) (#ux15 . 0) (#ux16 . 1) (#ux17 . 0)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 0) (#ux1D . 0) (#ux1E . 0) (#ux1F . 1)
      (#ux20 . 0) (#ux21 . 0) (#ux22 . 0) (#ux23 . 0)
      (#ux24 . 0) (#ux25 . 0) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 0) (#ux29 . 0) (#ux2A . 0) (#ux2B . 0)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 0) (#ux31 . 0) (#ux32 . 0) (#ux33 . 0)
      (#ux34 . 0) (#ux35 . 0) (#ux36 . 1) (#ux37 . 0)
      (#ux38 . 0) (#ux39 . 0) (#ux3A . 0) (#ux3B . 0)
      (#ux3C . 0) (#ux3D . 0) (#ux3E . 0) (#ux3F . 0)
      (#ux40 . 0) (#ux41 . 0) (#ux42 . 1) (#ux43 . 1)
      (#ux44 . 1) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 0) (#ux81 . 0) (#ux82 . 0) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 0)
      (#uxDC . 0) (#uxDD . 0) (#uxDE . 0) (#uxDF . 0)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 0) (#uxF1 . 0) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 0) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-66-with-0F-38-three-byte-opcode
     (equal (len *error-66-with-0F-38-three-byte-opcode-alist*) 256)))

  (defconst *error-66-with-0F-38-three-byte-opcode-ar*
    (list-to-array
     'error-66-with-0F-38-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-66-with-0F-38-three-byte-opcode-alist*))))

  (defconst *error-F2-with-0F-38-three-byte-opcode-alist*
    '((#ux00 . 1) (#ux01 . 1) (#ux02 . 1) (#ux03 . 1)
      (#ux04 . 1) (#ux05 . 1) (#ux06 . 1) (#ux07 . 1)
      (#ux08 . 1) (#ux09 . 1) (#ux0A . 1) (#ux0B . 1)
      (#ux0C . 1) (#ux0D . 1) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 1) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 1) (#ux17 . 1)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 1) (#ux1D . 1) (#ux1E . 1) (#ux1F . 1)
      (#ux20 . 1) (#ux21 . 1) (#ux22 . 1) (#ux23 . 1)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 1) (#ux2B . 1)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 1) (#ux31 . 1) (#ux32 . 1) (#ux33 . 1)
      (#ux34 . 1) (#ux35 . 1) (#ux36 . 1) (#ux37 . 1)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 1) (#ux41 . 1) (#ux42 . 1) (#ux43 . 1)
      (#ux44 . 1) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 1) (#ux81 . 1) (#ux82 . 1) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 0) (#uxF1 . 0) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-F2-with-0F-38-three-byte-opcode
     (equal (len *error-F2-with-0F-38-three-byte-opcode-alist*) 256)))

  (defconst *error-F2-with-0F-38-three-byte-opcode-ar*
    (list-to-array
     'error-F2-with-0F-38-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-F2-with-0F-38-three-byte-opcode-alist*))))

  (defconst *error-F3-with-0F-38-three-byte-opcode-alist*
    '((#ux00 . 1) (#ux01 . 1) (#ux02 . 1) (#ux03 . 1)
      (#ux04 . 1) (#ux05 . 1) (#ux06 . 1) (#ux07 . 1)
      (#ux08 . 1) (#ux09 . 1) (#ux0A . 1) (#ux0B . 1)
      (#ux0C . 1) (#ux0D . 1) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 1) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 1) (#ux17 . 1)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 1) (#ux1D . 1) (#ux1E . 1) (#ux1F . 1)
      (#ux20 . 1) (#ux21 . 1) (#ux22 . 1) (#ux23 . 1)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 1) (#ux2B . 1)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 1) (#ux31 . 1) (#ux32 . 1) (#ux33 . 1)
      (#ux34 . 1) (#ux35 . 1) (#ux36 . 1) (#ux37 . 1)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 1) (#ux41 . 1) (#ux42 . 1) (#ux43 . 1)
      (#ux44 . 1) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 1) (#ux81 . 1) (#ux82 . 1) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 1) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 0) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-F3-with-0F-38-three-byte-opcode
     (equal (len *error-F3-with-0F-38-three-byte-opcode-alist*) 256)))

  (defconst *error-F3-with-0F-38-three-byte-opcode-ar*
    (list-to-array
     'error-F3-with-0F-38-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-F3-with-0F-38-three-byte-opcode-alist*))))


  (defconst *error-66-with-0F-3A-three-byte-opcode-alist*
    '((#ux00 . 1) (#ux01 . 1) (#ux02 . 1) (#ux03 . 1)
      (#ux04 . 1) (#ux05 . 1) (#ux06 . 1) (#ux07 . 1)
      (#ux08 . 0) (#ux09 . 0) (#ux0A . 0) (#ux0B . 0)
      (#ux0C . 0) (#ux0D . 0) (#ux0E . 0) (#ux0F . 0)
      (#ux10 . 1) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 0) (#ux15 . 0) (#ux16 . 0) (#ux17 . 0)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 1) (#ux1D . 1) (#ux1E . 1) (#ux1F . 1)
      (#ux20 . 0) (#ux21 . 0) (#ux22 . 0) (#ux23 . 1)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 1) (#ux2B . 1)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 1) (#ux31 . 1) (#ux32 . 1) (#ux33 . 1)
      (#ux34 . 1) (#ux35 . 1) (#ux36 . 1) (#ux37 . 1)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 0) (#ux41 . 0) (#ux42 . 0) (#ux43 . 1)
      (#ux44 . 0) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 0) (#ux61 . 0) (#ux62 . 0) (#ux63 . 0)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 1) (#ux81 . 1) (#ux82 . 1) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 0)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 1) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-66-with-0F-3A-three-byte-opcode
     (equal (len *error-66-with-0F-3A-three-byte-opcode-alist*) 256)))

  (defconst *error-66-with-0F-3A-three-byte-opcode-ar*
    (list-to-array
     'error-66-with-0F-3A-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-66-with-0F-3A-three-byte-opcode-alist*))))

  (defconst *error-F2-with-0F-3A-three-byte-opcode-alist*
    '((#ux00 . 1) (#ux01 . 1) (#ux02 . 1) (#ux03 . 1)
      (#ux04 . 1) (#ux05 . 1) (#ux06 . 1) (#ux07 . 1)
      (#ux08 . 1) (#ux09 . 1) (#ux0A . 1) (#ux0B . 1)
      (#ux0C . 1) (#ux0D . 1) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 1) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 1) (#ux17 . 1)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 1) (#ux1D . 1) (#ux1E . 1) (#ux1F . 1)
      (#ux20 . 1) (#ux21 . 1) (#ux22 . 1) (#ux23 . 1)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 1) (#ux2B . 1)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 1) (#ux31 . 1) (#ux32 . 1) (#ux33 . 1)
      (#ux34 . 1) (#ux35 . 1) (#ux36 . 1) (#ux37 . 1)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 1) (#ux41 . 1) (#ux42 . 1) (#ux43 . 1)
      (#ux44 . 1) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 1) (#ux81 . 1) (#ux82 . 1) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 1) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-F2-with-0F-3A-three-byte-opcode
     (equal (len *error-F2-with-0F-3A-three-byte-opcode-alist*) 256)))

  (defconst *error-F2-with-0F-3A-three-byte-opcode-ar*
    (list-to-array
     'error-F2-with-0F-3A-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-F2-with-0F-3A-three-byte-opcode-alist*))))

  (defconst *error-F3-with-0F-3A-three-byte-opcode-alist*
    '((#ux00 . 1) (#ux01 . 1) (#ux02 . 1) (#ux03 . 1)
      (#ux04 . 1) (#ux05 . 1) (#ux06 . 1) (#ux07 . 1)
      (#ux08 . 1) (#ux09 . 1) (#ux0A . 1) (#ux0B . 1)
      (#ux0C . 1) (#ux0D . 1) (#ux0E . 1) (#ux0F . 1)
      (#ux10 . 1) (#ux11 . 1) (#ux12 . 1) (#ux13 . 1)
      (#ux14 . 1) (#ux15 . 1) (#ux16 . 1) (#ux17 . 1)
      (#ux18 . 1) (#ux19 . 1) (#ux1A . 1) (#ux1B . 1)
      (#ux1C . 1) (#ux1D . 1) (#ux1E . 1) (#ux1F . 1)
      (#ux20 . 1) (#ux21 . 1) (#ux22 . 1) (#ux23 . 1)
      (#ux24 . 1) (#ux25 . 1) (#ux26 . 1) (#ux27 . 1)
      (#ux28 . 1) (#ux29 . 1) (#ux2A . 1) (#ux2B . 1)
      (#ux2C . 1) (#ux2D . 1) (#ux2E . 1) (#ux2F . 1)
      (#ux30 . 1) (#ux31 . 1) (#ux32 . 1) (#ux33 . 1)
      (#ux34 . 1) (#ux35 . 1) (#ux36 . 1) (#ux37 . 1)
      (#ux38 . 1) (#ux39 . 1) (#ux3A . 1) (#ux3B . 1)
      (#ux3C . 1) (#ux3D . 1) (#ux3E . 1) (#ux3F . 1)
      (#ux40 . 1) (#ux41 . 1) (#ux42 . 1) (#ux43 . 1)
      (#ux44 . 1) (#ux45 . 1) (#ux46 . 1) (#ux47 . 1)
      (#ux48 . 1) (#ux49 . 1) (#ux4A . 1) (#ux4B . 1)
      (#ux4C . 1) (#ux4D . 1) (#ux4E . 1) (#ux4F . 1)
      (#ux50 . 1) (#ux51 . 1) (#ux52 . 1) (#ux53 . 1)
      (#ux54 . 1) (#ux55 . 1) (#ux56 . 1) (#ux57 . 1)
      (#ux58 . 1) (#ux59 . 1) (#ux5A . 1) (#ux5B . 1)
      (#ux5C . 1) (#ux5D . 1) (#ux5E . 1) (#ux5F . 1)
      (#ux60 . 1) (#ux61 . 1) (#ux62 . 1) (#ux63 . 1)
      (#ux64 . 1) (#ux65 . 1) (#ux66 . 1) (#ux67 . 1)
      (#ux68 . 1) (#ux69 . 1) (#ux6A . 1) (#ux6B . 1)
      (#ux6C . 1) (#ux6D . 1) (#ux6E . 1) (#ux6F . 1)
      (#ux70 . 1) (#ux71 . 1) (#ux72 . 1) (#ux73 . 1)
      (#ux74 . 1) (#ux75 . 1) (#ux76 . 1) (#ux77 . 1)
      (#ux78 . 1) (#ux79 . 1) (#ux7A . 1) (#ux7B . 1)
      (#ux7C . 1) (#ux7D . 1) (#ux7E . 1) (#ux7F . 1)
      (#ux80 . 1) (#ux81 . 1) (#ux82 . 1) (#ux83 . 1)
      (#ux84 . 1) (#ux85 . 1) (#ux86 . 1) (#ux87 . 1)
      (#ux88 . 1) (#ux89 . 1) (#ux8A . 1) (#ux8B . 1)
      (#ux8C . 1) (#ux8D . 1) (#ux8E . 1) (#ux8F . 1)
      (#ux90 . 1) (#ux91 . 1) (#ux92 . 1) (#ux93 . 1)
      (#ux94 . 1) (#ux95 . 1) (#ux96 . 1) (#ux97 . 1)
      (#ux98 . 1) (#ux99 . 1) (#ux9A . 1) (#ux9B . 1)
      (#ux9C . 1) (#ux9D . 1) (#ux9E . 1) (#ux9F . 1)
      (#uxA0 . 1) (#uxA1 . 1) (#uxA2 . 1) (#uxA3 . 1)
      (#uxA4 . 1) (#uxA5 . 1) (#uxA6 . 1) (#uxA7 . 1)
      (#uxA8 . 1) (#uxA9 . 1) (#uxAA . 1) (#uxAB . 1)
      (#uxAC . 1) (#uxAD . 1) (#uxAE . 1) (#uxAF . 1)
      (#uxB0 . 1) (#uxB1 . 1) (#uxB2 . 1) (#uxB3 . 1)
      (#uxB4 . 1) (#uxB5 . 1) (#uxB6 . 1) (#uxB7 . 1)
      (#uxB8 . 1) (#uxB9 . 1) (#uxBA . 1) (#uxBB . 1)
      (#uxBC . 1) (#uxBD . 1) (#uxBE . 1) (#uxBF . 1)
      (#uxC0 . 1) (#uxC1 . 1) (#uxC2 . 1) (#uxC3 . 1)
      (#uxC4 . 1) (#uxC5 . 1) (#uxC6 . 1) (#uxC7 . 1)
      (#uxC8 . 1) (#uxC9 . 1) (#uxCA . 1) (#uxCB . 1)
      (#uxCC . 1) (#uxCD . 1) (#uxCE . 1) (#uxCF . 1)
      (#uxD0 . 1) (#uxD1 . 1) (#uxD2 . 1) (#uxD3 . 1)
      (#uxD4 . 1) (#uxD5 . 1) (#uxD6 . 1) (#uxD7 . 1)
      (#uxD8 . 1) (#uxD9 . 1) (#uxDA . 1) (#uxDB . 1)
      (#uxDC . 1) (#uxDD . 1) (#uxDE . 1) (#uxDF . 1)
      (#uxE0 . 1) (#uxE1 . 1) (#uxE2 . 1) (#uxE3 . 1)
      (#uxE4 . 1) (#uxE5 . 1) (#uxE6 . 1) (#uxE7 . 1)
      (#uxE8 . 1) (#uxE9 . 1) (#uxEA . 1) (#uxEB . 1)
      (#uxEC . 1) (#uxED . 1) (#uxEE . 1) (#uxEF . 1)
      (#uxF0 . 1) (#uxF1 . 1) (#uxF2 . 1) (#uxF3 . 1)
      (#uxF4 . 1) (#uxF5 . 1) (#uxF6 . 1) (#uxF7 . 1)
      (#uxF8 . 1) (#uxF9 . 1) (#uxFA . 1) (#uxFB . 1)
      (#uxFC . 1) (#uxFD . 1) (#uxFE . 1) (#uxFF . 1)))

  (local
   (defthm len-of-error-F3-with-0F-3A-three-byte-opcode
     (equal (len *error-F3-with-0F-3A-three-byte-opcode-alist*) 256)))

  (defconst *error-F3-with-0F-3A-three-byte-opcode-ar*
    (list-to-array
     'error-F3-with-0F-3A-three-byte-opcode
     (ints-to-booleans (strip-cdrs
                        *error-F3-with-0F-3A-three-byte-opcode-alist*))))


  (local (include-book "std/strings/decimal" :dir :system))


  (local
   (define gen-compute-mandatory-prefix-fn
     ((map (member-equal map '(#ux0F #ux0F_38 #ux0F_3A)))
      (mode (member-equal mode '(32 64))))

     (b* ((mode-name (str::cat (str::natstr mode) "-BIT"))
          (pre-name (str::cat mode-name "-COMPUTE-MANDATORY-PREFIX-FOR-"))
          (map-name (case map
                      (#ux0F    "TWO-BYTE")
                      (#ux0F_38 "0F-38-THREE-BYTE")
                      (#ux0F_3A "0F-3A-THREE-BYTE")))
          (name (intern$ (str::cat pre-name map-name "-OPCODE") "X86ISA"))
          (compound-opcode-name-crux
           (str::cat mode-name "-MODE-" map-name "-COMPOUND-OPCODES"))
          (compound-opcode-name
           (intern$ compound-opcode-name-crux "X86ISA"))
          (compound-opcode-const
           (intern$ (str::cat "*" compound-opcode-name-crux "-AR*")
                    "X86ISA"))

          (F3-ok-crux
           (str::cat mode-name "-MODE-" map-name "-F3-OK"))
          (F3-ok (intern$ F3-ok-crux "X86ISA"))
          (F3-ok-const (intern$ (str::cat "*" F3-ok-crux "-AR*") "X86ISA"))
          (F3-error-crux
           (str::cat "ERROR-F3-WITH-" map-name "-OPCODE"))
          (F3-error
           (intern$ F3-error-crux "X86ISA"))
          (F3-error-const
           (intern$ (str::cat "*" F3-error-crux "-AR*") "X86ISA"))

          (F2-ok-crux
           (str::cat mode-name "-MODE-" map-name "-F2-OK"))
          (F2-ok (intern$ F2-ok-crux "X86ISA"))
          (F2-ok-const (intern$ (str::cat "*" F2-ok-crux "-AR*") "X86ISA"))
          (F2-error-crux
           (str::cat "ERROR-F2-WITH-" map-name "-OPCODE"))
          (F2-error
           (intern$ F2-error-crux "X86ISA"))
          (F2-error-const
           (intern$ (str::cat "*" F2-error-crux "-AR*") "X86ISA"))

          (66-ok-crux
           (str::cat mode-name "-MODE-" map-name "-66-OK"))
          (66-ok (intern$ 66-ok-crux "X86ISA"))
          (66-ok-const (intern$ (str::cat "*" 66-ok-crux "-AR*") "X86ISA"))
          (66-error-crux
           (str::cat "ERROR-66-WITH-" map-name "-OPCODE"))
          (66-error
           (intern$ 66-error-crux "X86ISA"))
          (66-error-const
           (intern$ (str::cat "*" 66-error-crux "-AR*") "X86ISA")))

       `(define ,name
          ((opcode        :type (unsigned-byte 8)
                          "Relevant opcode byte")
           (prefixes      :type (unsigned-byte #.*prefixes-width*)))

          :returns (mv
                    err-flg
                    (mandatory-prefix (unsigned-byte-p 8 mandatory-prefix)))

          (b* ((compound-opcode?
                (aref1 ',compound-opcode-name
                       ,compound-opcode-const
                       opcode))
               ((unless compound-opcode?)
                ;; Return 0 if the opcode is not allowed to have any mandatory
                ;; prefixes.  In this case, if 66/F3/F2 are present, they assume
                ;; their normal roles as modifier prefixes.
                (mv nil 0)))

            (let ((rep-pfx (prefixes-slice :rep prefixes)))

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

                      (mv nil rep-pfx)

                    ;; If F2/F3 is used with an opcode that does not support these
                    ;; prefixes as mandatory prefixes, then we look whether the use
                    ;; of these prefixes with this opcode causes an error.

                    (if (or (and (equal rep-pfx #.*mandatory-f3h*)
                                 (not (aref1 ',F3-error ,F3-error-const opcode)))
                            (and (equal rep-pfx #.*mandatory-f2h*)
                                 (not (aref1 ',F2-error ,F2-error-const opcode))))

                        ;; F2/F3 are used as modifier prefixes.

                        (mv nil 0)

                      (mv (list :illegal-use-of-mandatory-prefix rep-pfx
                                :opcode ,map opcode)
                          0)))

                ;; If F2/F3 are not present, then we check for 66 prefix.
                (let ((opr-pfx  (prefixes-slice :opr prefixes)))

                  (if (not (eql opr-pfx 0))

                      (if (aref1 ',66-ok ,66-ok-const opcode)

                          (mv nil opr-pfx)

                        ;; If 66 is used with an opcode that does not support it
                        ;; as a mandatory prefix, then we look whether the use of
                        ;; this prefixes with this opcode causes an error.

                        (if (not (aref1 ',66-error ,66-error-const opcode))

                            ;; 66 is used as a modifier prefix.
                            (mv nil 0)

                          (mv (list :illegal-use-of-mandatory-prefix opr-pfx
                                    :opcode ,map opcode)
                              0)))

                    ;; No mandatory prefixes present.
                    (mv nil 0))))))))))

  (make-event
   `(progn
      ,(gen-compute-mandatory-prefix-fn #ux0F    64)
      ,(gen-compute-mandatory-prefix-fn #ux0F    32)
      ,(gen-compute-mandatory-prefix-fn #ux0F_38 64)
      ,(gen-compute-mandatory-prefix-fn #ux0F_38 32)
      ,(gen-compute-mandatory-prefix-fn #ux0F_3A 64)
      ,(gen-compute-mandatory-prefix-fn #ux0F_3A 32)))

  (define compute-mandatory-prefix-for-two-byte-opcode
    ((proc-mode     :type (integer 0 #.*num-proc-modes-1*))
     (opcode        :type (unsigned-byte 8)
                    "Second byte of a two-byte opcode")
     (prefixes      :type (unsigned-byte #.*prefixes-width*)))

    :inline t
    :returns (mv
              err-flg
              (mandatory-prefix
               (unsigned-byte-p 8 mandatory-prefix)
               :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))))
    :short "Two-byte Opcodes: picks the appropriate SIMD prefix as the
    mandatory prefix, if applicable"

    (case proc-mode
      (#.*64-bit-mode*
       (64-bit-compute-mandatory-prefix-for-two-byte-opcode
        opcode prefixes))
      (otherwise
       ;; TODO: Other modes.
       (32-bit-compute-mandatory-prefix-for-two-byte-opcode
        opcode prefixes))))

  (define compute-mandatory-prefix-for-0F-38-three-byte-opcode
    ((proc-mode          :type (integer 0 #.*num-proc-modes-1*))
     (opcode             :type (unsigned-byte 8))
     (prefixes           :type (unsigned-byte #.*prefixes-width*)))
    :inline t
    :returns (mv
              err-flg
              (mandatory-prefix
               (unsigned-byte-p 8 mandatory-prefix)
               :hints (("Goal" :in-theory (e/d ()
                                               (unsigned-byte-p))))))

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
    :returns (mv err-flg
                 (mandatory-prefix
                  (unsigned-byte-p 8 mandatory-prefix)
                  :hints (("Goal" :in-theory (e/d ()
                                                  (unsigned-byte-p))))))

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
    :guard (or (equal second-escape-byte #x38)
               (equal second-escape-byte #x3A))

    :returns (mv err-flg
                 (mandatory-prefix
                  (unsigned-byte-p 8 mandatory-prefix)
                  :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))))

    :short "Three-byte opcodes: picks the appropriate SIMD prefix as the
    mandatory prefix, if applicable"

    (case second-escape-byte
      (#x38
       (compute-mandatory-prefix-for-0F-38-three-byte-opcode
        proc-mode opcode prefixes))
      (#x3A
       (compute-mandatory-prefix-for-0F-3A-three-byte-opcode
        proc-mode opcode prefixes))
      (otherwise
       (mv nil 0)))))

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
