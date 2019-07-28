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
; Contributing Author(s):
; Rob Sumners         <rob.sumners@gmail.com>

(in-package "X86ISA")
(include-book "../utils/basic-structs")
(include-book "std/util/defenum" :dir :system)
(include-book "cpuid-constants")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/lists/duplicity" :dir :system)
(include-book "std/strings/hexify" :dir :system)

(defsection opcode-maps-structures
  :parents (structures opcode-maps)
  :short "Structures for representing of Intel's x86 Opcode Maps in ACL2"
  )

(local (xdoc::set-default-parents 'opcode-maps-structures))

;; ----------------------------------------------------------------------

;; Addressing Information:

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

   '(A (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "Direct address: the instruction has no ModR/M byte; the address
             of the operand is encoded in the instruction. No base register,
             index register, or scaling factor can be applied (for example far
             JMP (EA))."))

   '(B (:modr/m? . nil) (:vex? . t)
       (:doc .
             "The VEX.vvvv field of the VEX prefix selects a general purpose
             register."))


   '(C (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The reg field of the ModR/M byte selects a control register (for
             example MOV (0F20, 0F22))."))

   '(D (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The reg field of the ModR/M byte selects a debug register (for
             example MOV (0F21,0F23))."))

   '(E (:modr/m? . t) (:vex? . nil)
       (:doc .
             "A ModR/M byte follows the opcode and specifies the operand. The
             operand is either a general-purpose register or a memory
             address. If it is a memory address the address is computed from a
             segment register and any of the following values: a base register,
             an index register, a scaling factor,a displacement."))

   '(F (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "EFLAGS/RFLAGS Register."))

   '(G (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The reg field of the ModR/M byte selects a general register (for
             example AX (000))."))

   '(H (:modr/m? . nil) (:vex? . t)
       (:doc .
             "The VEX.vvvv field of the VEX prefix selects a 128-bit XMM
             register or a 256-bit YMM register determined by operand type. For
             legacy SSE encodings this operand does not exist, changing the
             instruction to destructive form."))

   '(I (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "Immediate data: the operand value is encoded in subsequent bytes
             of the instruction."))

   '(J (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "The instruction contains a relative offset to be added to the
             instruction pointer register (for example JMP (0E9), LOOP)."))

   ;; Important: Note that rB, mB are not listed as Z addressing methods in the
   ;; Intel manuals (May 2018 edition).  I borrowed them from the following:
   ;; http://sandpile.org/x86/opc_enc.htm.

   '(rB (:modr/m? . t) (:vex? . nil)
        (:doc .
              "modr/m.reg is used to access bound registers (added as a part of
              the Intel MPX Programming Environment)."))

   '(mB (:modr/m? . t) (:vex? . nil)
        (:doc .
              "modr/m.r/m is used to access bound registers (added as a part of
              the Intel MPX Programming Environment)."))

   ;; Important: Addressing info with "K-" prefix below does not appear in the
   ;; Intel Manuals (dated May, 2018).  The Intel manuals do not define a Z
   ;; addressing method for AVX512 instructions yet, so until they do, I am
   ;; going to use my own encoding for specifying opmask registers.

   ;; Source: Section 2.6.3 (Opmask Register Encoding), specifically, Table
   ;; 2-33 (Opmask Register Specifier Encoding), Intel Vol. 2

   '(K-reg (:modr/m? . t) (:vex? . nil)
           (:doc .
                 "modr/m.reg is used to access opmask registers k0-k7 (common
                 usages: source). "))

   '(K-vex (:modr/m? . nil) (:vex? . t)
           (:doc .
                 "VEX.vvvv is used to access opmask registers k0-k7 (common
                 usages: 2nd source)."))

   '(K-r/m (:modr/m? . t) (:vex? . nil)
           (:doc .
                 "modr/m.r/m is used to access opmask registers k0-k7 (common
                 usages: 1st source)."))

   '(K-evex (:modr/m? . nil) (:vex? . nil) (:evex? . t)
            (:doc .
                  "EVEX.aaa is used to access opmask registers k0-k4 (common
                  usages: Opmask)."))

   '(L (:modr/m? . nil) (:vex? . t)
       (:doc .
             "The upper 4 bits of the 8-bit immediate selects a 128-bit XMM
             register or a 256-bit YMM register determined by operand
             type. (the MSB is ignored in 32-bit mode)"))

   '(M (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The ModR/M byte may refer only to memory (for example BOUND, LES,
             LDS, LSS, LFS, LGS, CMPXCHG8B)."))

   '(N (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The R/M field of the ModR/M byte selects a packed-quadword MMX
             technology register."))

   '(O (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "The instruction has no ModR/M byte. The offset of the operand is
             coded as a word or double word (depending on address size
             attribute) in the instruction. No base register index register or
             scaling factor can be applied (for example MOV (A0-A3))."))

   '(P (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The reg field of the ModR/M byte selects a packed quadword MMX
             technology register."))

   '(Q (:modr/m? . t) (:vex? . nil)
       (:doc .
             "A ModR/M byte follows the opcode and specifies the operand. The
             operand is either an MMX technology register or a memory
             address. If it is a memory address the address is computed from a
             segment register and any of the following values: a base register,
             an index register, a scaling factor, and a displacement."))

   '(R (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The R/M field of the ModR/M byte may refer only to a general
             register (for example MOV (0F20-0F23))."))

   '(S (:modr/m? . t) (:vex? . nil)
       (:doc .
             "The reg field of the ModR/M byte selects a segment register (for
             example MOV (8C,8E))."))

   '(U (:modr/m? . t) (:vex? . t)
       (:doc .
             "The R/M field of the ModR/M byte selects a 128-bit XMM register
             or a 256-bit YMM register determined by operand type."))

   '(V (:modr/m? . t) (:vex? . t)
       (:doc .
             "The reg field of the ModR/M byte selects a 128-bit XMM register
             or a 256-bit YMM register determined by operand type."))

   '(W (:modr/m? . t) (:vex? . t)
       (:doc .
             "A ModR/M byte follows the opcode and specifies the operand. The
             operand is either a 128-bit XMM register, a 256-bit YMM
             register (determined by operand type), or a memory address. If it
             is a memory address the address is computed from a segment
             register and any of the following values: a base register, an
             index register, a scaling factor,and a displacement."))

   '(X (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "Memory addressed by the DS:rSI register pair (for example MOVS,
             CMPS, OUTS, or LODS)."))

   '(Y (:modr/m? . nil) (:vex? . nil)
       (:doc .
             "Memory addressed by the ES:rDI register pair (for example MOVS,
             CMPS, INS, STOS, or SCAS)."))))

(make-event
 `(defenum addressing-method-code-p
    ,(strip-cars *Z-addressing-method-info*)
    :parents (opcode-maps)
    :short "Codes for Operand Addressing Method; See Intel Vol. 2,
  Appendix A.2.1"))

(defconst *operand-type-code-info*

  ;; See Intel Vol. 2, A.2.2 Codes for Operand Types
  ;; The following abbreviations are used to document operand types:

  (list


   '(a
     (:doc . "Two one-word operands in memory or two double-word operands in
       memory,depending on operand-size attribute (used only by the BOUND
       instruction)."))

   '(b
     (:doc . "Byte, regardless of operand-size attribute."))

   '(c
     (:doc . "Byte or word, depending on operand-size attribute."))

   '(d
     (:doc . "Doubleword, regardless of operand-size attribute."))

   '(dq
     (:doc . "Double-quadword, regardless of operand-size attribute."))

   '(p
     (:doc . "32-bit, 48-bit, or 80-bit pointer, depending on operand-size
       attribute."))

   '(pd
     (:doc . "128-bit or 256-bit packed double-precision floating-point data."))

   '(pi
     (:doc . "Quadword MMX technology register (for example: mm0)."))

   '(ps
     (:doc . "128-bit or 256-bit packed single-precision floating-point data."))

   '(q
     (:doc . "Quadword, regardless of operand-size attribute."))

   '(qq
     (:doc . "Quad-Quadword (256-bits), regardless of operand-size attribute."))

   '(s
     (:doc . "6-byte or 10-byte pseudo-descriptor."))

   '(sd
     (:doc . "Scalar element of a 128-bit double-precision floating data."))

   '(ss
     (:doc . "Scalar element of a 128-bit single-precision floating data."))

   '(si
     (:doc . "Doubleword integer register (for example: eax)."))

   '(v
     (:doc . "Word, doubleword or quadword (in 64-bit mode), depending on
       operand-size attribute."))

   '(w
     (:doc . "Word, regardless of operand-size attribute."))

   '(x
     (:doc . "dq or qq based on the operand-size attribute."))

   '(y
     (:doc . "Doubleword or quadword (in 64-bit mode), depending on
       operand-size attribute."))

   '(z
     (:doc . "Word for 16-bit operand-size or doubleword for 32 or 64-bit
       operand-size."))))

(make-event
 `(defenum operand-type-code-p
    ,(strip-cars *operand-type-code-info*)
    :parents (opcode-maps)
    :short "Codes for Operand Type; See Intel Vol. 2, Appendix A.2.2"))

(defconst *opcode-map-superscripts*

  ;; Source: Intel Manuals, Volume 2, Appendix A.2.5.
  ;; Table A-1. Superscripts Utilized in Opcode Tables.

  (list

   ;; Bits 5, 4, and 3 of ModR/M byte used as an opcode extension
   ;; (refer to Section A.4, Opcode Extensions For One-Byte And
   ;; Two-byte Opcodes)
   :1a

   ;; Use the 0F0B opcode (UD2 instruction) or the 0FB9H opcode when
   ;; deliberately trying to generate an invalid opcode exception
   ;; (#UD).
   :1b

   ;; Some instructions use the same two-byte opcode. If the
   ;; instruction has variations, or the opcode represents different
   ;; instructions, the ModR/M byte will be used to differentiate the
   ;; instruction. For the value of the ModR/M byte needed to decode
   ;; the instruction, see Table A-6.
   :1c

   ;; The instruction is invalid or not encodable in 64-bit mode. 40
   ;; through 4F (single-byte INC and DEC) are REX prefix combinations
   ;; when in 64-bit mode (use FE/FF Grp 4 and 5 for INC and DEC).
   :i64

   ;; Instruction is only available when in 64-bit mode.
   :o64

   ;; When in 64-bit mode, instruction defaults to 64-bit operand size
   ;; and cannot encode 32-bit operand size.
   :d64

   ;; The operand size is forced to a 64-bit operand size when in
   ;; 64-bit mode (prefixes that change operand size are ignored for
   ;; this instruction in 64-bit mode).
   :f64

   ;; VEX form only exists. There is no legacy SSE form of the
   ;; instruction. For Integer GPR instructions it means VEX prefix
   ;; required.
   :v

   ;; VEX128 & SSE forms only exist (no VEX256), when can't be
   ;; inferred from the data size.
   :v1
   ))

(defconst *group-numbers*
  '(:group-1  :group-1a
    :group-2  :group-3
    :group-4  :group-5
    :group-6  :group-7
    :group-8  :group-9
    :group-10 :group-11
    :group-12 :group-13
    :group-14 :group-15
    :group-16 :group-17))

;; ----------------------------------------------------------------------

;; Data structures to represent the opcode maps:

(define op-pfx-p (x)
  (or (not x)
      (member-equal x '(:NO-PREFIX :66 :F3 :F2
                                   :v :v66 :vF3 :vF2
                                   :ev :ev66 :evF3 :evF2)))

  ///

  (define op-pfx-fix ((x op-pfx-p))
    :enabled t
    (mbe :logic (if (op-pfx-p x) x 'nil)
         :exec x))

  (fty::deffixtype op-pfx
    :pred op-pfx-p
    :fix op-pfx-fix
    :equiv op-pfx-equiv
    :define t))

(define op-mode-p (x)
  (or (not x)
      (member-equal x '(:o64 :i64)))

  ///

  (define op-mode-fix ((x op-mode-p))
    :enabled t
    (mbe :logic (if (op-mode-p x) x 'nil)
         :exec x))

  (fty::deffixtype op-mode
    :pred op-mode-p
    :fix op-mode-fix
    :equiv op-mode-equiv
    :define t))

(define rex-p (x)
  (or (not x)
      (member-equal x '(:w :not-w)))
  ///
  (define rex-fix ((x rex-p))
    :enabled t
    (mbe :logic (if (rex-p x) x 'nil)
         :exec x))

  (fty::deffixtype rex
    :pred rex-p
    :fix rex-fix
    :equiv rex-equiv
    :define t))

(define mod-p (x)
  (or (not x)
      (eq x :mem) ;; mod != #b11
      (2bits-p x))
  ///
  (define mod-fix ((x mod-p))
    :enabled t
    (mbe :logic (if (mod-p x) x 'nil)
         :exec x))

  (fty::deffixtype mod
    :pred mod-p
    :fix mod-fix
    :equiv mod-equiv
    :define t))

(define maybe-3bits-p (x)
  (or (not x) (3bits-p x))
  ///
  (define maybe-3bits-fix ((x maybe-3bits-p))
    :enabled t
    (mbe :logic (if (maybe-3bits-p x) x 'nil)
         :exec x))

  (fty::deffixtype maybe-3bits
    :pred maybe-3bits-p
    :fix maybe-3bits-fix
    :equiv maybe-3bits-equiv
    :define t))

;; I could've defined vex and evex using defprod too, but I don't want the
;; order of the vex/evex prefix cases to matter (so the defprod constructor is
;; out).  Nor do I want to use keywords like :vvvv to specify the classes of
;; the prefixes --- this'll reduce the amount of text one has to read/type
;; (thus, the make-* macro is out too).  So the following approach of defining
;; a recognizer for the vex/evex prefix cases serves me well.

(defconst *vvvv-pfx*
  '(:NDS :NDD :DDS ;; UNUSED-VVVV
         ))

(defconst *l-pfx*
  '(:128 :256 :L0 :L1 :LIG :LZ))

(defconst *pp-pfx*
  '(:66 :F2 :F3 ;; NP
        ))

(defconst *mm-pfx*
  '(:0F :0F38 :0F3A))

(defconst *w-pfx*
  '(:W0 :W1 :WIG))

(defconst *vex-pfx-cases*
  ;; See Intel Manual, Vol. 2A, Sec. 3.1.1.2 (Opcode Column in the Instruction
  ;; Summary Table (Instructions with VEX Prefix))
  ;; VEX:
  ;; [NDS|NDD|DDS].[128|256|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
  (append *vvvv-pfx* *l-pfx* *pp-pfx* *mm-pfx* *w-pfx*))

(defconst *evex-pfx-cases*
  ;; See Intel Manual, Vol. 2A, Sec. 3.1.1.2 (Opcode Column in the Instruction
  ;; Summary Table (Instructions with VEX Prefix))
  ;; EVEX:
  ;; [NDS|NDD|DDS].[128|256|512|LIG|LZ].[66|F2|F3].[0F|0F38|0F3A].[W0|W1|WIG]
  (append *vvvv-pfx*
          (cons :512 *l-pfx*)
          *pp-pfx* *mm-pfx* *w-pfx*))

(define count-avx-pfx-cases ((lst true-listp)
                             (alst alistp)
                             (vex? booleanp))
  :prepwork
  ((local
    (defthm alistp-put-assoc-equal
      (implies (alistp alst)
               (alistp (put-assoc-equal k v alst))))))

  :returns (count-alst alistp :hyp (and (alistp alst)
                                        (true-listp lst)))
  (if (endp lst)
      alst
    (b* ((e (car lst))
         ;; No duplicates in lst.
         (rest (cdr lst)))
      (cond ((member e *vvvv-pfx*)
             (b* ((vvvv (nfix (cdr (assoc-equal :vvvv alst))))
                  (alst (put-assoc :vvvv (1+ vvvv) alst)))
               (count-avx-pfx-cases rest alst vex?)))
            ((member e (if vex? *l-pfx* (cons :512 *l-pfx*)))
             (b* ((l (nfix (cdr (assoc-equal :l alst))))
                  (alst (put-assoc :l (1+ l) alst)))
               (count-avx-pfx-cases rest alst vex?)))
            ((member e *pp-pfx*)
             (b* ((pp (nfix (cdr (assoc-equal :pp alst))))
                  (alst (put-assoc :pp (1+ pp) alst)))
               (count-avx-pfx-cases rest alst vex?)))
            ((member e *mm-pfx*)
             (b* ((mm (nfix (cdr (assoc-equal :mm alst))))
                  (alst (put-assoc :mm (1+ mm) alst)))
               (count-avx-pfx-cases rest alst vex?)))
            ((member e *w-pfx*)
             (b* ((w (nfix (cdr (assoc-equal :w alst))))
                  (alst (put-assoc :w (1+ w) alst)))
               (count-avx-pfx-cases rest alst vex?)))))))

(define avx-pfx-well-formed-p ((lst true-listp)
                               (vex? booleanp))
  (b* ((count-alst (count-avx-pfx-cases lst nil vex?))
       (vvvv (if (consp (assoc-equal :vvvv count-alst))
                 (cdr (assoc-equal :vvvv count-alst))
               0))
       ((unless (and (natp vvvv) (<= vvvv 1)))
        (cw "Duplicates encountered in VVVV! Lst: ~p0~%" lst))
       (l    (if (consp (assoc-equal :l count-alst))
                 (cdr (assoc-equal :l count-alst))
               0))
       ((unless (and (natp L) (<= L 1)))
        (cw "Duplicates encountered in L! Lst: ~p0~%" lst))
       (pp   (if (consp (assoc-equal :pp count-alst))
                 (cdr (assoc-equal :pp count-alst))
               0))
       ((unless (and (natp pp) (<= pp 1)))
        (cw "Duplicates encountered in PP! Lst: ~p0~%" lst))
       (mm   (if (consp (assoc-equal :mm count-alst))
                 (cdr (assoc-equal :mm count-alst))
               0))
       ((unless (equal mm 1))
        (cw "MM not equal to 1! Lst: ~p0~%" lst))
       (w    (if (consp (assoc-equal :w count-alst))
                 (cdr (assoc-equal :w count-alst))
               0))
       ((unless (and (natp w) (<= w 1)))
        (cw "Duplicates encountered in W! Lst: ~p0~%" lst)))
    t))

(define vex-p (x)
  (and (true-listp x)
       (subsetp-equal x *vex-pfx-cases*)
       (no-duplicatesp-equal x)
       (avx-pfx-well-formed-p x t)))

(define maybe-vex-p (x)
  (or (not x) (vex-p x))
  ///
  (define maybe-vex-fix ((x maybe-vex-p))
    :enabled t
    (mbe :logic (if (maybe-vex-p x) x 'nil)
         :exec x))

  (fty::deffixtype maybe-vex
    :pred maybe-vex-p
    :fix maybe-vex-fix
    :equiv maybe-vex-equiv
    :define t))

(define evex-p (x)
  (and (true-listp x)
       (subsetp-equal x *evex-pfx-cases*)
       (no-duplicatesp-equal x)
       (avx-pfx-well-formed-p x nil)))

(define maybe-evex-p (x)
  (or (not x) (evex-p x))
  ///
  (define maybe-evex-fix ((x maybe-evex-p))
    :enabled t
    (mbe :logic (if (maybe-evex-p x) x 'nil)
         :exec x))

  (fty::deffixtype maybe-evex
    :pred maybe-evex-p
    :fix maybe-evex-fix
    :equiv maybe-evex-equiv
    :define t))

(define superscripts-p (x)
  (or (not x)
      (and (acl2::keyword-listp x)
           (subsetp-equal x *opcode-map-superscripts*)))
  ///
  (define superscripts-fix ((x superscripts-p))
    :enabled t
    (mbe :logic (if (superscripts-p x) x 'nil)
         :exec x))

  (fty::deffixtype superscripts
    :pred superscripts-p
    :fix superscripts-fix
    :equiv superscripts-equiv
    :define t))

(define opcode-extension-group-p (x)
  (or (not x)
      (and (acl2::keyword-listp x)
           (subsetp-equal x *group-numbers*)))
  ///
  (define opcode-extension-group-fix ((x opcode-extension-group-p))
    :enabled t
    (mbe :logic (if (opcode-extension-group-p x) x 'nil)
         :exec x))

  (fty::deffixtype opcode-extension-group
    :pred opcode-extension-group-p
    :fix opcode-extension-group-fix
    :equiv opcode-extension-group-equiv
    :define t))

(defprod opcode
  ((op            24bits-p
                  "Includes escape bytes of two- and three-byte opcodes as
                  well"
                  :default '0)
   (mode          op-mode-p
                  :default 'nil)
   (reg           maybe-3bits-p
                  "ModR/M.reg descriptor"
                  :default 'nil)
   (mod           mod-p
                  "ModR/M.mod descriptor"
                  :default 'nil)
   (r/m           maybe-3bits-p
                  "ModR/M.r/m descriptor"
                  :default 'nil)
   (pfx           op-pfx-p
                  :default 'nil)
   (rex           rex-p "REX descriptor"
                  :default 'nil)
   (vex           maybe-vex-p
                  :default 'nil)
   (evex          maybe-evex-p
                  :default 'nil)
   (feat          symbol-listp
                  :default 'nil)
   (superscripts  superscripts-p
                  :default 'nil)
   (group         opcode-extension-group-p
                  :default 'nil))
  :layout :tree)

(defmacro op (&rest args)
  `(make-opcode ,@args))

(define keyword-list-fix ((x acl2::keyword-listp))
  :enabled t
  (mbe :logic (if (acl2::keyword-listp x) x 'nil)
       :exec x))

(fty::deffixtype keyword-list
  :pred acl2::keyword-listp
  :fix keyword-list-fix
  :equiv keyword-list-equiv
  :define t)

(defprod Op/En-p
  ((src1 acl2::keyword-listp)
   (src2 acl2::keyword-listp)
   (src3 acl2::keyword-listp)
   (src4 acl2::keyword-listp)))

(define operand-type-p (x)
  (or (not x)
      ;; The opcode maps present in Intel's manuals are incomplete.  Notably,
      ;; the EVEX-encoded instructions are absent from it.  In such cases, we
      ;; can describe the operands using the Op/En column present in the
      ;; instruction description pages --- this info. can be put in a keyword
      ;; list. E.g.:
      ;; EVEX.LIG.F2.0F.W1 10 /r VMOVSD xmm1 {k1}{z}, xmm2, xmm3
      ;; Operand 1: ModRM:reg (w)
      ;; Operand 2: VEX.vvvv (r)
      ;; Operand 3: ModRM:r/m (r)
      ;; We can describe these operands as follows (respectively):
      ;; '(:ModRM.reg :XMM)
      ;; '(:VEX.vvvv  :XMM)
      ;; '(:ModRM.r/m :XMM)
      ;; Suppose YMM registers were also allowed.  Then one could say the
      ;; following:
      ;; '(:ModRM.reg :XMM :YMM)
      (acl2::keyword-listp x)
      (and (true-listp x)
           (if (equal (len x) 1)
               (or (acl2-numberp (nth 0 x))
                   (addressing-method-code-p (nth 0 x)))
             (if (equal (len x) 2)
                 (and
                  (addressing-method-code-p (nth 0 x))
                  (operand-type-code-p (nth 1 x)))
               nil))))
  ///
  (define operand-type-fix ((x operand-type-p))
    :enabled t
    (mbe :logic (if (operand-type-p x) x 'nil)
         :exec x))

  (fty::deffixtype operand-type
    :pred operand-type-p
    :fix operand-type-fix
    :equiv operand-type-equiv
    :define t))

(defprod operands
  ((op1 operand-type-p :default 'nil)
   (op2 operand-type-p :default 'nil)
   (op3 operand-type-p :default 'nil)
   (op4 operand-type-p :default 'nil))
  :layout :tree)

(defmacro arg (&rest args)
  `(make-operands ,@args))

(define maybe-operands-p (x)
  (or (not x) (operands-p x))
  ///
  (define maybe-operands-fix ((x maybe-operands-p))
    :enabled t
    (mbe :logic (if (maybe-operands-p x) x 'nil)
         :exec x))

  (fty::deffixtype maybe-operands
    :pred maybe-operands-p
    :fix maybe-operands-fix
    :equiv maybe-operands-equiv
    :define t))

(define exception-desc-p (x)
  (and (alistp x)
       (subsetp-equal (strip-cars x)
                      '(:ex :ud :gp :nm)))

  ///

  (define exception-desc-fix ((x exception-desc-p))
    :enabled t
    (mbe :logic (if (exception-desc-p x) x 'nil)
         :exec x))

  (fty::deffixtype exception-desc
    :pred exception-desc-p
    :fix exception-desc-fix
    :equiv exception-desc-equiv
    :define t))

(define fn-desc-p (x)
  (or (null x)
      (and (true-listp x)
           (symbolp (car x))
           (eqlable-alistp (cdr x))))

  ///

  (define fn-desc-fix ((x fn-desc-p))
    :enabled t
    (mbe :logic (if (fn-desc-p x) x 'nil)
         :exec x))

  (fty::deffixtype fn-desc
    :pred fn-desc-p
    :fix fn-desc-fix
    :equiv fn-desc-equiv
    :define t))

(define mnemonic-p (x)
  (or (stringp x)
      (keywordp x))
  ///

  (define mnemonic-fix ((x mnemonic-p))
    :enabled t
    (mbe :logic (if (mnemonic-p x) x ':NONE)
         :exec x))

  (defthm mnemonic-p-of-mnemonic-fix
    (mnemonic-p (mnemonic-fix x)))

  (fty::deffixtype mnemonic
    :pred mnemonic-p
    :fix mnemonic-fix
    :equiv mnemonic-equiv
    :define t))

(define any-present-in ((xs true-listp)
                        (ys true-listp))
  :short "Is any element of @('xs') present in @('ys')?"
  (if (endp xs)
      nil
    (if (member-equal (car xs) ys)
        t
      (any-present-in (cdr xs) ys))))

(define strict-opcode-p (x)
  (and (opcode-p x)
       (b* (((opcode x))
            ((when (and
                    (any-present-in
                     (append (list :avx :avx2 :bmi1 :bmi2)
                             *avx512-feature-flags*)
                     x.feat)
                    (null x.vex)
                    (null x.evex)))
             nil))
         t))
  ///
  (define strict-opcode-fix ((x strict-opcode-p))
    :enabled t
    (if (strict-opcode-p x)
        x
      ;; Wiping out :feat --- doesn't really matter what I put here.
      (b* ((x (opcode-fix x))
           (x (change-opcode x :feat nil)))
        x)))

  (defthm strict-opcode-p-of-strict-opcode-fix
    (strict-opcode-p (strict-opcode-fix x)))

  (fty::deffixtype strict-opcode
    :pred strict-opcode-p
    :fix strict-opcode-fix
    :equiv strict-opcode-equiv
    :define t))

(defprod inst
  ((mnemonic     mnemonic-p)
   (opcode       strict-opcode-p
                 "Opcode descriptor.")
   (operands     maybe-operands-p
                 "Description of operands; can be left empty if there are zero
                  operands."
                 :default 'nil)
   (fn           fn-desc-p
                 "Partial call of the semantic function that implements this
                  opcode."
                 :default 'nil)
   (excep        exception-desc-p
                 "Conditions for detecting certain decode-time exceptions; can
                  be left empty if there are no conditions to detect."
                 :default 'nil))
  :layout :tree)

(define inst-list-p (xs)
  :enabled t
  (if (atom xs)
      (equal xs nil)
    (and (or (inst-p (car xs))
             (cw "~% inst-list-p: problem in: ~p0~% Appears before: ~p1~%"
                 (car xs) (if (consp (cdr xs)) (cdr xs) nil)))
         (inst-list-p (cdr xs)))))

;; ----------------------------------------------------------------------

;; Some useful lemmas:

(local
 (defthm operands-p-when-maybe-operands-p
   (implies (and (maybe-operands-p x) x)
            (operands-p x))
   :hints (("Goal" :in-theory (e/d (maybe-operands-p) ())))))

(defthm operands-p-of-inst->operands
  (implies (and (inst-p x)
                (inst->operands x))
           (operands-p (inst->operands x)))
  :hints (("Goal" :in-theory (e/d (maybe-operands-p inst-p) ()))))

(defthm operand-type-p-implies-true-listp
  (implies (operand-type-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (operand-type-p) ())))
  :rule-classes :forward-chaining)

(defthm inst-p-implies-operand-type-p-op1
  (implies
   (inst-p inst)
   (operand-type-p (operands->op1 (inst->operands inst))))
  :hints (("Goal" :in-theory (e/d (inst-p operands-p) ())))
  :rule-classes :forward-chaining)

(defthm inst-p-implies-operand-type-p-op2
  (implies
   (inst-p inst)
   (operand-type-p (operands->op2 (inst->operands inst))))
  :hints (("Goal" :in-theory (e/d (inst-p operands-p) ())))
  :rule-classes :forward-chaining)

(defthm inst-p-implies-operand-type-p-op3
  (implies
   (inst-p inst)
   (operand-type-p (operands->op3 (inst->operands inst))))
  :hints (("Goal" :in-theory (e/d (inst-p operands-p) ())))
  :rule-classes :forward-chaining)

(defthm inst-p-implies-operand-type-p-op4
  (implies
   (inst-p inst)
   (operand-type-p (operands->op4 (inst->operands inst))))
  :hints (("Goal" :in-theory (e/d (inst-p operands-p) ())))
  :rule-classes :forward-chaining)

(defthm strict-opcode-p-implies-opcode-p
  (implies (strict-opcode-p x)
           (opcode-p x))
  :hints (("Goal" :in-theory (e/d (strict-opcode-p) ()))))

(defthm inst-p-implies-opcode-p
  (implies (inst-p x)
           (opcode-p (inst->opcode x)))
  :hints (("Goal" :in-theory (e/d (inst-p) ()))))

(defthm superscripts-p-implies-true-listp
  (implies (superscripts-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (superscripts-p) ())))
  :rule-classes :forward-chaining)

(defthm vex-p-implies-true-listp
  (implies (vex-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (vex-p) ())))
  :rule-classes :forward-chaining)

(defthm evex-p-implies-true-listp
  (implies (evex-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (evex-p) ())))
  :rule-classes :forward-chaining)

(defthm maybe-vex-p-implies-true-listp
  (implies (maybe-vex-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (maybe-vex-p) ())))
  :rule-classes :forward-chaining)

(defthm maybe-evex-p-implies-true-listp
  (implies (maybe-evex-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (e/d (maybe-evex-p) ())))
  :rule-classes :forward-chaining)

(local
 (defthm subsetp-equal-and-keyword-listp
   (implies (and (subsetp-equal x y)
                 (acl2::keyword-listp y)
                 (true-listp x))
            (acl2::keyword-listp x))
   :hints (("Goal" :in-theory (e/d (subsetp-equal
                                    acl2::keyword-listp)
                                   ())))))

(defthm maybe-vex-p-implies-keyword-listp
  (implies (maybe-vex-p x)
           (acl2::keyword-listp x))
  :hints (("Goal" :in-theory (e/d (maybe-vex-p vex-p) ())))
  :rule-classes :forward-chaining)

(defthm maybe-evex-p-implies-keyword-listp
  (implies (maybe-evex-p x)
           (acl2::keyword-listp x))
  :hints (("Goal" :in-theory (e/d (maybe-evex-p evex-p) ())))
  :rule-classes :forward-chaining)

;; ----------------------------------------------------------------------

(defsection filtering-instructions
  :parents (opcode-maps)
  :short "Some Functions to operate on the ACL2 representation of Intel's Opcode
  Maps"
  )

(local (xdoc::set-default-parents 'filtering-instructions))

;; Right now, we can't select AVX instructions using the function
;; select-insts. The reason is that VEX/EVEX-encoded instructions (but probably
;; just EVEX-encoded --- I'm being extra cautious here) may be missing
;; operands' information (i.e., their :vex or :evex fields may be empty)
;; because Intel manuals are missing that information.  So selecting an
;; instruction based on the presence or absence of the :vex or :evex fields
;; would result in false matches.  However, all AVX instructions (I believe)
;; have proper CPUID feature flags.  Thus, for now, we can do selection of AVX
;; instructions using the functions remove-insts-with-feat and
;; keep-insts-with-feat below.

;; I've tried to store all CPUID feature flag information in the :feat field of
;; the opcode, but there are a few cases where that information is in the
;; :excep field of inst instead (just three at this count: SAHF, LAHF, and
;; XSAVEOPT).  The reason they're separate is that in these cases, the absence
;; of one feature flag by itself is not enough to cause a #UD --- either we
;; need at least one flag to be present (and the dispatch functions check
;; whether ALL the flags are present in :FEAT) or the #UD also depends on the
;; mode of operation of the processor. Search for FEATURE-FLAG-MACRO in the
;; inst-listings to see those cases.

(define remove-insts-with-feat ((inst-lst inst-list-p)
                                (feat acl2::keyword-listp))
  :short "Remove all instructions from @('inst-lst') that have ANY feature
  present in @('feat')"
  ;; TODO: Replace with select-insts, with :vex and :evex set to t and :get/rem
  ;; set to :rem once we have operands' spec. for EVEX instructions.
  :returns (new-inst-lst inst-list-p
                         :hyp (inst-list-p inst-lst))
  (if (endp inst-lst)
      nil
    (b* ((inst (car inst-lst))
         (rest (remove-insts-with-feat (cdr inst-lst) feat))
         ((inst inst))
         (opcode inst.opcode)
         ((opcode opcode))
         ((when (any-present-in feat opcode.feat)) rest))
      (cons inst rest))))

(define keep-insts-with-feat ((inst-lst inst-list-p)
                              (feat acl2::keyword-listp))
  :short "Keep all instructions from @('inst-lst') that have ANY feature
  present in @('feat')"
  ;; TODO: Replace with select-insts, with :vex and :evex set to t and :get/rem
  ;; set to :get once we have operands' spec. for EVEX instructions.
  :returns (new-inst-lst inst-list-p
                         :hyp (inst-list-p inst-lst))

  (if (endp inst-lst)
      nil
    (b* ((inst (car inst-lst))
         (rest (keep-insts-with-feat (cdr inst-lst) feat))
         ((inst inst))
         (opcode inst.opcode)
         ((opcode opcode))
         ((when (any-present-in feat opcode.feat)) (cons inst rest)))
      rest)))

(define select-insts ((inst-lst inst-list-p)
                      &key
                      ((get/rem (member-equal get/rem '(:get :rem))
                                "Either get or remove the selected instructions")
                       ':get)
                      ((opcode (or (eql opcode nil) (24bits-p opcode))
                               "If specified, select all instructions with the
                                same opcode")
                       'nil)
                      ((mode op-mode-p
                             "If specified, select all instructions with the
                                same mode of operation")
                       'nil)
                      ((prefix op-pfx-p
                               "If specified, select all instructions with the
                                same prefix")
                       'nil)
                      ((vex? booleanp
                             "If @('t'), select all instructions with a non-nil
                             @('opcode.vex') field")
                       'nil)
                      ((fn? booleanp
                            "If @('t'), select all instructions with a non-nil
                             @('inst.fn') field")
                       'nil))

  :short "Select instructions satisfying some conditions, and then either
  remove the selection or keep only the selection"

  :returns (new-inst-lst inst-list-p
                         :hyp (inst-list-p inst-lst))

  (b* (((when (endp inst-lst)) nil)
       (rest (select-insts (cdr inst-lst)
                           ;; Remember to add key/vals here too if you expand
                           ;; the formals!
                           :get/rem get/rem
                           :opcode opcode
                           :mode mode
                           :prefix prefix
                           :vex? vex?
                           :fn? fn?))
       (inst (car inst-lst))
       ((inst inst))
       ((opcode inst.opcode))
       (match? (and (if (not opcode)
                        t
                      (equal opcode inst.opcode.op))
                    (if (not mode)
                        t
                      (equal mode inst.opcode.mode))
                    (if (not prefix)
                        t
                      (if (equal prefix :no-prefix)
                          (or (equal prefix inst.opcode.pfx)
                              (not inst.opcode.pfx))
                        (equal prefix inst.opcode.pfx)))
                    (if (not vex?)
                        t
                      (if inst.opcode.vex t nil))
                    (if (not fn?)
                        t
                      (if inst.fn t nil)))))
    (if (eql get/rem :get)
        (append (and match? (list inst)) rest)
      (append (if match? nil (list inst)) rest))))

;; ----------------------------------------------------------------------