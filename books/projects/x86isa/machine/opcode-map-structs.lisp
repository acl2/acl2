; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Copyright (C) 2018, Centaur Technology, Inc.
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
; Shilpi Goel         <shilpi@centtech.com>
; Contributing Author(s):
; Rob Sumners         <rsumners@centtech.com>

(in-package "X86ISA")
(include-book "../utils/basic-structs")
(include-book "std/util/defenum" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/lists/duplicity" :dir :system)
(include-book "std/strings/hexify" :dir :system)

; Lisp representation of Intel's opcode maps (See Intel Manuals,
; Vol. 2, Appendix A)

(defsection opcode-maps
  :parents (instructions x86-decoder)
  :short "ACL2 representation of Intel's x86 Opcode Maps"
  )

(local (xdoc::set-default-parents 'opcode-maps))

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

   ;; A Direct address: the instruction has no ModR/M byte; the
   ;; address of the operand is encoded in the instruction. No base
   ;; register, index register, or scaling factor can be applied (for
   ;; example far JMP (EA)).

   '(A (:modr/m? . nil))

   ;; B The VEX.vvvv field of the VEX prefix selects a general purpose
   ;; register.

   '(B (:modr/m? . nil))

   ;; C The reg field of the ModR/M byte selects a control register
   ;; (for example MOV (0F20, 0F22)).

   '(C (:modr/m? . t))

   ;; D The reg field of the ModR/M byte selects a debug register (for
   ;; example MOV (0F21,0F23)).

   '(D (:modr/m? . t))

   ;; E A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a general-purpose register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register, an index register, a scaling factor, a
   ;; displacement.

   '(E (:modr/m? . t))

   ;; F EFLAGS/RFLAGS Register.

   '(F (:modr/m? . nil))

   ;; G The reg field of the ModR/M byte selects a general register
   ;; (for example AX (000)).

   '(G (:modr/m? . t))

   ;; H The VEX.vvvv field of the VEX prefix selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. For legacy SSE encodings this operand does not exist,
   ;; changing the instruction to destructive form.

   '(H (:modr/m? . nil))

   ;; I Immediate data: the operand value is encoded in subsequent
   ;; bytes of the instruction.

   '(I (:modr/m? . nil))

   ;; J The instruction contains a relative offset to be added to the
   ;; instruction pointer register (for example JMP (0E9), LOOP).

   '(J (:modr/m? . nil))

   ;; Important: Note that rB, mB are not listed as Z addressing methods in the
   ;; Intel manuals (May 2018 edition).  I borrowed them from the following:
   ;; http://sandpile.org/x86/opc_enc.htm.

   ;; rB: modr/m.reg is used to access bound registers (added as a part of the
   ;; Intel MPX Programming Environment).

   '(rB (:modr/m? . t))

   ;; mB: modr/m.r/m is used to access bound registers (added as a part of the
   ;; Intel MPX Programming Environment).

   '(mB (:modr/m? . t))

   ;; Important: Addressing info with "K-" prefix below does not appear in the
   ;; Intel Manuals (dated May, 2018).  The Intel manuals do not define a Z
   ;; addressing method for AVX512 instructions yet, so until they do, I am
   ;; going to use my own encoding for specifying opmask registers.

   ;; Source: Section 2.6.3 (Opmask Register Encoding), specifically, Table
   ;; 2-33 (Opmask Register Specifier Encoding), Intel Vol. 2

   ;; K-reg: modr/m.reg is used to access opmask registers k0-k7 (common
   ;; usages: source).

   '(K-reg (:modr/m? . t))

   ;; K-vex: VEX.vvvv is used to access opmask registers k0-k7 (common usages:
   ;; 2nd source).

   '(K-vex (:modr/m? . nil) (:vex? . t))

   ;; K-r/m: modr/m.r/m is used to access opmask registers k0-k7 (common
   ;; usages: 1st source).

   '(K-r/m (:modr/m? . t))

   ;; K-evex: EVEX.aaa is used to access opmask registers k0-k4 (common usages:
   ;; Opmask).

   '(K-evex (:modr/m? . nil) (:vex? . nil) (:evex? . t))

   ;; L The upper 4 bits of the 8-bit immediate selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand
   ;; type. (the MSB is ignored in 32-bit mode)

   '(L (:modr/m? . nil))

   ;; M The ModR/M byte may refer only to memory (for example BOUND,
   ;; LES, LDS, LSS, LFS, LGS, CMPXCHG8B).

   '(M (:modr/m? . t))

   ;; N The R/M field of the ModR/M byte selects a packed-quadword MMX
   ;; technology register.

   '(N (:modr/m? . t))

   ;; O The instruction has no ModR/M byte. The offset of the operand
   ;; is coded as a word or double word (depending on address size
   ;; attribute) in the instruction. No base register index register
   ;; or scaling factor can be applied (for example MOV (A0-A3)).

   '(O (:modr/m? . nil) (:vex? . nil))

   ;; P The reg field of the ModR/M byte selects a packed quadword MMX
   ;; technology register.

   '(P (:modr/m? . t))

   ;; Q A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either an MMX technology register or a
   ;; memory address. If it is a memory address the address is
   ;; computed from a segment register and any of the following
   ;; values: a base register, an index register, a scaling factor, and a
   ;; displacement.

   '(Q (:modr/m? . t))

   ;; R The R/M field of the ModR/M byte may refer only to a general
   ;; register (for example MOV (0F20-0F23)).

   '(R (:modr/m? . t))

   ;; S The reg field of the ModR/M byte selects a segment register
   ;; (for example MOV (8C,8E)).

   '(S (:modr/m? . t))

   ;; U The R/M field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(U (:modr/m? . t))

   ;; V The reg field of the ModR/M byte selects a 128-bit XMM
   ;; register or a 256-bit YMM register determined by operand type.

   '(V (:modr/m? . t))

   ;; W A ModR/M byte follows the opcode and specifies the
   ;; operand. The operand is either a 128-bit XMM register, a 256-bit
   ;; YMM register (determined by operand type), or a memory
   ;; address. If it is a memory address the address is computed from
   ;; a segment register and any of the following values: a base
   ;; register, an index register, a scaling factor, and a displacement.

   '(W (:modr/m? . t))

   ;; X Memory addressed by the DS:rSI register pair (for example MOVS,
   ;; CMPS, OUTS, or LODS).

   '(X (:modr/m? . nil))

   ;; Y Memory addressed by the ES:rDI register pair (for example MOVS,
   ;; CMPS, INS, STOS, or SCAS).

   '(Y (:modr/m? . nil))

   ))

(make-event
 `(defenum addressing-method-code-p
    ,(strip-cars *Z-addressing-method-info*)
    :parents (opcode-maps)
    :short "Codes for Operand Addressing Method; See Intel Vol. 2,
  Appendix A.2.1"))

(defenum operand-type-code-p
  (
   ;; A.2.2 Codes for Operand Type

   ;; The following abbreviations are used to document operand types:

   a ;; Two one-word operands in memory or two double-word operands in
   ;; memory, depending on operand-size attribute (used only by the BOUND
   ;; instruction).

   b ;; Byte, regardless of operand-size attribute.

   c ;; Byte or word, depending on operand-size attribute.

   d ;; Doubleword, regardless of operand-size attribute.

   dq ;; Double-quadword, regardless of operand-size attribute.

   p ;; 32-bit, 48-bit, or 80-bit pointer, depending on operand-size
   ;; attribute.

   pd ;; 128-bit or 256-bit packed double-precision floating-point data.

   pi ;; Quadword MMX technology register (for example: mm0).

   ps ;; 128-bit or 256-bit packed single-precision floating-point data.

   q ;; Quadword, regardless of operand-size attribute.

   qq ;; Quad-Quadword (256-bits), regardless of operand-size attribute.

   s ;; 6-byte or 10-byte pseudo-descriptor.

   sd ;; Scalar element of a 128-bit double-precision floating data.

   ss ;; Scalar element of a 128-bit single-precision floating data.

   si ;; Doubleword integer register (for example: eax).

   v ;; Word, doubleword or quadword (in 64-bit mode), depending on
   ;; operand-size attribute.

   w ;; Word, regardless of operand-size attribute.

   x ;; dq or qq based on the operand-size attribute.

   y ;; Doubleword or quadword (in 64-bit mode), depending on operand-size
   ;; attribute.

   z ;; Word for 16-bit operand-size or doubleword for 32 or 64-bit
   ;; operand-size.
   )
  :parents (opcode-maps)
  :short "Codes for Operand Type; See Intel Vol. 2, Appendix A.2.2")

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
      (eq x :mem)
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

(define esc-p (x)
  (or (not x)
      (and (16bits-p x)
           (or (equal x #ux0F)
               (equal x #ux0F_38)
               (equal x #ux0F_3A))))
  ///
  (define esc-fix ((x esc-p))
    :enabled t
    (mbe :logic (if (esc-p x) x 'nil)
         :exec x))

  (fty::deffixtype esc
    :pred esc-p
    :fix esc-fix
    :equiv esc-equiv
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

(defprod opcode
  ((op            24bits-p)
   (esc           esc-p
                  :default 'nil)
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
   (superscripts  symbol-listp
                  :default 'nil))
  :layout :tree)

(defmacro op (&rest args)
  `(make-opcode ,@args))

(define operand-type-p (x)
  (or (not x)
      (and (true-listp x)
           (if (equal (len x) 1)
               (or (keywordp (nth 0 x))
                   (acl2-numberp (nth 0 x))
                   (addressing-method-code-p (nth 0 x)))
             (if (equal (len x) 2)
                 (operand-type-code-p (nth 1 x))
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

(defprod inst
  ((mnemonic     mnemonic-p)
   (opcode       opcode-p
                 "Opcode descriptor.")
   (operands     maybe-operands-p
                 "Description of operands; can be left empty if there are zero
                  operands."
                 :default 'nil)
   (fn           true-listp
                 "Partial call of the semantic function that implements this
                  opcode."
                 :default 'nil)
   (excep        exception-desc-p
                 "Conditions for detecting certain decode-time exceptions; can
                  be left empty if there are no conditions to detect."
                 :default 'nil))
  :layout :tree)

(define inst-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (or (inst-p (car xs))
             (cw "~% inst-list-p: problem in: ~p0~% Appears before: ~p1~%"
                 (car xs) (if (consp (cdr xs)) (cdr xs) nil)))
         (inst-list-p (cdr xs)))))

;; ----------------------------------------------------------------------

;; ;; From the one-byte opcode map:
;; (inst "ADD" (op :op #x00) (arg :op1 '(E b) :op2 '(G b))
;;       '(x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
;;         (operation . #.*OP-ADD*))
;;       '((:ud . ((ud-Lock-used-Dest-not-Memory-Op)))))

;; ;; From Opcode Extensions:
;; (inst "CLAC"
;;       (op :esc #x0F :op #x01 :mod #b11 :reg #b001 :r/m #b010 :feat '(:smap))
;;       'nil
;;       'nil
;;       '((:ud  . ((ud-Lock-used)
;;                  (ud-cpl-is-not-zero)))))

;; ;; A Vex Opcode:
;; (inst "VPSHUFB"
;;       (op :op #x00 :vex '(:NDS :0F38 :128 :66 :WIG) :feat '(:avx))
;;       (arg :op1 '(V x) :op2 '(H x) :op3 '(W x))
;;       'nil
;;       '((:ud  . ((ud-Lock-used)
;;                  (ud-cpl-is-not-zero)
;;                  (equal (feature-flags-macro '(:avx)) 0)))))

;; (b* ((vshufb-desc
;;       (inst "VPSHUFB"
;;             (op :op #x00 :vex '(:NDS :0F38 :128 :66 :WIG) :feat '(:avx))
;;             (arg :op1 '(V x) :op2 '(H x) :op3 '(W x))
;;             'nil
;;             '(:ud  . ((ud-Lock-used)
;;                       (ud-cpl-is-not-zero)
;;                       (equal (feature-flags-macro '(:avx)) 0)))))
;;      ((inst vshufb-desc))
;;      ((opcode vshufb-desc.opcode))
;;      ((operands vshufb-desc.operands)))
;;   (list vshufb-desc.mnemonic
;;         vshufb-desc.operands.op1
;;         vshufb-desc.opcode.feat))

;; ----------------------------------------------------------------------