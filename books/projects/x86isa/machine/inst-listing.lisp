; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Shilpi Goel
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

(include-book "inst-structs")
(include-book "std/strings/pretty" :dir :system)

(defsection opcode-maps
  :parents (instructions x86-decoder)
  :short "ACL2 representation of x86 Opcode Maps (see Intel Manuals, Vol. 2,
 Appendix A)"
  )

(local (xdoc::set-default-parents 'opcode-maps))

;; ----------------------------------------------------------------------

(defconst *pre-one-byte-opcode-map*
  '((INST "ADD" (OP :OP #x0)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADD" (OP :OP #x1)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADD" (OP :OP #x2)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x0))
          '((:UD (UD-LOCK-USED))))
    (INST "ADD" (OP :OP #x3)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x0))
          '((:UD (UD-LOCK-USED))))
    (INST "ADD" (OP :OP #x4)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED))))
    (INST "ADD" (OP :OP #x5)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH ES" (OP :OP #x6 :MODE :I64)
          NIL '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x6 :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "PUSH ES is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "POP ES" (OP :OP #x7 :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x7 :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "POP ES is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "OR" (OP :OP #x8)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR" (OP :OP #x9)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR" (OP :OP #xA)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x1))
          '((:UD (UD-LOCK-USED))))
    (INST "OR" (OP :OP #xB)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x1))
          '((:UD (UD-LOCK-USED))))
    (INST "OR" (OP :OP #xC)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED))))
    (INST "OR" (OP :OP #xD)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH CS" (OP :OP #xE :MODE :I64)
          NIL '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #xE :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "PUSH CS is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST :2-BYTE-ESCAPE (OP :OP #xF)
          'NIL
          '(TWO-BYTE-OPCODE-DECODE-AND-EXECUTE (ESCAPE-BYTE . OPCODE))
          'NIL)
    (INST "ADC" (OP :OP #x10)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC" (OP :OP #x11)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC" (OP :OP #x12)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC" (OP :OP #x13)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x2))
          '((:UD (UD-LOCK-USED))))
    (INST "ADC" (OP :OP #x14)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED))))
    (INST "ADC" (OP :OP #x15)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH SS" (OP :OP #x16 :MODE :I64)
          NIL '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x16 :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "PUSH SS is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "POP SS" (OP :OP #x17 :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x17 :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "POP SS is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "SBB" (OP :OP #x18)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB" (OP :OP #x19)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB" (OP :OP #x1A)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x6))
          '((:UD (UD-LOCK-USED))))
    (INST "SBB" (OP :OP #x1B)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x6))
          '((:UD (UD-LOCK-USED))))
    (INST "SBB" (OP :OP #x1C)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED))))
    (INST "SBB" (OP :OP #x1D)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH DS" (OP :OP #x1E :MODE :I64)
          NIL '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x1E :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "PUSH DS is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "POP DS" (OP :OP #x1F :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x1F :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "POP DS is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "AND" (OP :OP #x20)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND" (OP :OP #x21)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND" (OP :OP #x22)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x3))
          '((:UD (UD-LOCK-USED))))
    (INST "AND" (OP :OP #x23)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x3))
          '((:UD (UD-LOCK-USED))))
    (INST "AND" (OP :OP #x24)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED))))
    (INST "AND" (OP :OP #x25)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-ES (OP :OP #x26)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DAA" (OP :OP #x27 :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x27 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "DAA is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "SUB" (OP :OP #x28)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB" (OP :OP #x29)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB" (OP :OP #x2A)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x4))
          '((:UD (UD-LOCK-USED))))
    (INST "SUB" (OP :OP #x2B)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x4))
          '((:UD (UD-LOCK-USED))))
    (INST "SUB" (OP :OP #x2C)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED))))
    (INST "SUB" (OP :OP #x2D)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-CS (OP :OP #x2E)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DAS" (OP :OP #x2F :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x2F :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "DAS is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "XOR" (OP :OP #x30)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR" (OP :OP #x31)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR" (OP :OP #x32)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x5))
          '((:UD (UD-LOCK-USED))))
    (INST "XOR" (OP :OP #x33)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x5))
          '((:UD (UD-LOCK-USED))))
    (INST "XOR" (OP :OP #x34)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED))))
    (INST "XOR" (OP :OP #x35)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-SS (OP :OP #x36)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "AAA" (OP :OP #x37 :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x37 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "AAA is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "CMP" (OP :OP #x38)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "CMP" (OP :OP #x39)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "CMP" (OP :OP #x3A)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "CMP" (OP :OP #x3B)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "CMP" (OP :OP #x3C)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "CMP" (OP :OP #x3D)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-DS (OP :OP #x3E)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "AAS" (OP :OP #x3F :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x3F :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "AAS is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST :REX (OP :OP #x40 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x40 :MODE :I64)
          (ARG :OP1 '(:EAX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-B (OP :OP #x41 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x41 :MODE :I64)
          (ARG :OP1 '(:ECX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-X (OP :OP #x42 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x42 :MODE :I64)
          (ARG :OP1 '(:EDX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-XB (OP :OP #x43 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x43 :MODE :I64)
          (ARG :OP1 '(:EBX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-R (OP :OP #x44 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x44 :MODE :I64)
          (ARG :OP1 '(:ESP))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-RB (OP :OP #x45 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x45 :MODE :I64)
          (ARG :OP1 '(:EBP))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-RX (OP :OP #x46 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x46 :MODE :I64)
          (ARG :OP1 '(:ESI))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-RXB (OP :OP #x47 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INC" (OP :OP #x47 :MODE :I64)
          (ARG :OP1 '(:EDI))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-W (OP :OP #x48 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x48 :MODE :I64)
          (ARG :OP1 '(:EAX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WB (OP :OP #x49 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x49 :MODE :I64)
          (ARG :OP1 '(:ECX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WX (OP :OP #x4A :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4A :MODE :I64)
          (ARG :OP1 '(:EDX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WXB (OP :OP #x4B :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4B :MODE :I64)
          (ARG :OP1 '(:EBX))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WR (OP :OP #x4C :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4C :MODE :I64)
          (ARG :OP1 '(:ESP))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WRB (OP :OP #x4D :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4D :MODE :I64)
          (ARG :OP1 '(:EBP))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WRX (OP :OP #x4E :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4E :MODE :I64)
          (ARG :OP1 '(:ESI))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST :REX-WRXB (OP :OP #x4F :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "DEC" (OP :OP #x4F :MODE :I64)
          (ARG :OP1 '(:EDI))
          '(X86-INC/DEC-4X)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x50 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RAX/R8))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x51 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RCX/R9))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x52 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RDX/R10))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x53 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RBX/R11))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x54 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RSP/R11))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x55 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RBP/R13))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x56 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RSI/R14))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x57 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RDI/R15))
          '(X86-PUSH-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x58 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RAX/R8))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x59 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RCX/R9))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5A :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RDX/R10))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5B :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RBX/R11))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5C :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RSP/R11))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5D :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RBP/R13))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5E :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RSI/R14))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x5F :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:RDI/R15))
          '(X86-POP-GENERAL-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSHA/PUSHAD" (OP :OP #x60 :MODE :I64)
          NIL '(X86-PUSHA)
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x60 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE .
                                        "PUSHA is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "POPA/POPAD" (OP :OP #x61 :MODE :I64)
          NIL '(X86-POPA)
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #x61 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE .
                                        "POPA is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "BOUND" (OP :OP #x62 :MODE :I64)
          (ARG :OP1 '(G V) :OP2 '(M A))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SECOND-OPERAND-IS-A-REGISTER))))
    (INST :EVEX-BYTE0 (OP :OP #x62 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "MOVSXD" (OP :OP #x63 :MODE :O64)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-MOVSX)
          '((:UD (UD-LOCK-USED))))
    (INST "ARPL" (OP :OP #x63 :MODE :I64)
          (ARG :OP1 '(E W) :OP2 '(G W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-FS (OP :OP #x64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST :PREFIX-GS (OP :OP #x65)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST :PREFIX-OPSIZE (OP :OP #x66)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST :PREFIX-ADDRSIZE (OP :OP #x67)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "PUSH"
          (OP :OP #x68 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(I Z))
          '(X86-PUSH-I)
          '((:UD (UD-LOCK-USED))))
    (INST "IMUL" (OP :OP #x69)
          (ARG :OP1 '(G V)
               :OP2 '(E V)
               :OP3 '(I Z))
          '(X86-IMUL-OP/EN-RMI)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH"
          (OP :OP #x6A :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(I B))
          '(X86-PUSH-I)
          '((:UD (UD-LOCK-USED))))
    (INST "IMUL" (OP :OP #x6B)
          (ARG :OP1 '(G V)
               :OP2 '(E V)
               :OP3 '(I B))
          '(X86-IMUL-OP/EN-RMI)
          '((:UD (UD-LOCK-USED))))
    (INST "INS/INSB" (OP :OP #x6C)
          (ARG :OP1 '(Y B) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "INS/INSW/INSD" (OP :OP #x6D)
          (ARG :OP1 '(Y Z) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUTS/OUTSB" (OP :OP #x6E)
          (ARG :OP1 '(Y B) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUTS/OUTSW/OUTSD" (OP :OP #x6F)
          (ARG :OP1 '(Y Z) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "JO"
          (OP :OP #x70 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNO"
          (OP :OP #x71 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JB/NAE/C"
          (OP :OP #x72 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNB/AE/NC"
          (OP :OP #x73 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JZ/E"
          (OP :OP #x74 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNZ/NE"
          (OP :OP #x75 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JBE/NA"
          (OP :OP #x76 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNBE/A"
          (OP :OP #x77 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JS"
          (OP :OP #x78 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNS"
          (OP :OP #x79 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JP/PE"
          (OP :OP #x7A :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNP/PO"
          (OP :OP #x7B :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JL/NGE"
          (OP :OP #x7C :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNL/GE"
          (OP :OP #x7D :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JLE/NG"
          (OP :OP #x7E :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNLE/G"
          (OP :OP #x7F :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-ONE-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "ADD"
          (OP :OP #x80
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR"
          (OP :OP #x80
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC"
          (OP :OP #x80
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB"
          (OP :OP #x80
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND"
          (OP :OP #x80
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB"
          (OP :OP #x80
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR"
          (OP :OP #x80
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMP"
          (OP :OP #x80
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "ADD"
          (OP :OP #x81
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR"
          (OP :OP #x81
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC"
          (OP :OP #x81
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB"
          (OP :OP #x81
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND"
          (OP :OP #x81
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB"
          (OP :OP #x81
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR"
          (OP :OP #x81
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMP"
          (OP :OP #x81
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "ADD"
          (OP :OP #x82
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR"
          (OP :OP #x82
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC"
          (OP :OP #x82
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB"
          (OP :OP #x82
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND"
          (OP :OP #x82
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB"
          (OP :OP #x82
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR"
          (OP :OP #x82
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMP"
          (OP :OP #x82
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1)
              :MODE :I64)
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x82 :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "Opcode 0x82 is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "ADD"
          (OP :OP #x83
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x0))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "OR"
          (OP :OP #x83
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x1))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "ADC"
          (OP :OP #x83
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x2))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SBB"
          (OP :OP #x83
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x6))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "AND"
          (OP :OP #x83
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x3))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SUB"
          (OP :OP #x83
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x4))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XOR"
          (OP :OP #x83
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x5))
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMP"
          (OP :OP #x83
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-1))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x8))
          '((:UD (UD-LOCK-USED))))
    (INST "TEST" (OP :OP #x84)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "TEST" (OP :OP #x85)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x86)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XCHG" (OP :OP #x87)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "MOV" (OP :OP #x88)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-MOV-OP/EN-MR)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #x89)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-MOV-OP/EN-MR)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #x8A)
          (ARG :OP1 '(G B) :OP2 '(E B))
          '(X86-MOV-OP/EN-RM)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #x8B)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-MOV-OP/EN-RM)
          '((:UD (UD-LOCK-USED))))
    ;; TODO: For (S w) operands, sensible modr/m.reg values are 0-5
    ;; because there are 6 segment registers.  Will these
    ;; instructions #UD when modr/m.reg = 6 or 7? E.g., when modr/m
    ;; is #x30 or #x38.
    (INST "MOV" (OP :OP #x8C)
          (ARG :OP1 '(E V) :OP2 '(S W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LEA" (OP :OP #x8D)
          (ARG :OP1 '(G V) :OP2 '(M))
          '(X86-LEA)
          '((:UD (UD-SOURCE-OPERAND-IS-A-REGISTER)
                 (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #x8E)
          (ARG :OP1 '(S W) :OP2 '(E W))
          'NIL
          '((:UD (EQUAL (MODR/M->REG MODR/M) #x1)
                 (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #x8F
              :REG #x0
              :SUPERSCRIPTS '(:1A :D64)
              :GROUP '(:GROUP-1A))
          (ARG :OP1 '(E V))
          '(X86-POP-EV)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x90)
          (ARG :OP1 '(:R8))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x91)
          (ARG :OP1 '(:RCX/R9) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x92)
          (ARG :OP1 '(:RDX/R10) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x93)
          (ARG :OP1 '(:RBX/R11) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x94)
          (ARG :OP1 '(:RSP/R12) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x95)
          (ARG :OP1 '(:RBP/R13) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x96)
          (ARG :OP1 '(:RSI/R14) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "XCHG" (OP :OP #x97)
          (ARG :OP1 '(:RDI/R15) :OP2 '(:RAX))
          '(X86-XCHG)
          '((:UD (UD-LOCK-USED))))
    (INST "CBW/CWDE/CDQE" (OP :OP #x98)
          NIL '(X86-CBW/CWD/CDQE)
          '((:UD (UD-LOCK-USED))))
    (INST "CWD/CDQ/CQO" (OP :OP #x99)
          NIL '(X86-CWD/CDQ/CQO)
          '((:UD (UD-LOCK-USED))))
    (INST "CALL" (OP :OP #x9A :MODE :I64)
          (ARG :OP1 '(A P))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "#UD" (OP :OP #x9A :MODE :O64)
          NIL
          '(X86-ILLEGAL-INSTRUCTION
            (MESSAGE .
                     "far CALL is illegal in the 64-bit mode!"))
          '((:UD T)))
    (INST "FWAIT/WAIT" (OP :OP #x9B)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "PUSHF/D/Q"
          (OP :OP #x9C :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(F V))
          '(X86-PUSHF)
          '((:UD (UD-LOCK-USED))))
    (INST "POPF/D/Q"
          (OP :OP #x9D :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(F V))
          '(X86-POPF)
          '((:UD (UD-LOCK-USED))))
    (INST "SAHF" (OP :OP #x9E)
          NIL '(X86-SAHF)
          '((:UD (UD-LOCK-USED)
                 (AND (EQUAL PROC-MODE #x0)
                      (EQUAL (FEATURE-FLAG-MACRO :LAHF-SAHF) #x0)))))
    (INST "LAHF" (OP :OP #x9F)
          NIL '(X86-LAHF)
          '((:UD (UD-LOCK-USED)
                 (AND (EQUAL PROC-MODE #x0)
                      (EQUAL (FEATURE-FLAG-MACRO :LAHF-SAHF) #x0)))))
    (INST "MOV" (OP :OP #xA0)
          (ARG :OP1 '(:AL) :OP2 '(O B))
          '(X86-MOV-OP/EN-FD)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xA1)
          (ARG :OP1 '(:RAX) :OP2 '(O V))
          '(X86-MOV-OP/EN-FD)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xA2)
          (ARG :OP1 '(O B) :OP2 '(:AL))
          '(X86-MOV-OP/EN-TD)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xA3)
          (ARG :OP1 '(O V) :OP2 '(:RAX))
          '(X86-MOV-OP/EN-TD)
          '((:UD (UD-LOCK-USED))))
    (INST "MOVS/B" (OP :OP #xA4)
          (ARG :OP1 '(Y B) :OP2 '(X B))
          '(X86-MOVS)
          '((:UD (UD-LOCK-USED))))
    (INST "MOVS/W/D/Q" (OP :OP #xA5)
          (ARG :OP1 '(Y V) :OP2 '(X V))
          '(X86-MOVS)
          '((:UD (UD-LOCK-USED))))
    (INST "CMPS/B" (OP :OP #xA6)
          (ARG :OP1 '(X B) :OP2 '(Y B))
          '(X86-CMPS)
          '((:UD (UD-LOCK-USED))))
    (INST "CMPS/W/D" (OP :OP #xA7)
          (ARG :OP1 '(X V) :OP2 '(Y V))
          '(X86-CMPS)
          '((:UD (UD-LOCK-USED))))
    (INST "TEST" (OP :OP #xA8)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "TEST" (OP :OP #xA9)
          (ARG :OP1 '(:RAX) :OP2 '(I Z))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-RAX-I (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "STOS/B" (OP :OP #xAA)
          (ARG :OP1 '(Y B) :OP2 '(:AL))
          '(X86-STOS)
          '((:UD (UD-LOCK-USED))))
    (INST "STOS/W/D/Q" (OP :OP #xAB)
          (ARG :OP1 '(Y V) :OP2 '(:RAX))
          '(X86-STOS)
          '((:UD (UD-LOCK-USED))))
    (INST "LODS/B" (OP :OP #xAC)
          (ARG :OP1 '(:AL) :OP2 '(X B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LODS/W/D/Q" (OP :OP #xAD)
          (ARG :OP1 '(:RAX) :OP2 '(X V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "SCAS/B" (OP :OP #xAE)
          (ARG :OP1 '(:AL) :OP2 '(Y B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "SCAS/W/D/Q" (OP :OP #xAF)
          (ARG :OP1 '(:RAX) :OP2 '(Y V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB0)
          (ARG :OP1 '(:AL/R8L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB1)
          (ARG :OP1 '(:CL/R9L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB2)
          (ARG :OP1 '(:DL/R10L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB3)
          (ARG :OP1 '(:BL/R11L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB4)
          (ARG :OP1 '(:AH/R12L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB5)
          (ARG :OP1 '(:CH/R13L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB6)
          (ARG :OP1 '(:DH/R14L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB7)
          (ARG :OP1 '(:BH/R15L) :OP2 '(I B))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB8)
          (ARG :OP1 '(:RAX/R8) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xB9)
          (ARG :OP1 '(:RCX/R9) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBA)
          (ARG :OP1 '(:RDX/R10) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBB)
          (ARG :OP1 '(:RBX/R11) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBC)
          (ARG :OP1 '(:RSP/R12) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBD)
          (ARG :OP1 '(:RBP/R13) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBE)
          (ARG :OP1 '(:RSI/R14) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xBF)
          (ARG :OP1 '(:RDI/R15) :OP2 '(I V))
          '(X86-MOV-OP/EN-OI)
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xC0
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xC0
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xC0
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xC0
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xC0
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xC0
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xC0
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xC1
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xC1
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xC1
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xC1
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xC1
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xC1
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xC1
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RET"
          (OP :OP #xC2 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(I W))
          '(X86-RET)
          '((:UD (UD-LOCK-USED))))
    (INST "RET"
          (OP :OP #xC3 :SUPERSCRIPTS '(:F64))
          NIL '(X86-RET)
          '((:UD (UD-LOCK-USED))))
    ;; C4 and C5 are first bytes of the vex prefixes, both
    ;; in 32-bit and IA-32e modes.  However, in the 32-bit
    ;; and compatibility modes, the second byte determines
    ;; whether the instruction is LES/LDS or a VEX
    ;; instruction.  We use :o64 here because we're sure
    ;; that an "opcode" of C4 and C5 in the 64-bit mode will
    ;; not have a modr/m corresponding to it --- basically,
    ;; we shouldn't be looking up modr/m info. for these
    ;; opcodes in the 64-bit mode.
    (INST :VEX3-BYTE0 (OP :OP #xC4 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "LES" (OP :OP #xC4 :MODE :I64)
          (ARG :OP1 '(G Z) :OP2 '(M P))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST :VEX2-BYTE0 (OP :OP #xC5 :MODE :O64)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "LDS" (OP :OP #xC5 :MODE :I64)
          (ARG :OP1 '(G Z) :OP2 '(M P))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST "MOV"
          (OP :OP #xC6
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-11))
          (ARG :OP1 '(E B) :OP2 '(I B))
          '(X86-MOV-OP/EN-MI)
          '((:UD (UD-LOCK-USED))))
    (INST "XABORT"
          (OP :OP #xC6
              :REG #x7
              :MOD #x3
              :R/M #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-11)
              :FEAT '(:RTM))
          (ARG :OP1 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MOV"
          (OP :OP #xC7
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-11))
          (ARG :OP1 '(E V) :OP2 '(I Z))
          '(X86-MOV-OP/EN-MI)
          '((:UD (UD-LOCK-USED))))
    (INST "XBEGIN"
          (OP :OP #xC7
              :REG #x7
              :MOD #x3
              :R/M #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-11)
              :FEAT '(:RTM))
          (ARG :OP1 '(J Z))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ENTER" (OP :OP #xC8)
          (ARG :OP1 '(I W) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LEAVE"
          (OP :OP #xC9 :SUPERSCRIPTS '(:D64))
          NIL '(X86-LEAVE)
          '((:UD (UD-LOCK-USED))))
    (INST "RET" (OP :OP #xCA)
          (ARG :OP1 '(I W))
          'NIL
          'NIL)
    (INST "RET" (OP :OP #xCB) NIL 'NIL 'NIL)
    (INST "INT3" (OP :OP #xCC)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "INT" (OP :OP #xCD)
          (ARG :OP1 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "INTO" (OP :OP #xCE :MODE :I64)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #xCE :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE .
                                        "INTO is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "IRET/D/Q" (OP :OP #xCF)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xD0
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xD0
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xD0
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xD0
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xD0
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xD0
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xD0
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xD1
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xD1
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xD1
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xD1
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xD1
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xD1
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xD1
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(#x1))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xD2
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xD2
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xD2
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xD2
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xD2
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xD2
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xD2
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E B) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROL"
          (OP :OP #xD3
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "ROR"
          (OP :OP #xD3
              :REG #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCL"
          (OP :OP #xD3
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "RCR"
          (OP :OP #xD3
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHL/SAL"
          (OP :OP #xD3
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SHR"
          (OP :OP #xD3
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "SAR"
          (OP :OP #xD3
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-2))
          (ARG :OP1 '(E V) :OP2 '(:CL))
          '(X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR)
          '((:UD (UD-LOCK-USED))))
    (INST "AAM" (OP :OP #xD4 :MODE :I64)
          (ARG :OP1 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #xD4 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "AAM is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "AAD" (OP :OP #xD5 :MODE :I64)
          (ARG :OP1 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #xD5 :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "AAD is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "XLAT/XLATB" (OP :OP #xD7)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST :ESC (OP :OP #xD8)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xD9)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDA)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDB)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDC)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDD)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDE)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST :ESC (OP :OP #xDF)
          'NIL
          'NIL
          '((:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST "LOOPNE/LOOPNZ"
          (OP :OP #xE0 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-LOOP)
          '((:UD (UD-LOCK-USED))))
    (INST "LOOPE/LOOPZ"
          (OP :OP #xE1 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-LOOP)
          '((:UD (UD-LOCK-USED))))
    (INST "LOOP"
          (OP :OP #xE2 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-LOOP)
          '((:UD (UD-LOCK-USED))))
    (INST "JrCXZ"
          (OP :OP #xE3 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-JRCXZ)
          '((:UD (UD-LOCK-USED))))
    (INST "IN" (OP :OP #xE4)
          (ARG :OP1 '(:AL) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "IN" (OP :OP #xE5)
          (ARG :OP1 '(:EAX) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUT" (OP :OP #xE6)
          (ARG :OP1 '(I B) :OP2 '(:AL))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUT" (OP :OP #xE7)
          (ARG :OP1 '(I B) :OP2 '(:EAX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "CALL"
          (OP :OP #xE8 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-CALL-E8-OP/EN-M)
          '((:UD (UD-LOCK-USED))))
    (INST "JMP"
          (OP :OP #xE9 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-NEAR-JMP-OP/EN-D)
          '((:UD (UD-LOCK-USED))))
    (INST "JMP" (OP :OP #xEA :MODE :I64)
          (ARG :OP1 '(A P))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST
     "#UD" (OP :OP #xEA :MODE :O64)
     NIL
     '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "JMP is illegal in the 64-bit mode!"))
     '((:UD T)))
    (INST "JMP"
          (OP :OP #xEB :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J B))
          '(X86-NEAR-JMP-OP/EN-D)
          '((:UD (UD-LOCK-USED))))
    (INST "IN" (OP :OP #xEC)
          (ARG :OP1 '(:AL) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "IN" (OP :OP #xED)
          (ARG :OP1 '(:EAX) :OP2 '(:DX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUT" (OP :OP #xEE)
          (ARG :OP1 '(:DX) :OP2 '(:AL))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "OUT" (OP :OP #xEF)
          (ARG :OP1 '(:DX) :OP2 '(:EAX))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-LOCK (OP :OP #xF0)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "INT1" (OP :OP #xF1)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST :PREFIX-REPNE (OP :OP #xF2)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST :PREFIX-REP/REPE (OP :OP #xF3)
          'NIL
          '(:NO-INSTRUCTION)
          'NIL)
    (INST "HLT" (OP :OP #xF4)
          NIL '(X86-HLT)
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "CMC" (OP :OP #xF5)
          NIL '(X86-CMC/CLC/STC/CLD/STD)
          '((:UD (UD-LOCK-USED))))
    (INST "TEST"
          (OP :OP #xF6
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "NOT"
          (OP :OP #xF6
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-NOT/NEG-F6-F7)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "NEG"
          (OP :OP #xF6
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-NOT/NEG-F6-F7)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "MUL"
          (OP :OP #xF6
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-MUL)
          '((:UD (UD-LOCK-USED))))
    (INST "IMUL"
          (OP :OP #xF6
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-IMUL-OP/EN-M)
          '((:UD (UD-LOCK-USED))))
    (INST "DIV"
          (OP :OP #xF6
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-DIV)
          '((:UD (UD-LOCK-USED))))
    (INST "IDIV"
          (OP :OP #xF6
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-IDIV)
          '((:UD (UD-LOCK-USED))))
    (INST "TEST"
          (OP :OP #xF7
              :REG #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I (OPERATION . #x7))
          '((:UD (UD-LOCK-USED))))
    (INST "NOT"
          (OP :OP #xF7
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-NOT/NEG-F6-F7)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "NEG"
          (OP :OP #xF7
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-NOT/NEG-F6-F7)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "MUL"
          (OP :OP #xF7
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-MUL)
          '((:UD (UD-LOCK-USED))))
    (INST "IMUL"
          (OP :OP #xF7
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-IMUL-OP/EN-M)
          '((:UD (UD-LOCK-USED))))
    (INST "DIV"
          (OP :OP #xF7
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-DIV)
          '((:UD (UD-LOCK-USED))))
    (INST "IDIV"
          (OP :OP #xF7
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-3))
          (ARG :OP1 '(E B))
          '(X86-IDIV)
          '((:UD (UD-LOCK-USED))))
    (INST "CLC" (OP :OP #xF8)
          NIL '(X86-CMC/CLC/STC/CLD/STD)
          '((:UD (UD-LOCK-USED))))
    (INST "STC" (OP :OP #xF9)
          NIL '(X86-CMC/CLC/STC/CLD/STD)
          '((:UD (UD-LOCK-USED))))
    (INST "CLI" (OP :OP #xFA)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "STI" (OP :OP #xFB)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "CLD" (OP :OP #xFC)
          NIL '(X86-CMC/CLC/STC/CLD/STD)
          'NIL)
    (INST "STD" (OP :OP #xFD)
          NIL '(X86-CMC/CLC/STC/CLD/STD)
          '((:UD (UD-LOCK-USED))))
    (INST "INC"
          (OP :OP #xFE
           :REG #x0
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-4))
       (ARG :OP1 '(E B))
       '(X86-INC/DEC-FE-FF)
       '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
 (INST "DEC"
       (OP :OP #xFE
           :REG #x1
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-4))
       (ARG :OP1 '(E B))
       '(X86-INC/DEC-FE-FF)
       '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
 (INST "INC"
       (OP :OP #xFF
           :REG #x0
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E V))
       '(X86-INC/DEC-FE-FF)
       '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
 (INST "DEC"
       (OP :OP #xFF
           :REG #x1
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E V))
       '(X86-INC/DEC-FE-FF)
       '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
 (INST "near CALL"
       (OP :OP #xFF
           :REG #x2
           :SUPERSCRIPTS '(:1A :F64)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E V))
       '(X86-CALL-FF/2-OP/EN-M)
       '((:UD (UD-LOCK-USED))))
 (INST "far CALL"
       (OP :OP #xFF
           :REG #x3
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E P))
       'NIL
       '((:UD (UD-LOCK-USED))))
 (INST "near JMP"
       (OP :OP #xFF
           :REG #x4
           :SUPERSCRIPTS '(:1A :F64)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E V))
       '(X86-NEAR-JMP-OP/EN-M)
       '((:UD (UD-LOCK-USED))))
 (INST "far JMP"
       (OP :OP #xFF
           :REG #x5
           :MOD :MEM
           :SUPERSCRIPTS '(:1A)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(M P))
       '(X86-FAR-JMP-OP/EN-D)
       '((:UD (UD-LOCK-USED))))
 (INST "PUSH"
       (OP :OP #xFF
           :REG #x6
           :SUPERSCRIPTS '(:1A :D64)
           :GROUP '(:GROUP-5))
       (ARG :OP1 '(E V))
       '(X86-PUSH-EV)
       '((:UD (UD-LOCK-USED))))))

(defconst *pre-two-byte-opcode-map*
  '((INST "SLDT"
          (OP :OP #xF00
              :REG #x0
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(M W))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "SLDT"
          (OP :OP #xF00
              :REG #x0
              :MOD #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(R V))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "STR"
          (OP :OP #xF00
              :REG #x1
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(M W))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "STR"
          (OP :OP #xF00
              :REG #x1
              :MOD #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(R V))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "LLDT"
          (OP :OP #xF00
              :REG #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(E W))
          '(X86-LLDT)
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "LTR"
          (OP :OP #xF00
              :REG #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "VERR"
          (OP :OP #xF00
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "VERW"
          (OP :OP #xF00
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-6))
          (ARG :OP1 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "SGDT"
          (OP :OP #xF01
              :REG #x0
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M S))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "VMCALL"
          (OP :OP #xF01
              :REG #x0
              :MOD #x3
              :R/M #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          'NIL)
    (INST "VMLAUNCH"
          (OP :OP #xF01
              :REG #x0
              :MOD #x3
              :R/M #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "VMRESUME"
          (OP :OP #xF01
              :REG #x0
              :MOD #x3
              :R/M #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          'NIL)
    (INST "VMXOFF"
          (OP :OP #xF01
              :REG #x0
              :MOD #x3
              :R/M #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          ;; BOZO Rob -- following GP only if executed in VMX root operation!
          '((:GP (GP-CPL-NOT-0))))
    (INST "SIDT"
          (OP :OP #xF01
              :REG #x1
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M S))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "MONITOR"
          (OP :OP #xF01
              :REG #x1
              :MOD #x3
              :R/M #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:MONITOR))
          NIL 'NIL
          '((:UD (UD-CPL-IS-NOT-ZERO))))
    (INST "MWAIT"
          (OP :OP #xF01
              :REG #x1
              :MOD #x3
              :R/M #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:MONITOR))
          NIL 'NIL
          '((:UD (UD-CPL-IS-NOT-ZERO))))
    (INST "CLAC"
          (OP :OP #xF01
              :REG #x1
              :MOD #x3
              :R/M #x2
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:SMAP))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-CPL-IS-NOT-ZERO))))
    (INST "STAC"
          (OP :OP #xF01
              :REG #x1
              :MOD #x3
              :R/M #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:SMAP))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-CPL-IS-NOT-ZERO))))
    (INST "ENCLS"
          (OP :OP #xF01
              :REG #x1
              :MOD #x3
              :R/M #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          'NIL)
    (INST "LGDT"
          (OP :OP #xF01
              :REG #x2
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M S))
          '(X86-LGDT)
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "LIDT"
          (OP :OP #xF01
              :REG #x3
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M S))
          '(X86-LIDT)
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "XGETBV"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x0
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:XSAVE))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->OSXSAVE (CR4)) #x0))))
    (INST "XSETBV"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:XSAVE))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->OSXSAVE (CR4)) #x0))))
    (INST "VMFUNC"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          'NIL)
    (INST "XEND"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:RTM))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-OPR-USED)
                 (UD-REPS-USED))))
    (INST "XTEST"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:HLE :RTM))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ENCLU"
          (OP :OP #xF01
              :REG #x3
              :MOD #x3
              :R/M #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          '((:NM (NM-CR0-TS-IS-1))))
    (INST "SMSW"
          (OP :OP #xF01
              :REG #x4
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M W))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "SMSW"
          (OP :OP #xF01
              :REG #x4
              :MOD #x3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(R V))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-UMIP-IS-1)))))
    (INST "LMSW"
          (OP :OP #xF01
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "INVLPG"
          (OP :OP #xF01
              :REG #x7
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          (ARG :OP1 '(M B))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))
            (:GP (GP-CPL-NOT-0))))
    (INST "SWAPGS"
          (OP :OP #xF01
              :REG #x7
              :MOD #x3
              :R/M #x0
              :MODE :O64
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "RDTSCP"
          (OP :OP #xF01
              :REG #x7
              :MOD #x3
              :R/M #x1
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-7)
              :FEAT '(:RDTSCP))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LAR" (OP :OP #xF02)
          (ARG :OP1 '(G V) :OP2 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LSL" (OP :OP #xF03)
          (ARG :OP1 '(G V) :OP2 '(E W))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "SYSCALL" (OP :OP #xF05 :MODE :O64)
          NIL '(X86-SYSCALL-BOTH-VIEWS)
          '((:UD (UD-LOCK-USED)
                 (EQUAL (IA32_EFERBITS->SCE (N12 (IA32_EFER)))
                        #x0))))
    (INST "CLTS" (OP :OP #xF06)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0))))
    (INST "SYSRET" (OP :OP #xF07 :MODE :O64)
          NIL '(X86-SYSRET)
          '((:UD (UD-LOCK-USED)
                 (EQUAL (IA32_EFERBITS->SCE (N12 (IA32_EFER)))
                        #x0))
            (:GP (GP-CPL-NOT-0))))
    (INST "INVD" (OP :OP #xF08)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "WBINVD" (OP :OP #xF09)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "UD2"
          (OP :OP #xF0B :SUPERSCRIPTS '(:1B))
          NIL
          '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "UD2 encountered!"))
          'NIL)
    (INST "prefetchw(/1)" (OP :OP #xF0D)
          (ARG :OP1 '(E V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MOVUPS"
          (OP :OP #xF10
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "MOVUPD"
          (OP :OP #xF10 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "MOVSS"
          (OP :OP #xF10 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SS))
          '(X86-MOVSS/MOVSD-OP/EN-RM (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "MOVSD"
          (OP :OP #xF10 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SD))
          '(X86-MOVSS/MOVSD-OP/EN-RM (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "MOVSD"
          (OP :OP #xF10
              :VEX '(:0F :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSD"
          (OP :OP #xF10
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSS"
          (OP :OP #xF10
              :VEX '(:0F :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSS"
          (OP :OP #xF10
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVUPD"
          (OP :OP #xF10
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPD"
          (OP :OP #xF10
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPS"
          (OP :OP #xF10
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPS"
          (OP :OP #xF10
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVSD"
          (OP :OP #xF10
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          (ARG :OP1 '(:ModR/M.reg :XMM)
               :OP2 '(:VEX.vvvv   :XMM)
               :OP3 '(:ModR/M.r/m :XMM))
          NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSD"
          (OP :OP #xF10
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL
          NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSS"
          (OP :OP #xF10
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSS"
          (OP :OP #xF10
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF10
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF10
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF10
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF10
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF10
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF10
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "MOVUPS"
          (OP :OP #xF11
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(W PS) :OP2 '(V PS))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "MOVUPD"
          (OP :OP #xF11 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(W PD) :OP2 '(V PD))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "MOVSS"
          (OP :OP #xF11 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(W SS)
               :OP2 '(H X)
               :OP3 '(V SS))
          '(X86-MOVSS/MOVSD-OP/EN-MR (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "MOVSD"
          (OP :OP #xF11 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(W SD)
               :OP2 '(H X)
               :OP3 '(V SD))
          '(X86-MOVSS/MOVSD-OP/EN-MR (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "VMOVSD"
          (OP :OP #xF11
              :VEX '(:0F :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSD"
          (OP :OP #xF11
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSS"
          (OP :OP #xF11
              :VEX '(:0F :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSS"
          (OP :OP #xF11
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVUPD"
          (OP :OP #xF11
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPD"
          (OP :OP #xF11
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPS"
          (OP :OP #xF11
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVUPS"
          (OP :OP #xF11
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVSD"
          (OP :OP #xF11
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSD"
          (OP :OP #xF11
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSS"
          (OP :OP #xF11
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVSS"
          (OP :OP #xF11
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF11
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF11
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPD"
          (OP :OP #xF11
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF11
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF11
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVUPS"
          (OP :OP #xF11
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "MOVLPS"
          (OP :OP #xF12 :MOD :MEM :PFX :NO-PREFIX)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          '(X86-MOVLPS/MOVLPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "MOVHLPS"
          (OP :OP #xF12 :MOD #x3 :PFX :NO-PREFIX)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(U Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE)))))
    (INST "MOVLPD"
          (OP :OP #xF12 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          '(X86-MOVLPS/MOVLPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVSLDUP"
          (OP :OP #xF12 :PFX :F3 :FEAT '(:SSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          '(X86-MOVLPS/MOVLPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-4 (:SSE3)))))
    (INST "MOVDDUP"
          (OP :OP #xF12 :PFX :F2 :FEAT '(:SSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          '(X86-MOVLPS/MOVLPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-5 (:SSE3)))))
    (INST "VMOVDDUP"
          (OP :OP #xF12
              :VEX '(:0F :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVDDUP"
          (OP :OP #xF12
              :VEX '(:0F :256 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVHLPS"
          (OP :OP #xF12
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(U Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVLPD"
          (OP :OP #xF12
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVLPS"
          (OP :OP #xF12
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSLDUP"
          (OP :OP #xF12
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVSLDUP"
          (OP :OP #xF12
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVDDUP"
          (OP :OP #xF12
              :EVEX '(:0F :128 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDDUP"
          (OP :OP #xF12
              :EVEX '(:0F :256 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDDUP"
          (OP :OP #xF12
              :EVEX '(:0F :512 :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVHLPS"
          (OP :OP #xF12
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVLPD"
          (OP :OP #xF12
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVLPS"
          (OP :OP #xF12
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512F)
              :MOD :MEM)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVSLDUP"
          (OP :OP #xF12
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVSLDUP"
          (OP :OP #xF12
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVSLDUP"
          (OP :OP #xF12
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "MOVLPS"
          (OP :OP #xF13
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(M Q) :OP2 '(V Q))
          '(X86-MOVLPS/MOVLPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVLPD"
          (OP :OP #xF13 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(M Q) :OP2 '(V Q))
          '(X86-MOVLPS/MOVLPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMOVLPD"
          (OP :OP #xF13
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVLPS"
          (OP :OP #xF13
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V Q)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVLPD"
          (OP :OP #xF13
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVLPS"
          (OP :OP #xF13
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "UNPCKLPS"
          (OP :OP #xF14
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-UNPCK?PS-OP/EN-RM (HIGH/LOW . #x0))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "UNPCKLPD"
          (OP :OP #xF14 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-UNPCK?PD-OP/EN-RM (HIGH/LOW . #x0))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VUNPCKLPD"
          (OP :OP #xF14
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKLPD"
          (OP :OP #xF14
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKLPS"
          (OP :OP #xF14
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKLPS"
          (OP :OP #xF14
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKLPD"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKLPD"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKLPD"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VUNPCKLPS"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKLPS"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKLPS"
          (OP :OP #xF14
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "UNPCKHPS"
          (OP :OP #xF15
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-UNPCK?PS-OP/EN-RM (HIGH/LOW . #x1))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "UNPCKHPD"
          (OP :OP #xF15 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-UNPCK?PD-OP/EN-RM (HIGH/LOW . #x1))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VUNPCKHPD"
          (OP :OP #xF15
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKHPD"
          (OP :OP #xF15
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKHPS"
          (OP :OP #xF15
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKHPS"
          (OP :OP #xF15
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VUNPCKHPD"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKHPD"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKHPD"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VUNPCKHPS"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKHPS"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VUNPCKHPS"
          (OP :OP #xF15
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "MOVHPS"
          (OP :OP #xF16
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:V1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          '(X86-MOVHPS/MOVHPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "MOVLHPS"
          (OP :OP #xF16 :MOD #x3 :PFX :NO-PREFIX)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(U Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE)))))
    (INST "MOVHPD"
          (OP :OP #xF16
              :PFX :66
              :SUPERSCRIPTS '(:V1)
              :FEAT '(:SSE2))
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          '(X86-MOVHPS/MOVHPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))
            (:UD (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST "MOVSHDUP"
          (OP :OP #xF16 :PFX :F3 :FEAT '(:SSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE3)))))
    (INST "VMOVHPD"
          (OP :OP #xF16
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVHPS"
          (OP :OP #xF16
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVLHPS"
          (OP :OP #xF16
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(U Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVSHDUP"
          (OP :OP #xF16
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVSHDUP"
          (OP :OP #xF16
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVHPD"
          (OP :OP #xF16
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVHPS"
          (OP :OP #xF16
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512F)
              :MOD :MEM)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVLHPS"
          (OP :OP #xF16
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVSHDUP"
          (OP :OP #xF16
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVSHDUP"
          (OP :OP #xF16
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VMOVSHDUP"
          (OP :OP #xF16
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "MOVHPS"
          (OP :OP #xF17
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:V1)
              :FEAT '(:SSE))
          (ARG :OP1 '(M Q) :OP2 '(V Q))
          '(X86-MOVHPS/MOVHPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVHPD"
          (OP :OP #xF17
              :PFX :66
              :SUPERSCRIPTS '(:V1)
              :FEAT '(:SSE2))
          (ARG :OP1 '(M Q) :OP2 '(V Q))
          '(X86-MOVHPS/MOVHPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMOVHPD"
          (OP :OP #xF17
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVHPS"
          (OP :OP #xF17
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V DQ)
               :OP2 '(H Q)
               :OP3 '(M Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVHPD"
          (OP :OP #xF17
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVHPS"
          (OP :OP #xF17
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "PREFETCHNTA"
          (OP :OP #xF18
              :REG #x0
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "PREFETCHT0"
          (OP :OP #xF18
              :REG #x1
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "PREFETCHT1"
          (OP :OP #xF18
              :REG #x2
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "PREFETCHT2"
          (OP :OP #xF18
              :REG #x3
              :MOD :MEM
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RESERVEDNOP" (OP :OP #xF18 :REG #x4
                            :SUPERSCRIPTS '(:1A)
                            :GROUP '(:GROUP-16))
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF18 :REG #x5
                            :SUPERSCRIPTS '(:1A)
                            :GROUP '(:GROUP-16))
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF18 :REG #x6
                            :SUPERSCRIPTS '(:1A)
                            :GROUP '(:GROUP-16))
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF18 :REG #x7
                            :SUPERSCRIPTS '(:1A)
                            :GROUP '(:GROUP-16))
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF18 :MOD #x3
                            :SUPERSCRIPTS '(:1A)
                            :GROUP '(:GROUP-16))
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF19)
          NIL 'NIL
          'NIL)
    ;; Source: BNDLDX-Load Extended Bounds Using Address
    ;; Translation, Intel Vol. 2 (May 2018 edition)
    ;; "Any encoding of this instruction that does not specify
    ;; base or index register will treat those registers as zero
    ;; (constant)."
    ;; This leads me to infer that even though the source operand
    ;; is obtained from the SIB byte, we should not #UD when the
    ;; SIB byte is not present (i.e., when ModR/M.r/m != #b100 --
    ;; See Table 2-2 in Intel Vol. 2).
    (INST "BNDLDX"
          (OP :OP #xF1A
              :MOD :MEM
              :PFX :NO-PREFIX
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(M))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (<= #x4
                     ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                     ;; the Intel manuals.  It should be ModRM.reg,
                     ;; because the latter is used to encode the BND
                     ;; registers.
                     ;; "- If ModRM.r/m and REX encodes BND4-BND15 when
                     ;;    Intel MPX is enabled."
                     (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (IF (EQL PROC-MODE #x0)
                     ;; RIP-relative addressing in 64-bit mode
                     ;; Source: Table 2-7 (RIP-Relative Addressing),
                     ;; Intel Vol. 2 (May 2018 edition)
                     ;; "- If ModRM is RIP-relative"
                     (AND (EQL (MODR/M->MOD MODR/M) #x0)
                          (OR ;; SIB Byte not present
                           (EQL (MODR/M->R/M MODR/M) #x5)
                           (AND ;; SIB Byte present
                            (EQL (MODR/M->R/M MODR/M) #x4)
                            (EQL (SIB->BASE SIB) #x5)
                            (EQL (SIB->INDEX SIB) #x4))))
                     ;; In Compatibility/Protected Mode:
                     ;; "- If 67H prefix is used and CS.D=1.
                     ;;  - If 67H prefix is not used and CS.D=0."
                     (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                         (EQL (CS.D) #x1)
                         (EQL (CS.D) #x0))))))
    ;; Source: BNDLDX-Load Extended Bounds Using Address
    ;; Translation, Intel Vol. 2 (May 2018 edition)
    ;; "The reg-reg form of this instruction will remain a NOP."
    (INST "RESERVEDNOP"
          (OP :OP #xF1A
              :MOD #x3
              :PFX :NO-PREFIX
              :FEAT '(:MPX))
          NIL 'NIL
          'NIL)
    (INST "BNDMOV"
          (OP :OP #xF1A
              :MOD :MEM
              :PFX :66
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(M))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP)
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->R/M MODR/M) REX-BYTE #x0))
                 ;; In Compatibility/Protected Mode:
                 ;; - If 67H prefix is used and CS.D=1.
                 ;; - If 67H prefix is not used and CS.D=0.
                 (IF (AND (NOT (EQL PROC-MODE #x0))
                          (EQL (PREFIXES->ADR PREFIXES) #x67))
                     (EQL (CS.D) #x1)
                     (EQL (CS.D) #x0)))))
    (INST "BNDMOV"
          (OP :OP #xF1A
              :MOD #x3
              :PFX :66
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(MB))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP)
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->R/M MODR/M) REX-BYTE #x0))
                 ;; In Compatibility/Protected Mode:
                 ;; - If 67H prefix is used and CS.D=1.
                 ;; - If 67H prefix is not used and CS.D=0.
                 (IF (AND (NOT (EQL PROC-MODE #x0))
                          (EQL (PREFIXES->ADR PREFIXES) #x67))
                     (EQL (CS.D) #x1)
                     (EQL (CS.D) #x0)))))
    (INST "BNDCL"
          (OP :OP #xF1A
              :PFX :F3
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                 ;; the Intel manuals.  It should be ModRM.reg,
                 ;; because the latter is used to encode the BND
                 ;; registers.
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (AND (NOT (EQL PROC-MODE #x0))
                      ;; In Compatibility/Protected Mode:
                      ;; - If 67H prefix is used and CS.D=1.
                      ;; - If 67H prefix is not used and CS.D=0.
                      (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                          (EQL (CS.D) #x1)
                          (EQL (CS.D) #x0))))))
    (INST "BNDCU"
          (OP :OP #xF1A
              :PFX :F2
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                 ;; the Intel manuals.  It should be ModRM.reg,
                 ;; because the latter is used to encode the BND
                 ;; registers.
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (AND (NOT (EQL PROC-MODE #x0))
                      ;; In Compatibility/Protected Mode:
                      ;; - If 67H prefix is used and CS.D=1.
                      ;; - If 67H prefix is not used and CS.D=0.
                      (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                          (EQL (CS.D) #x1)
                          (EQL (CS.D) #x0))))))
    ;; Non-mpx encoding will fall through.
    ;; (INST "RESERVEDNOP" (OP :OP #xF1A)
    ;;       NIL 'NIL
    ;;       'NIL)
    (INST "BNDSTX"
          ;; Source: BNDSTX-Load Extended Bounds Using Address
          ;; Translation, Intel Vol. 2 (May 2018 edition)
          ;; "Any encoding of this instruction that does not specify
          ;; base or index register will treat those registers as zero
          ;; (constant)."
          ;; Similar to BNDLDX.
          (OP :OP #xF1B
              :MOD :MEM
              :PFX :NO-PREFIX
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(M) :OP2 '(RB))
          'NIL
          '((:UD (UD-LOCK-USED)
                 ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                 ;; the Intel manuals.  It should be ModRM.reg,
                 ;; because the latter is used to encode the BND
                 ;; registers.
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (IF (EQL PROC-MODE #x0)
                     ;; RIP-relative addressing in 64-bit mode
                     ;; Source: Table 2-7 (RIP-Relative Addressing),
                     ;; Intel Vol. 2 (May 2018 edition)
                     ;; - If ModRM is RIP-relative
                     (AND (EQL (MODR/M->MOD MODR/M) #x0)
                          (OR ;; SIB Byte not present
                           (EQL (MODR/M->R/M MODR/M) #x5)
                           (AND ;; SIB Byte present
                            (EQL (MODR/M->R/M MODR/M) #x4)
                            (EQL (SIB->BASE SIB) #x5)
                            (EQL (SIB->INDEX SIB) #x4))))
                     ;; In Compatibility/Protected Mode:
                     ;; - If 67H prefix is used and CS.D=1.
                     ;; - If 67H prefix is not used and CS.D=0.
                     (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                         (EQL (CS.D) #x1)
                         (EQL (CS.D) #x0))))))
    ;; "The reg-reg form of this instruction will remain a NOP."
    (INST "RESERVEDNOP"
          (OP :OP #xF1B
              :MOD #x3
              :PFX :NO-PREFIX
              :FEAT '(:MPX))
          NIL 'NIL
          'NIL)
    (INST "BNDMOV"
          (OP :OP #xF1B
              :MOD :MEM
              :PFX :66
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(M) :OP2 '(RB))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP)
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->R/M MODR/M) REX-BYTE #x0))
                 ;; In Compatibility/Protected Mode:
                 ;; - If 67H prefix is used and CS.D=1.
                 ;; - If 67H prefix is not used and CS.D=0.
                 (IF (AND (NOT (EQL PROC-MODE #x0))
                          (EQL (PREFIXES->ADR PREFIXES) #x67))
                     (EQL (CS.D) #x1)
                     (EQL (CS.D) #x0)))))
    (INST "BNDMOV"
          (OP :OP #xF1B
              :MOD #x3
              :PFX :66
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(MB) :OP2 '(RB))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP)
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->R/M MODR/M) REX-BYTE #x0))
                 ;; In Compatibility/Protected Mode:
                 ;; - If 67H prefix is used and CS.D=1.
                 ;; - If 67H prefix is not used and CS.D=0.
                 (IF (AND (NOT (EQL PROC-MODE #x0))
                          (EQL (PREFIXES->ADR PREFIXES) #x67))
                     (EQL (CS.D) #x1)
                     (EQL (CS.D) #x0)))))
    (INST "BNDMK"
          (OP :OP #xF1B
              :MOD :MEM
              :PFX :F3
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(M Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                 ;; the Intel manuals.  It should be ModRM.reg,
                 ;; because the latter is used to encode the BND
                 ;; registers.
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (IF (EQL PROC-MODE #x0)
                     ;; - If RIP-relative addressing is used.
                     ;; Source: Table 2-7 (RIP-Relative Addressing),
                     ;; Intel Vol. 2 (May 2018 edition)
                     (AND (EQL (MODR/M->MOD MODR/M) #x0)
                          (OR ;; SIB Byte not present
                           (EQL (MODR/M->R/M MODR/M) #x5)
                           (AND ;; SIB Byte present
                            (EQL (MODR/M->R/M MODR/M) #x4)
                            (EQL (SIB->BASE SIB) #x5)
                            (EQL (SIB->INDEX SIB) #x4))))
                     ;; In Compatibility/Protected Mode:
                     ;; - If 67H prefix is used and CS.D=1.
                     ;; - If 67H prefix is not used and CS.D=0.
                     (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                         (EQL (CS.D) #x1)
                         (EQL (CS.D) #x0))))))
    ;; Source: BNDMK-Make Bounds, Intel Vol. 2 (May 2018 Edition)
    ;; "The reg-reg form of this instruction retains legacy behavior
    ;; (NOP)."
    (INST "RESERVEDNOP"
          (OP :OP #xF1B
              :MOD #x3
              :PFX :F3
              :FEAT '(:MPX))
          NIL 'NIL
          'NIL)
    (INST "BNDCN"
          (OP :OP #xF1B
              :PFX :F2
              :FEAT '(:MPX)
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-16))
          (ARG :OP1 '(RB) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 ;; [Shilpi] "ModRM.r/m" below is likely a typo in
                 ;; the Intel manuals.  It should be ModRM.reg,
                 ;; because the latter is used to encode the BND
                 ;; registers.
                 ;; - If ModRM.r/m and REX encodes BND4-BND15 when
                 ;;   Intel MPX is enabled.
                 (<= #x4 (REG-INDEX (MODR/M->REG MODR/M) REX-BYTE #x2))
                 (AND (NOT (EQL PROC-MODE #x0))
                      ;; In Compatibility/Protected Mode:
                      ;; - If 67H prefix is used and CS.D=1.
                      ;; - If 67H prefix is not used and CS.D=0.
                      (IF (EQL (PREFIXES->ADR PREFIXES) #x67)
                          (EQL (CS.D) #x1)
                          (EQL (CS.D) #x0))))))
    ;; Non-mpx encoding will fall through.
    ;; (INST "RESERVEDNOP" (OP :OP #xF1B)
    ;;       NIL 'NIL
    ;;       'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF1C)
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF1D)
          NIL 'NIL
          'NIL)
    (INST "RESERVEDNOP" (OP :OP #xF1E)
          NIL 'NIL
          'NIL)
    (INST "NOP" (OP :OP #xF1F)
          (ARG :OP1 '(E V))
          '(X86-TWO-BYTE-NOP)
          '((:UD (UD-LOCK-USED))))
    (INST "MOV" (OP :OP #xF20)
          (ARG :OP1 '(R D) :OP2 '(C D))
          '(X86-MOV-CONTROL-REGS-OP/EN-MR)
          '((:UD (UD-LOCK-USED)
                 (LET ((REG (MODR/M->REG MODR/M)))
                      (IF (AND (EQUAL PROC-MODE #x0)
                               (LOGBITP #x2 REX-BYTE))
                          (NOT (EQUAL REG #x0))
                          (OR (EQUAL REG #x1)
                              (EQUAL REG #x5)
                              (EQUAL REG #x6)
                              (EQUAL REG #x7)))))
            (:GP (GP-CPL-NOT-0))))
    (INST "MOV" (OP :OP #xF21)
          (ARG :OP1 '(R D) :OP2 '(D D))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (AND (EQUAL (CR4BITS->DE (CR4)) #x1)
                      (OR (EQUAL (MODR/M->REG MODR/M) #x4)
                          (EQUAL (MODR/M->REG MODR/M) #x5))))
            (:GP (GP-CPL-NOT-0))))
    (INST "MOV" (OP :OP #xF22)
          (ARG :OP1 '(C D) :OP2 '(R D))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (LET ((REG (MODR/M->REG MODR/M)))
                      (IF (AND (EQUAL PROC-MODE #x0)
                               (LOGBITP #x2 REX-BYTE))
                          (NOT (EQUAL REG #x0))
                          (OR (EQUAL REG #x1)
                              (EQUAL REG #x5)
                              (EQUAL REG #x6)
                              (EQUAL REG #x7)))))
            (:GP (GP-CPL-NOT-0))))
    (INST "MOV" (OP :OP #xF23)
          (ARG :OP1 '(D D) :OP2 '(R D))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (AND (EQUAL (CR4BITS->DE (CR4)) #x1)
                      (OR (EQUAL (MODR/M->REG MODR/M) #x4)
                          (EQUAL (MODR/M->REG MODR/M) #x5))))
            (:GP (GP-CPL-NOT-0))))
    (INST "MOVAPS"
          (OP :OP #xF28
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          '(X86-MOVAPS/MOVAPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-1 (:SSE)))))
    (INST "MOVAPD"
          (OP :OP #xF28 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          '(X86-MOVAPS/MOVAPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))))
    (INST "VMOVAPD"
          (OP :OP #xF28
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPD"
          (OP :OP #xF28
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPS"
          (OP :OP #xF28
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPS"
          (OP :OP #xF28
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPD"
          (OP :OP #xF28
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPD"
          (OP :OP #xF28
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPD"
          (OP :OP #xF28
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF28
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF28
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF28
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512F)))))
    (INST "MOVAPS"
          (OP :OP #xF29
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(W PS) :OP2 '(V PS))
          '(X86-MOVAPS/MOVAPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-1 (:SSE)))))
    (INST "MOVAPD"
          (OP :OP #xF29 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(W PD) :OP2 '(V PD))
          '(X86-MOVAPS/MOVAPD-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))))
    (INST "VMOVAPD"
          (OP :OP #xF29
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPD"
          (OP :OP #xF29
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPS"
          (OP :OP #xF29
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPS"
          (OP :OP #xF29
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVAPD"
          (OP :OP #xF29
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPD"
          (OP :OP #xF29
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPD"
          (OP :OP #xF29
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF29
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF29
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512VL :AVX512F)))))
    (INST "VMOVAPS"
          (OP :OP #xF29
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1 (:AVX512F)))))
    (INST "CVTPI2PS"
          (OP :OP #xF2A
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(V PS) :OP2 '(Q PI))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-5 (:MMX)))))
    (INST "CVTPI2PD"
          (OP :OP #xF2A :PFX :66 :FEAT '(:MMX))
          (ARG :OP1 '(V PD) :OP2 '(Q PI))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-6 (:MMX)))))
    (INST "CVTSI2SS"
          (OP :OP #xF2A :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(E Y))
          '(X86-CVTSI2S?-OP/EN-RM (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "CVTSI2SD"
          (OP :OP #xF2A :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(E Y))
          '(X86-CVTSI2S?-OP/EN-RM (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCVTSI2SD"
          (OP :OP #xF2A
              :VEX '(:0F :NDS :LIG :F2 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(E Y))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSI2SD"
          (OP :OP #xF2A
              :VEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(E Y))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSI2SS"
          (OP :OP #xF2A
              :VEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(E Y))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSI2SS"
          (OP :OP #xF2A
              :VEX '(:0F :NDS :LIG :F3 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(E Y))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSI2SD"
          (OP :OP #xF2A
              :EVEX '(:0F :NDS :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10NF (:AVX512F)))))
    (INST "VCVTSI2SD"
          (OP :OP #xF2A
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10NF (:AVX512F)))))
    (INST "VCVTSI2SS"
          (OP :OP #xF2A
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSI2SS"
          (OP :OP #xF2A
              :EVEX '(:0F :NDS :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "MOVNTPS"
          (OP :OP #xF2B
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(M PS) :OP2 '(V PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVNTPD"
          (OP :OP #xF2B :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(M PD) :OP2 '(V PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMOVNTPD"
          (OP :OP #xF2B
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M PD) :OP2 '(V PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTPD"
          (OP :OP #xF2B
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M PD) :OP2 '(V PD))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTPS"
          (OP :OP #xF2B
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M PS) :OP2 '(V PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTPS"
          (OP :OP #xF2B
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M PS) :OP2 '(V PS))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTPD"
          (OP :OP #xF2B
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTPD"
          (OP :OP #xF2B
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTPD"
          (OP :OP #xF2B
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512F)))))
    (INST "VMOVNTPS"
          (OP :OP #xF2B
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTPS"
          (OP :OP #xF2B
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTPS"
          (OP :OP #xF2B
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512F)))))
    (INST "CVTTPS2PI"
          (OP :OP #xF2C
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P PI) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-5 (:MMX)))))
    (INST "CVTTPD2PI"
          (OP :OP #xF2C :PFX :66 :FEAT '(:MMX))
          (ARG :OP1 '(P PI) :OP2 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-4 (:MMX)))))
    (INST "CVTTSS2SI"
          (OP :OP #xF2C :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          '(X86-CVTS?2SI/CVTTS?2SI-OP/EN-RM (SP/DP . #x0)
                                            (TRUNC . T))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "CVTTSD2SI"
          (OP :OP #xF2C :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          '(X86-CVTS?2SI/CVTTS?2SI-OP/EN-RM (SP/DP . #x1)
                                            (TRUNC . T))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCVTTSD2SI"
          (OP :OP #xF2C
              :VEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTTSD2SI"
          (OP :OP #xF2C
              :VEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTTSS2SI"
          (OP :OP #xF2C
              :VEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTTSS2SI"
          (OP :OP #xF2C
              :VEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTTSD2SI"
          (OP :OP #xF2C
              :EVEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSD2SI"
          (OP :OP #xF2C
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSS2SI"
          (OP :OP #xF2C
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSS2SI"
          (OP :OP #xF2C
              :EVEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "CVTPS2PI"
          (OP :OP #xF2D
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P PI) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-5 (:MMX)))))
    (INST "CVTPD2PI"
          (OP :OP #xF2D :PFX :66 :FEAT '(:MMX))
          (ARG :OP1 '(Q PI) :OP2 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-4 (:MMX)))))
    (INST "CVTSS2SI"
          (OP :OP #xF2D :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          '(X86-CVTS?2SI/CVTTS?2SI-OP/EN-RM (SP/DP . #x0)
                                            (TRUNC))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "CVTSD2SI"
          (OP :OP #xF2D :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          '(X86-CVTS?2SI/CVTTS?2SI-OP/EN-RM (SP/DP . #x1)
                                            (TRUNC))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCVTSD2SI"
          (OP :OP #xF2D
              :VEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSD2SI"
          (OP :OP #xF2D
              :VEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSS2SI"
          (OP :OP #xF2D
              :VEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSS2SI"
          (OP :OP #xF2D
              :VEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSD2SI"
          (OP :OP #xF2D
              :EVEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSD2SI"
          (OP :OP #xF2D
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSS2SI"
          (OP :OP #xF2D
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSS2SI"
          (OP :OP #xF2D
              :EVEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "UCOMISS"
          (OP :OP #xF2E
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V SS) :OP2 '(W SS))
          '(X86-COMIS?/UCOMIS?-OP/EN-RM (OPERATION . #x9)
                                        (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "UCOMISD"
          (OP :OP #xF2E :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD) :OP2 '(W SD))
          '(X86-COMIS?/UCOMIS?-OP/EN-RM (OPERATION . #x9)
                                        (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VUCOMISD"
          (OP :OP #xF2E
              :VEX '(:0F :LIG :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VUCOMISS"
          (OP :OP #xF2E
              :VEX '(:0F :LIG :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VUCOMISD"
          (OP :OP #xF2E
              :EVEX '(:0F :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VUCOMISS"
          (OP :OP #xF2E
              :EVEX '(:0F :LIG :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "COMISS"
          (OP :OP #xF2F
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V SS) :OP2 '(W SS))
          '(X86-COMIS?/UCOMIS?-OP/EN-RM (OPERATION . #x9)
                                        (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "COMISD"
          (OP :OP #xF2F :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD) :OP2 '(W SD))
          '(X86-COMIS?/UCOMIS?-OP/EN-RM (OPERATION . #x9)
                                        (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCOMISD"
          (OP :OP #xF2F
              :VEX '(:0F :LIG :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD) :OP2 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCOMISS"
          (OP :OP #xF2F
              :VEX '(:0F :LIG :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS) :OP2 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCOMISD"
          (OP :OP #xF2F
              :EVEX '(:0F :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCOMISS"
          (OP :OP #xF2F
              :EVEX '(:0F :LIG :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "WRMSR" (OP :OP #xF30)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RDTSC" (OP :OP #xF31)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RDMSR" (OP :OP #xF32)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RDPMC" (OP :OP #xF33)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (AND (GP-CPL-NOT-0)
                      (GP-CR4-PCE-IS-0)))))
    (INST "SYSENTER" (OP :OP #xF34)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CR0-PE-IS-0))))
    (INST "SYSEXIT" (OP :OP #xF35)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:GP (GP-CPL-NOT-0) (GP-CR0-PE-IS-0))))
    (INST "GETSEC" (OP :OP #xF37)
          NIL 'NIL
          ;; TODO: Lock Used? Feature flag info?
          'NIL)
    (INST :3-BYTE-ESCAPE (OP :OP #xF38)
          'NIL
          '(THREE-BYTE-OPCODE-DECODE-AND-EXECUTE (SECOND-ESCAPE-BYTE . OPCODE))
          'NIL)
    (INST :3-BYTE-ESCAPE (OP :OP #xF3A)
          'NIL
          '(THREE-BYTE-OPCODE-DECODE-AND-EXECUTE (SECOND-ESCAPE-BYTE . OPCODE))
          'NIL)
    (INST "CMOVO" (OP :OP #xF40)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVNO" (OP :OP #xF41)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KANDB"
          (OP :OP #xF41
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KANDD"
          (OP :OP #xF41
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KANDQ"
          (OP :OP #xF41
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KANDW"
          (OP :OP #xF41
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVB/C/NAE" (OP :OP #xF42)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KANDNB"
          (OP :OP #xF42
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KANDND"
          (OP :OP #xF42
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KANDNQ"
          (OP :OP #xF42
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KANDNW"
          (OP :OP #xF42
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVAE/NB/NC" (OP :OP #xF43)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVE/Z" (OP :OP #xF44)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KNOTB"
          (OP :OP #xF44
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KNOTD"
          (OP :OP #xF44
              :VEX '(:0F :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KNOTQ"
          (OP :OP #xF44
              :VEX '(:0F :L0 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KNOTW"
          (OP :OP #xF44
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVNE/NZ" (OP :OP #xF45)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KORB"
          (OP :OP #xF45
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KORD"
          (OP :OP #xF45
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KORQ"
          (OP :OP #xF45
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KORW"
          (OP :OP #xF45
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVBE/NA" (OP :OP #xF46)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KXNORB"
          (OP :OP #xF46
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KXNORD"
          (OP :OP #xF46
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KXNORQ"
          (OP :OP #xF46
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KXNORW"
          (OP :OP #xF46
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVA/NBE" (OP :OP #xF47)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KXORB"
          (OP :OP #xF47
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KXORD"
          (OP :OP #xF47
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KXORQ"
          (OP :OP #xF47
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KXORW"
          (OP :OP #xF47
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "CMOVS" (OP :OP #xF48)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVNS" (OP :OP #xF49)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVP/PE" (OP :OP #xF4A)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KADDB"
          (OP :OP #xF4A
              :VEX '(:0F :L1 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-VEX B)
               :OP3 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KADDD"
          (OP :OP #xF4A
              :VEX '(:0F :L1 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KADDQ"
          (OP :OP #xF4A
              :VEX '(:0F :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KADDW"
          (OP :OP #xF4A
              :VEX '(:0F :L1 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "CMOVNP/PO" (OP :OP #xF4B)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KUNPCKBW"
          (OP :OP #xF4B
              :VEX '(:0F :NDS :L1 :66 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-VEX W)
               :OP3 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "KUNPCKDQ"
          (OP :OP #xF4B
              :VEX '(:0F :NDS :L1 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-VEX Q)
               :OP3 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KUNPCKWD"
          (OP :OP #xF4B
              :VEX '(:0F :NDS :L1 :W0)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-VEX D)
               :OP3 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "CMOVL/NGE" (OP :OP #xF4C)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVNL/GE" (OP :OP #xF4D)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVLE/NG" (OP :OP #xF4E)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "CMOVNLE/G" (OP :OP #xF4F)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-CMOVCC)
          '((:UD (UD-LOCK-USED))))
    (INST "MOVMSKPS"
          (OP :OP #xF50
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(G Y) :OP2 '(U PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE)))))
    (INST "MOVMSKPD"
          (OP :OP #xF50 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(G Y) :OP2 '(U PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "VMOVMSKPD"
          (OP :OP #xF50
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(U PD))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VMOVMSKPD"
          (OP :OP #xF50
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(U PD))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VMOVMSKPS"
          (OP :OP #xF50
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(U PS))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VMOVMSKPS"
          (OP :OP #xF50
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(G Y) :OP2 '(U PS))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "SQRTPS"
          (OP :OP #xF51
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          '(X86-SQRTPS-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "SQRTPD"
          (OP :OP #xF51 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          '(X86-SQRTPD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "SQRTSS"
          (OP :OP #xF51 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-SQRTS?-OP/EN-RM (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "SQRTSD"
          (OP :OP #xF51 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-SQRTS?-OP/EN-RM (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VSQRTPD"
          (OP :OP #xF51
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSQRTPD"
          (OP :OP #xF51
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSQRTPS"
          (OP :OP #xF51
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSQRTPS"
          (OP :OP #xF51
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSQRTSD"
          (OP :OP #xF51
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VSQRTSS"
          (OP :OP #xF51
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VSQRTPD"
          (OP :OP #xF51
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSQRTPD"
          (OP :OP #xF51
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSQRTPD"
          (OP :OP #xF51
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VSQRTPS"
          (OP :OP #xF51
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSQRTPS"
          (OP :OP #xF51
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSQRTPS"
          (OP :OP #xF51
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VSQRTSD"
          (OP :OP #xF51
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VSQRTSS"
          (OP :OP #xF51
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "RSQRTPS"
          (OP :OP #xF52
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "RSQRTSS"
          (OP :OP #xF52 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "VRSQRTPS"
          (OP :OP #xF52
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VRSQRTPS"
          (OP :OP #xF52
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VRSQRTSS"
          (OP :OP #xF52
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "RCPPS"
          (OP :OP #xF53
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "RCPSS"
          (OP :OP #xF53 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "VRCPPS"
          (OP :OP #xF53
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VRCPPS"
          (OP :OP #xF53
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VRCPSS"
          (OP :OP #xF53
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "ANDPS"
          (OP :OP #xF54
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x3))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "ANDPD"
          (OP :OP #xF54 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x3))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VANDPD"
          (OP :OP #xF54
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDPD"
          (OP :OP #xF54
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDPS"
          (OP :OP #xF54
              :VEX '(:0F :NDS :128)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDPS"
          (OP :OP #xF54
              :VEX '(:0F :NDS :256)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDPD"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDPD"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDPD"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VANDPS"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDPS"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDPS"
          (OP :OP #xF54
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "ANDNPS"
          (OP :OP #xF55
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #xD))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "ANDNPD"
          (OP :OP #xF55 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #xD))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VANDNPD"
          (OP :OP #xF55
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDNPD"
          (OP :OP #xF55
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDNPS"
          (OP :OP #xF55
              :VEX '(:0F :NDS :128)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDNPS"
          (OP :OP #xF55
              :VEX '(:0F :NDS :256)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VANDNPD"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDNPD"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDNPD"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VANDNPS"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDNPS"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VANDNPS"
          (OP :OP #xF55
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "ORPS"
          (OP :OP #xF56
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x1))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "ORPD"
          (OP :OP #xF56 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x1))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VORPD"
          (OP :OP #xF56
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VORPD"
          (OP :OP #xF56
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VORPS"
          (OP :OP #xF56
              :VEX '(:0F :NDS :128)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VORPS"
          (OP :OP #xF56
              :VEX '(:0F :NDS :256)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VORPD"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VORPD"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VORPD"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VORPS"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VORPS"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VORPS"
          (OP :OP #xF56
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "XORPS"
          (OP :OP #xF57
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x5))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "XORPD"
          (OP :OP #xF57 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x5))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VXORPD"
          (OP :OP #xF57
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VXORPD"
          (OP :OP #xF57
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VXORPS"
          (OP :OP #xF57
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VXORPS"
          (OP :OP #xF57
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VXORPD"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VXORPD"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VXORPD"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VXORPS"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VXORPS"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VXORPS"
          (OP :OP #xF57
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "ADDPS"
          (OP :OP #xF58
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x0))
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "ADDPD"
          (OP :OP #xF58 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x0))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "ADDSS"
          (OP :OP #xF58 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x0)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "ADDSD"
          (OP :OP #xF58 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x0)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VADDPD"
          (OP :OP #xF58
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDPD"
          (OP :OP #xF58
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDPS"
          (OP :OP #xF58
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDPS"
          (OP :OP #xF58
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDSD"
          (OP :OP #xF58
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VADDSS"
          (OP :OP #xF58
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VADDPD"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VADDPD"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VADDPD"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VADDPS"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VADDPS"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VADDPS"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VADDSD"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VADDSS"
          (OP :OP #xF58
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "MULPS"
          (OP :OP #xF59
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x1A))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "MULPD"
          (OP :OP #xF59 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x1A))
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "MULSS"
          (OP :OP #xF59 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x1A)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "MULSD"
          (OP :OP #xF59 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x1A)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VMULPD"
          (OP :OP #xF59
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMULPD"
          (OP :OP #xF59
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMULPS"
          (OP :OP #xF59
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMULPS"
          (OP :OP #xF59
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMULSD"
          (OP :OP #xF59
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VMULSS"
          (OP :OP #xF59
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VMULPD"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMULPD"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMULPD"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMULPS"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMULPS"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMULPS"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMULSD"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VMULSS"
          (OP :OP #xF59
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "CVTPS2PD"
          (OP :OP #xF5A
              :PFX :NO-PREFIX
              :FEAT '(:SSE2))
          (ARG :OP1 '(V PD) :OP2 '(W PS))
          '(X86-CVTPS2PD-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "CVTPD2PS"
          (OP :OP #xF5A :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PS) :OP2 '(W PD))
          '(X86-CVTPD2PS-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "CVTSS2SD"
          (OP :OP #xF5A :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H X)
               :OP3 '(W SS))
          '(X86-CVTS?2S?-OP/EN-RM (DP-TO-SP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "CVTSD2SS"
          (OP :OP #xF5A :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SS)
               :OP2 '(H X)
               :OP3 '(W SD))
          '(X86-CVTS?2S?-OP/EN-RM (DP-TO-SP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCVTPD2PS"
          (OP :OP #xF5A
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTPD2PS"
          (OP :OP #xF5A
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTPS2PD"
          (OP :OP #xF5A
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTPS2PD"
          (OP :OP #xF5A
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSD2SS"
          (OP :OP #xF5A
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H X)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTSS2SD"
          (OP :OP #xF5A
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H X)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCVTPD2PS"
          (OP :OP #xF5A
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2PS"
          (OP :OP #xF5A
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2PS"
          (OP :OP #xF5A
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTPS2PD"
          (OP :OP #xF5A
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2PD"
          (OP :OP #xF5A
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512VL)))))
    (INST "VCVTPS2PD"
          (OP :OP #xF5A
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VCVTSD2SS"
          (OP :OP #xF5A
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VCVTSS2SD"
          (OP :OP #xF5A
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "CVTDQ2PS"
          (OP :OP #xF5B
              :PFX :NO-PREFIX
              :FEAT '(:SSE2))
          (ARG :OP1 '(V PS) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "CVTPS2DQ"
          (OP :OP #xF5B :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "CVTTPS2DQ"
          (OP :OP #xF5B :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "VCVTDQ2PS"
          (OP :OP #xF5B
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W DQ))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTDQ2PS"
          (OP :OP #xF5B
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS) :OP2 '(W DQ))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTPS2DQ"
          (OP :OP #xF5B
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTPS2DQ"
          (OP :OP #xF5B
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTTPS2DQ"
          (OP :OP #xF5B
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTTPS2DQ"
          (OP :OP #xF5B
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTDQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTDQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTDQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTQQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :128 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTQQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :256 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTQQ2PS"
          (OP :OP #xF5B
              :EVEX '(:0F :512 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPS2DQ"
          (OP :OP #xF5B
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "SUBPS"
          (OP :OP #xF5C
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x4))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "SUBPD"
          (OP :OP #xF5C :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x4))
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "SUBSS"
          (OP :OP #xF5C :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x4)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "SUBSD"
          (OP :OP #xF5C :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x4)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VSUBPD"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSUBPD"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSUBPS"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSUBPS"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VSUBSD"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VSUBSS"
          (OP :OP #xF5C
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VSUBPD"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSUBPD"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSUBPD"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VSUBPS"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSUBPS"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSUBPS"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VSUBSD"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VSUBSS"
          (OP :OP #xF5C
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "MINPS"
          (OP :OP #xF5D
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x24))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "MINPD"
          (OP :OP #xF5D :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x24))
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "MINSS"
          (OP :OP #xF5D :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x24)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "MINSD"
          (OP :OP #xF5D :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x24)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VMINPD"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMINPD"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMINPS"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMINPS"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMINSD"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VMINSS"
          (OP :OP #xF5D
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMINPD"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMINPD"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMINPD"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMINPS"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMINPS"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMINPS"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMINSD"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VMINSS"
          (OP :OP #xF5D
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "DIVPS"
          (OP :OP #xF5E
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x1C))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "DIVPD"
          (OP :OP #xF5E :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x1C))
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "DIVSS"
          (OP :OP #xF5E :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x1C)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "DIVSD"
          (OP :OP #xF5E :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x1C)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VDIVPD"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VDIVPD"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VDIVPS"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VDIVPS"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VDIVSD"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VDIVSS"
          (OP :OP #xF5E
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VDIVPD"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VDIVPD"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VDIVPD"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VDIVPS"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VDIVPS"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VDIVPS"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VDIVSD"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VDIVSS"
          (OP :OP #xF5E
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "MAXPS"
          (OP :OP #xF5F
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          '(X86-ADDPS/SUBPS/MULPS/DIVPS/MAXPS/MINPS-OP/EN-RM (OPERATION . #x22))
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "MAXPD"
          (OP :OP #xF5F :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          '(X86-ADDPD/SUBPD/MULPD/DIVPD/MAXPD/MINPD-OP/EN-RM (OPERATION . #x22))
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "MAXSS"
          (OP :OP #xF5F :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x22)
                                                             (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "MAXSD"
          (OP :OP #xF5F :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          '(X86-ADDS?/SUBS?/MULS?/DIVS?/MAXS?/MINS?-OP/EN-RM (OPERATION . #x22)
                                                             (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VMAXPD"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMAXPD"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMAXPS"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMAXPS"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VMAXSD"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VMAXSS"
          (OP :OP #xF5F
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VMAXPD"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMAXPD"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMAXPD"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMAXPS"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMAXPS"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VMAXPS"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMAXSD"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VMAXSS"
          (OP :OP #xF5F
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "PUNPCKLBW"
          (OP :OP #xF60
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKLBW"
          (OP :OP #xF60 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKLBW"
          (OP :OP #xF60
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKLBW"
          (OP :OP #xF60
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKLBW"
          (OP :OP #xF60
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKLBW"
          (OP :OP #xF60
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKLBW"
          (OP :OP #xF60
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PUNPCKLWD"
          (OP :OP #xF61
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKLWD"
          (OP :OP #xF61 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKLWD"
          (OP :OP #xF61
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKLWD"
          (OP :OP #xF61
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKLWD"
          (OP :OP #xF61
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKLWD"
          (OP :OP #xF61
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKLWD"
          (OP :OP #xF61
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PUNPCKLDQ"
          (OP :OP #xF62
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKLDQ"
          (OP :OP #xF62 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKLDQ"
          (OP :OP #xF62
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKLDQ"
          (OP :OP #xF62
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKLDQ"
          (OP :OP #xF62
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKLDQ"
          (OP :OP #xF62
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKLDQ"
          (OP :OP #xF62
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PACKSSWB"
          (OP :OP #xF63
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PACKSSWB"
          (OP :OP #xF63 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPACKSSWB"
          (OP :OP #xF63
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPACKSSWB"
          (OP :OP #xF63
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPACKSSWB"
          (OP :OP #xF63
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPACKSSWB"
          (OP :OP #xF63
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPACKSSWB"
          (OP :OP #xF63
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PCMPGTB"
          (OP :OP #xF64
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPGTB"
          (OP :OP #xF64 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPGTB"
          (OP :OP #xF64
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPGTB"
          (OP :OP #xF64
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPGTB"
          (OP :OP #xF64
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPGTB"
          (OP :OP #xF64
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPGTB"
          (OP :OP #xF64
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PCMPGTW"
          (OP :OP #xF65
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPGTW"
          (OP :OP #xF65 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPGTW"
          (OP :OP #xF65
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPGTW"
          (OP :OP #xF65
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPGTW"
          (OP :OP #xF65
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPGTW"
          (OP :OP #xF65
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPGTW"
          (OP :OP #xF65
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PCMPGTD"
          (OP :OP #xF66
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPGTD"
          (OP :OP #xF66 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPGTD"
          (OP :OP #xF66
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPGTD"
          (OP :OP #xF66
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPGTD"
          (OP :OP #xF66
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPGTD"
          (OP :OP #xF66
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPGTD"
          (OP :OP #xF66
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PACKUSWB"
          (OP :OP #xF67
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PACKUSWB"
          (OP :OP #xF67 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPACKUSWB"
          (OP :OP #xF67
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPACKUSWB"
          (OP :OP #xF67
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPACKUSWB"
          (OP :OP #xF67
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPACKUSWB"
          (OP :OP #xF67
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPACKUSWB"
          (OP :OP #xF67
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PUNPCKHBW"
          (OP :OP #xF68
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKHBW"
          (OP :OP #xF68 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKHBW"
          (OP :OP #xF68
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKHBW"
          (OP :OP #xF68
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKHBW"
          (OP :OP #xF68
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKHBW"
          (OP :OP #xF68
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKHBW"
          (OP :OP #xF68
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PUNPCKHWD"
          (OP :OP #xF69
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKHWD"
          (OP :OP #xF69 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKHWD"
          (OP :OP #xF69
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKHWD"
          (OP :OP #xF69
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKHWD"
          (OP :OP #xF69
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKHWD"
          (OP :OP #xF69
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPUNPCKHWD"
          (OP :OP #xF69
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PUNPCKHDQ"
          (OP :OP #xF6A
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PUNPCKHDQ"
          (OP :OP #xF6A :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKHDQ"
          (OP :OP #xF6A
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKHDQ"
          (OP :OP #xF6A
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKHDQ"
          (OP :OP #xF6A
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKHDQ"
          (OP :OP #xF6A
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKHDQ"
          (OP :OP #xF6A
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PACKSSDW"
          (OP :OP #xF6B
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PACKSSDW"
          (OP :OP #xF6B :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPACKSSDW"
          (OP :OP #xF6B
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPACKSSDW"
          (OP :OP #xF6B
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPACKSSDW"
          (OP :OP #xF6B
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512BW)))))
    (INST "VPACKSSDW"
          (OP :OP #xF6B
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512BW)))))
    (INST "VPACKSSDW"
          (OP :OP #xF6B
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512BW)))))
    (INST "PUNPCKLQDQ"
          (OP :OP #xF6C :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKLQDQ"
          (OP :OP #xF6C
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKLQDQ"
          (OP :OP #xF6C
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKLQDQ"
          (OP :OP #xF6C
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKLQDQ"
          (OP :OP #xF6C
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKLQDQ"
          (OP :OP #xF6C
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "PUNPCKHQDQ"
          (OP :OP #xF6D :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPUNPCKHQDQ"
          (OP :OP #xF6D
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPUNPCKHQDQ"
          (OP :OP #xF6D
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPUNPCKHQDQ"
          (OP :OP #xF6D
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKHQDQ"
          (OP :OP #xF6D
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPUNPCKHQDQ"
          (OP :OP #xF6D
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "MOVD/Q"
          (OP :OP #xF6E
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P D) :OP2 '(E Y))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))))
    (INST "MOVD/Q"
          (OP :OP #xF6E :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V Y) :OP2 '(E Y))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "VMOVQ"
          (OP :OP #xF6E
              :VEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVD"
          (OP :OP #xF6E
              :VEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVD"
          (OP :OP #xF6E
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVQ"
          (OP :OP #xF6E
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "MOVQ"
          (OP :OP #xF6F
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))))
    (INST "MOVDQA"
          (OP :OP #xF6F :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))))
    (INST "MOVDQU"
          (OP :OP #xF6F :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VMOVDQA"
          (OP :OP #xF6F
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVDQA"
          (OP :OP #xF6F
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVDQU"
          (OP :OP #xF6F
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVDQU"
          (OP :OP #xF6F
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVDQA32"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA32"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA32"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU16"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU16"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU16"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :F2 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "VMOVDQU32"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU32"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU32"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU8"
          (OP :OP #xF6F
              :EVEX '(:0F :128 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU8"
          (OP :OP #xF6F
              :EVEX '(:0F :256 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU8"
          (OP :OP #xF6F
              :EVEX '(:0F :512 :F2 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "PSHUFW"
          (OP :OP #xF70
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q)
               :OP2 '(Q Q)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSHUFD"
          (OP :OP #xF70 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "PSHUFHW"
          (OP :OP #xF70 :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "PSHUFLW"
          (OP :OP #xF70 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSHUFD"
          (OP :OP #xF70
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSHUFD"
          (OP :OP #xF70
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSHUFHW"
          (OP :OP #xF70
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSHUFHW"
          (OP :OP #xF70
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSHUFLW"
          (OP :OP #xF70
              :VEX '(:0F :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSHUFLW"
          (OP :OP #xF70
              :VEX '(:0F :256 :F2 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSHUFD"
          (OP :OP #xF70
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSHUFD"
          (OP :OP #xF70
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSHUFD"
          (OP :OP #xF70
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPSHUFHW"
          (OP :OP #xF70
              :EVEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFHW"
          (OP :OP #xF70
              :EVEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFHW"
          (OP :OP #xF70
              :EVEX '(:0F :512 :F3 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSHUFLW"
          (OP :OP #xF70
              :EVEX '(:0F :128 :F2 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFLW"
          (OP :OP #xF70
              :EVEX '(:0F :256 :F2 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFLW"
          (OP :OP #xF70
              :EVEX '(:0F :512 :F2 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSRLW"
          (OP :OP #xF71
              :REG #x2
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLW"
          (OP :OP #xF71
              :REG #x2
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSRAW"
          (OP :OP #xF71
              :REG #x4
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRAW"
          (OP :OP #xF71
              :REG #x4
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSLLW"
          (OP :OP #xF71
              :REG #x6
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLW"
          (OP :OP #xF71
              :REG #x6
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-12))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "VPSRLVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSRLVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPSRAVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x4)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSRAVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x4)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPSLLVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSLLVW"
          (OP :OP #xF71
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPSRLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :512 :66 :WIG)
              :FEAT '(:AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSRAW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRAW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX512BW)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSRAW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :512 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLW"
          (OP :OP #xF71
              :EVEX '(:0F :NDD :512 :66 :WIG)
              :FEAT '(:AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSRLD"
          (OP :OP #xF72
              :REG #x2
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLD"
          (OP :OP #xF72
              :REG #x2
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSRAD"
          (OP :OP #xF72
              :REG #x4
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRAD"
          (OP :OP #xF72
              :REG #x4
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSLLD"
          (OP :OP #xF72
              :REG #x6
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLD"
          (OP :OP #xF72
              :REG #x6
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-13))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "VPSLLVD"
          (OP :OP #xF72
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSLLVD"
          (OP :OP #xF72
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPSRAVW"
          (OP :OP #xF72
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x4)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSRAVW"
          (OP :OP #xF72
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x4)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPSLLVW"
          (OP :OP #xF72
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPSLLVW"
          (OP :OP #xF72
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W0)
              :FEAT '(:AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPRORD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W1)
              :FEAT '(:AVX512F)
              :REG #x0)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W0)
              :FEAT '(:AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPROLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W1)
              :FEAT '(:AVX512F)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPSRLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W0)
              :FEAT '(:AVX512F)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W0)
              :FEAT '(:AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W1)
              :FEAT '(:AVX512F)
              :REG #x4)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPSLLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSLLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPSLLD"
          (OP :OP #xF72
              :EVEX '(:0F :NDD :512 :66 :W0)
              :FEAT '(:AVX512F)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PSRLQ"
          (OP :OP #xF73
              :REG #x2
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLQ"
          (OP :OP #xF73
              :REG #x2
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSRLDQ"
          (OP :OP #xF73
              :REG #x3
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSLLQ"
          (OP :OP #xF73
              :REG #x6
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(N Q) :OP2 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLQ"
          (OP :OP #xF73
              :REG #x6
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "PSLLDQ"
          (OP :OP #xF73
              :REG #x7
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-14))
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "VPSRLVQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRLVQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x2)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLDQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x3)
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRLDQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x3)
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSLLQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x6)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLDQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX)
              :REG #x7)
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSLLDQ"
          (OP :OP #xF73
              :VEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX2)
              :REG #x7)
          (ARG :OP1 '(H X)
               :OP2 '(U X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :512 :66 :W1)
              :FEAT '(:AVX512BW)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSRLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x3)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x3)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :512 :66 :WIG)
              :FEAT '(:AVX512BW)
              :REG #x3)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSLLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :512 :66 :W1)
              :FEAT '(:AVX512BW)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPSLLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x7)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW)
              :REG #x7)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLDQ"
          (OP :OP #xF73
              :EVEX '(:0F :NDD :512 :66 :WIG)
              :FEAT '(:AVX512BW)
              :REG #x7)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PCMPEQB"
          (OP :OP #xF74
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPEQB"
          (OP :OP #xF74 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-PCMPEQB-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPEQB"
          (OP :OP #xF74
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPEQB"
          (OP :OP #xF74
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPEQB"
          (OP :OP #xF74
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPEQB"
          (OP :OP #xF74
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPEQB"
          (OP :OP #xF74
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PCMPEQW"
          (OP :OP #xF75
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPEQW"
          (OP :OP #xF75 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPEQW"
          (OP :OP #xF75
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPEQW"
          (OP :OP #xF75
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPEQW"
          (OP :OP #xF75
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPEQW"
          (OP :OP #xF75
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPEQW"
          (OP :OP #xF75
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PCMPEQD"
          (OP :OP #xF76
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PCMPEQD"
          (OP :OP #xF76 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPCMPEQD"
          (OP :OP #xF76
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPEQD"
          (OP :OP #xF76
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPEQD"
          (OP :OP #xF76
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPEQD"
          (OP :OP #xF76
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPEQD"
          (OP :OP #xF76
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "EMMS" (OP :OP #xF77 :PFX :NO-PREFIX)
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR0BITS->EM (CR0)) #x1))))
    (INST "VZEROALL"
          (OP :OP #xF77
              :VEX '(:0F :256 :WIG)
              :FEAT '(:AVX))
          NIL
          NIL '((:EX (CHK-EXC :TYPE-8 (:AVX)))))
    (INST "VZEROUPPER"
          (OP :OP #xF77
              :VEX '(:0F :128 :WIG)
              :FEAT '(:AVX))
          NIL
          NIL '((:EX (CHK-EXC :TYPE-8 (:AVX)))))
    (INST "MREAD" (OP :OP #xF78)
          (ARG :OP1 '(E Y) :OP2 '(G Y))
          'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "VCVTTPD2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :256 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPD2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :128 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPD2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :512 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTTPD2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPD2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPD2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTTPS2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPS2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPS2UDQ"
          (OP :OP #xF78
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTTPS2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPS2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPS2UQQ"
          (OP :OP #xF78
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTTSD2USI"
          (OP :OP #xF78
              :EVEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSD2USI"
          (OP :OP #xF78
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSS2USI"
          (OP :OP #xF78
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTSS2USI"
          (OP :OP #xF78
              :EVEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "MWRITE" (OP :OP #xF79)
          (ARG :OP1 '(E Y) :OP2 '(G Y))
          'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "VCVTPD2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :128 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :256 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :512 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTPD2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPD2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPD2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTPS2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2UDQ"
          (OP :OP #xF79
              :EVEX '(:0F :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTPS2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPS2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPS2UQQ"
          (OP :OP #xF79
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTSD2USI"
          (OP :OP #xF79
              :EVEX '(:0F :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSD2USI"
          (OP :OP #xF79
              :EVEX '(:0F :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSS2USI"
          (OP :OP #xF79
              :EVEX '(:0F :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTSS2USI"
          (OP :OP #xF79
              :EVEX '(:0F :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTTPD2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPD2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPD2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTTPS2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPS2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTTPS2QQ"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTUDQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTUDQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTUDQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTUDQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTUDQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTUDQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTUQQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTUQQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTUQQ2PD"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :F3 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTUQQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :128 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTUQQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :256 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTUQQ2PS"
          (OP :OP #xF7A
              :EVEX '(:0F :512 :F2 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTPD2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPD2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPD2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTPS2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPS2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTPS2QQ"
          (OP :OP #xF7B
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTUSI2SD"
          (OP :OP #xF7B
              :EVEX '(:0F :NDS :LIG :F2 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10NF (:AVX512F)))))
    (INST "VCVTUSI2SD"
          (OP :OP #xF7B
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10NF (:AVX512F)))))
    (INST "VCVTUSI2SS"
          (OP :OP #xF7B
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "VCVTUSI2SS"
          (OP :OP #xF7B
              :EVEX '(:0F :NDS :LIG :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3NF (:AVX512F)))))
    (INST "HADDPD"
          (OP :OP #xF7C :PFX :66 :FEAT '(:SSE3))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE3)))))
    (INST "HADDPS"
          (OP :OP #xF7C :PFX :F2 :FEAT '(:SSE3))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE3)))))
    (INST "VHADDPD"
          (OP :OP #xF7C
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHADDPD"
          (OP :OP #xF7C
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHADDPS"
          (OP :OP #xF7C
              :VEX '(:0F :NDS :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHADDPS"
          (OP :OP #xF7C
              :VEX '(:0F :NDS :256 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "HSUBPD"
          (OP :OP #xF7D :PFX :66 :FEAT '(:SSE3))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE3)))))
    (INST "HSUBPS"
          (OP :OP #xF7D :PFX :F2 :FEAT '(:SSE3))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE3)))))
    (INST "VHSUBPD"
          (OP :OP #xF7D
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHSUBPD"
          (OP :OP #xF7D
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHSUBPS"
          (OP :OP #xF7D
              :VEX '(:0F :NDS :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VHSUBPS"
          (OP :OP #xF7D
              :VEX '(:0F :NDS :256 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "MOVD/Q"
          (OP :OP #xF7E
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(E Y) :OP2 '(P D))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))))
    (INST "MOVD/Q"
          (OP :OP #xF7E :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(E Y) :OP2 '(V Y))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "MOVQ"
          (OP :OP #xF7E :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "VMOVD"
          (OP :OP #xF7E
              :VEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(E Y) :OP2 '(V Y))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVQ"
          (OP :OP #xF7E
              :VEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVQ"
          (OP :OP #xF7E
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VMOVD"
          (OP :OP #xF7E
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVQ"
          (OP :OP #xF7E
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVQ"
          (OP :OP #xF7E
              :EVEX '(:0F :128 :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "MOVQ"
          (OP :OP #xF7F
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(Q Q) :OP2 '(P Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))))
    (INST "MOVDQA"
          (OP :OP #xF7F :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(W X) :OP2 '(V X))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))))
    (INST "MOVDQU"
          (OP :OP #xF7F :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(W X) :OP2 '(V X))
          '(X86-MOVUPS/MOVUPD/MOVDQU-OP/EN-MR)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VMOVDQA"
          (OP :OP #xF7F
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVDQA"
          (OP :OP #xF7F
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVDQU"
          (OP :OP #xF7F
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVDQU"
          (OP :OP #xF7F
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVDQA32"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA32"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA32"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQA64"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU16"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU16"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU16"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :F2 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "VMOVDQU32"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU32"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU32"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512F)))))
    (INST "VMOVDQU64"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VMOVDQU8"
          (OP :OP #xF7F
              :EVEX '(:0F :128 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU8"
          (OP :OP #xF7F
              :EVEX '(:0F :256 :F2 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512VL :AVX512BW)))))
    (INST "VMOVDQU8"
          (OP :OP #xF7F
              :EVEX '(:0F :512 :F2 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "JO"
          (OP :OP #xF80 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNO"
          (OP :OP #xF81 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JB/NAE/C"
          (OP :OP #xF82 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNB/AE/NC"
          (OP :OP #xF83 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JZ/E"
          (OP :OP #xF84 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNZ/NE"
          (OP :OP #xF85 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JBE/NA"
          (OP :OP #xF86 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNBE/A"
          (OP :OP #xF87 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JS"
          (OP :OP #xF88 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNS"
          (OP :OP #xF89 :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JP/PE"
          (OP :OP #xF8A :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNP/PO"
          (OP :OP #xF8B :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JL/NGE"
          (OP :OP #xF8C :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNL/GE"
          (OP :OP #xF8D :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JLE/NG"
          (OP :OP #xF8E :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "JNLE/G"
          (OP :OP #xF8F :SUPERSCRIPTS '(:F64))
          (ARG :OP1 '(J Z))
          '(X86-TWO-BYTE-JCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETO" (OP :OP #xF90)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KMOVB"
          (OP :OP #xF90
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ))
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512DQ)))))
    (INST "KMOVD"
          (OP :OP #xF90
              :VEX '(:0F :L0 :66 :W1)
              :FEAT '(:AVX512BW))
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512BW)))))
    (INST "KMOVQ"
          (OP :OP #xF90
              :VEX '(:0F :L0 :W1)
              :FEAT '(:AVX512BW))
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512BW)))))
    (INST "KMOVW"
          (OP :OP #xF90
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F))
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512F)))))
    (INST "SETNO" (OP :OP #xF91)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KMOVB"
          (OP :OP #xF91
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD :MEM)
          (ARG :OP1 '(K-R/M B)
               :OP2 '(K-REG B))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512DQ)))))
    (INST "KMOVD"
          (OP :OP #xF91
              :VEX '(:0F :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD :MEM)
          (ARG :OP1 '(K-R/M D)
               :OP2 '(K-REG D))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512BW)))))
    (INST "KMOVQ"
          (OP :OP #xF91
              :VEX '(:0F :L0 :W1)
              :FEAT '(:AVX512BW)
              :MOD :MEM)
          (ARG :OP1 '(K-R/M Q) :OP2 '(K-REG Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512BW)))))
    (INST "KMOVW"
          (OP :OP #xF91
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F)
              :MOD :MEM)
          (ARG :OP1 '(K-R/M W) :OP2 '(K-REG W))
          NIL
          '((:EX (CHK-EXC :TYPE-K21 (:AVX512F)))))
    (INST "SETB/NAE/C" (OP :OP #xF92)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KMOVB"
          (OP :OP #xF92
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KMOVD"
          (OP :OP #xF92
              :VEX '(:0F :L0 :F2 :W0)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KMOVQ"
          (OP :OP #xF92
              :VEX '(:0F :L0 :F2 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KMOVW"
          (OP :OP #xF92
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "SETNB/AE/NC" (OP :OP #xF93)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KMOVB"
          (OP :OP #xF93
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KMOVD"
          (OP :OP #xF93
              :VEX '(:0F :L0 :F2 :W0)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KMOVQ"
          (OP :OP #xF93
              :VEX '(:0F :L0 :F2 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KMOVW"
          (OP :OP #xF93
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "SETZ/E" (OP :OP #xF94)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETNZ/NE" (OP :OP #xF95)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETBE/NA" (OP :OP #xF96)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETNBE/A" (OP :OP #xF97)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETS" (OP :OP #xF98)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KORTESTB"
          (OP :OP #xF98
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KORTESTD"
          (OP :OP #xF98
              :VEX '(:0F :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KORTESTQ"
          (OP :OP #xF98
              :VEX '(:0F :L0 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KORTESTW"
          (OP :OP #xF98
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "SETNS" (OP :OP #xF99)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "KTESTB"
          (OP :OP #xF99
              :VEX '(:0F :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KTESTD"
          (OP :OP #xF99
              :VEX '(:0F :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KTESTQ"
          (OP :OP #xF99
              :VEX '(:0F :L0 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q) :OP2 '(K-R/M Q))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KTESTW"
          (OP :OP #xF99
              :VEX '(:0F :L0 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG W) :OP2 '(K-R/M W))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "SETP/PE" (OP :OP #xF9A)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETNP/PO" (OP :OP #xF9B)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETL/NGE" (OP :OP #xF9C)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETNL/GE" (OP :OP #xF9D)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETLE/NG" (OP :OP #xF9E)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "SETNLE/G" (OP :OP #xF9F)
          (ARG :OP1 '(E B))
          '(X86-SETCC)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH FS"
          (OP :OP #xFA0 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:FS))
          '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #xFA1 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:FS))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "CPUID" (OP :OP #xFA2)
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BT" (OP :OP #xFA3)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-BT-0F-A3)
          '((:UD (UD-LOCK-USED))))
    (INST "SHLD" (OP :OP #xFA4)
          (ARG :OP1 '(E V)
               :OP2 '(G V)
               :OP3 '(I B))
          '(X86-SHLD/SHRD)
          '((:UD (UD-LOCK-USED))))
    (INST "SHLD" (OP :OP #xFA5)
          (ARG :OP1 '(E V)
               :OP2 '(G V)
               :OP3 '(:CL))
          '(X86-SHLD/SHRD)
          '((:UD (UD-LOCK-USED))))
    (INST "PUSH GS"
          (OP :OP #xFA8 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:GS))
          '(X86-PUSH-SEGMENT-REGISTER)
          '((:UD (UD-LOCK-USED))))
    (INST "POP"
          (OP :OP #xFA9 :SUPERSCRIPTS '(:D64))
          (ARG :OP1 '(:GS))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RSM" (OP :OP #xFAA)
          NIL 'NIL
          'NIL)
    (INST "BTS" (OP :OP #xFAB)
          (ARG :OP1 '(E V) :OP2 '(G V))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "SHRD" (OP :OP #xFAC)
          (ARG :OP1 '(E V)
               :OP2 '(G V)
               :OP3 '(I B))
          '(X86-SHLD/SHRD)
          '((:UD (UD-LOCK-USED))))
    (INST "SHRD" (OP :OP #xFAD)
          (ARG :OP1 '(E V)
               :OP2 '(G V)
               :OP3 '(:CL))
          '(X86-SHLD/SHRD)
          '((:UD (UD-LOCK-USED))))
    (INST "FXSAVE"
          (OP :OP #xFAE
              :REG #x0
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FXSR))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST "RDFSBASE"
          (OP :OP #xFAE
              :REG #x0
              :MOD #x3
              :PFX :F3
              :MODE :O64
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FSGSBASE))
          (ARG :OP1 '(R Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->FSGSBASE (CR4)) #x0))))
    (INST "FXRSTOR"
          (OP :OP #xFAE
              :REG #x1
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FXSR))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))
            (:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))
    (INST "RDGSBASE"
          (OP :OP #xFAE
              :REG #x1
              :MOD #x3
              :PFX :F3
              :MODE :O64
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FSGSBASE))
          (ARG :OP1 '(R Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->FSGSBASE (CR4)) #x0))))
    (INST "LDMXCSR"
          (OP :OP #xFAE
              :REG #x2
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15))
          NIL '(X86-LDMXCSR/STMXCSR-OP/EN-M)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "WRFSBASE"
          (OP :OP #xFAE
              :REG #x2
              :MOD #x3
              :PFX :F3
              :MODE :O64
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FSGSBASE))
          (ARG :OP1 '(R Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->FSGSBASE (CR4)) #x0))))
    (INST "STMXCSR"
          (OP :OP #xFAE
              :REG #x3
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15))
          NIL '(X86-LDMXCSR/STMXCSR-OP/EN-M)
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "WRGSBASE"
          (OP :OP #xFAE
              :REG #x3
              :MOD #x3
              :PFX :F3
              :MODE :O64
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:FSGSBASE))
          (ARG :OP1 '(R Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->FSGSBASE (CR4)) #x0))))
    (INST "XSAVE"
          (OP :OP #xFAE
              :REG #x4
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:XSAVE))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->OSXSAVE (CR4)) #x0))
            (:GP (GP-CPL-NOT-0))
            (:NM (NM-CR0-TS-IS-1))))
    (INST "XRSTOR"
          (OP :OP #xFAE
              :REG #x5
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:XSAVE))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->OSXSAVE (CR4)) #x0))
            (:GP (GP-CPL-NOT-0))
            (:NM (NM-CR0-TS-IS-1))))
    (INST "LFENCE"
          (OP :OP #xFAE
              :REG #x5
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:SSE2))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "XSAVEOPT"
          (OP :OP #xFAE
              :REG #x6
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15))
          NIL 'NIL
          '((:UD (UD-LOCK-USED)
                 (EQUAL (CR4BITS->OSXSAVE (CR4)) #x0)
                 (OR (EQUAL (FEATURE-FLAG-MACRO :XSAVE) #x0)
                     (EQUAL (FEATURE-FLAG-MACRO :XSAVEOPT) #x0)))
            (:NM (NM-CR0-TS-IS-1))))
    (INST "MFENCE"
          (OP :OP #xFAE
              :REG #x6
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:SSE2))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "CLFLUSH"
          (OP :OP #xFAE
              :REG #x7
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:CLFSH))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "SFENCE"
          (OP :OP #xFAE
              :REG #x7
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-15)
              :FEAT '(:SSE))
          NIL 'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "VLDMXCSR"
          (OP :OP #xFAE
              :VEX '(:0F :LZ :WIG)
              :FEAT '(:AVX)
              :REG #x2)
          (ARG :OP1 '(M D))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VSTMXCSR"
          (OP :OP #xFAE
              :VEX '(:0F :LZ :WIG)
              :FEAT '(:AVX)
              :REG #x3)
          (ARG :OP1 '(M D))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "IMUL" (OP :OP #xFAF)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-IMUL-OP/EN-RM)
          '((:UD (UD-LOCK-USED))))
    (INST "CMPXCHG" (OP :OP #xFB0)
          (ARG :OP1 '(E B) :OP2 '(G B))
          '(X86-CMPXCHG)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMPXCHG" (OP :OP #xFB1)
          (ARG :OP1 '(E V) :OP2 '(G V))
          '(X86-CMPXCHG)
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "LSS" (OP :OP #xFB2)
          (ARG :OP1 '(G V) :OP2 '(M P))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST "BTR" (OP :OP #xFB3)
          (ARG :OP1 '(E V) :OP2 '(G V))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "LFS" (OP :OP #xFB4)
          (ARG :OP1 '(G V) :OP2 '(M P))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST "LGS" (OP :OP #xFB5)
          (ARG :OP1 '(G V) :OP2 '(M P))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-SOURCE-OPERAND-IS-A-REGISTER))))
    (INST "MOVZX" (OP :OP #xFB6)
          (ARG :OP1 '(G V) :OP2 '(E B))
          '(X86-MOVZX)
          '((:UD (UD-LOCK-USED))))
    (INST "MOVZX" (OP :OP #xFB7)
          (ARG :OP1 '(G V) :OP2 '(E W))
          '(X86-MOVZX)
          '((:UD (UD-LOCK-USED))))
    (INST "JMPE" (OP :OP #xFB8 :PFX :NO-PREFIX)
          ;; Reserved for emulator on IPF (Itanium Processor Family).
          NIL 'NIL
          'NIL)
    (INST "POPCNT" (OP :OP #xFB8
                       :PFX :F3
                       :FEAT '(:POPCNT))
          (ARG :OP1 '(G V) :OP2 '(E V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "UD1"
          (OP :OP #xFB9
              :SUPERSCRIPTS '(:1A :1C)
              :GROUP '(:GROUP-10))
          NIL
          '(X86-ILLEGAL-INSTRUCTION (MESSAGE . "UD1 encountered!"))
          'NIL)
    (INST "BT"
          (OP :OP #xFBA
              :REG #x4
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-8))
          (ARG :OP1 '(E V) :OP2 '(I B))
          '(X86-BT-0F-BA)
          '((:UD (UD-LOCK-USED))))
    (INST "BTS"
          (OP :OP #xFBA
              :REG #x5
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-8))
          (ARG :OP1 '(E B) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "BTR"
          (OP :OP #xFBA
              :REG #x6
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-8))
          (ARG :OP1 '(E B) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "BTC"
          (OP :OP #xFBA
              :REG #x7
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-8))
          (ARG :OP1 '(E B) :OP2 '(I B))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "BTC" (OP :OP #xFBB)
          (ARG :OP1 '(E V) :OP2 '(G V))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "BSF" (OP :OP #xFBC :PFX :NO-PREFIX)
          (ARG :OP1 '(G V) :OP2 '(E V))
          '(X86-BSF-OP/EN-RM)
          '((:UD (UD-LOCK-USED))))
    (INST "TZCNT" (OP :OP #xFBC :PFX :F3)
          (ARG :OP1 '(G V) :OP2 '(E V))
          'NIL
          'NIL)
    (INST "BSR" (OP :OP #xFBD :PFX :NO-PREFIX)
          (ARG :OP1 '(G V) :OP2 '(E V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "LZCNT" (OP :OP #xFBD :PFX :F3)
          (ARG :OP1 '(G V) :OP2 '(E V))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MOVSX" (OP :OP #xFBE)
          (ARG :OP1 '(G V) :OP2 '(E B))
          '(X86-MOVSXD)
          '((:UD (UD-LOCK-USED))))
    (INST "MOVSX" (OP :OP #xFBF)
          (ARG :OP1 '(G V) :OP2 '(E W))
          '(X86-MOVSXD)
          '((:UD (UD-LOCK-USED))))
    (INST "XADD" (OP :OP #xFC0)
          (ARG :OP1 '(E B) :OP2 '(G B))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "XADD" (OP :OP #xFC1)
          (ARG :OP1 '(E V) :OP2 '(G V))
          'NIL
          '((:UD (UD-LOCK-USED-DEST-NOT-MEMORY-OP))))
    (INST "CMPPS"
          (OP :OP #xFC2
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          '(X86-CMPPS-OP/EN-RMI)
          '((:EX (CHK-EXC :TYPE-2 (:SSE)))))
    (INST "CMPPD"
          (OP :OP #xFC2 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          '(X86-CMPPD-OP/EN-RMI)
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "CMPSS"
          (OP :OP #xFC2 :PFX :F3 :FEAT '(:SSE))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS)
               :OP4 '(I B))
          '(X86-CMPSS/CMPSD-OP/EN-RMI (SP/DP . #x0))
          '((:EX (CHK-EXC :TYPE-3 (:SSE)))))
    (INST "CMPSD"
          (OP :OP #xFC2 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD)
               :OP4 '(I B))
          '(X86-CMPSS/CMPSD-OP/EN-RMI (SP/DP . #x1))
          '((:EX (CHK-EXC :TYPE-3 (:SSE2)))))
    (INST "VCMPPD"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCMPPD"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCMPPS"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCMPPS"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCMPSD"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :LIG :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(H SD)
               :OP3 '(W SD)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCMPSS"
          (OP :OP #xFC2
              :VEX '(:0F :NDS :LIG :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(H SS)
               :OP3 '(W SS)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VCMPPD"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCMPPD"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCMPPD"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCMPPS"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCMPPS"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCMPPS"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCMPSD"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :LIG :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VCMPSS"
          (OP :OP #xFC2
              :EVEX '(:0F :NDS :LIG :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "MOVNTI" (OP :OP #xFC3
                       :FEAT '(:SSE2))
          (ARG :OP1 '(M Y) :OP2 '(G Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "PINSRW"
          (OP :OP #xFC4 :MOD #x3 :PFX :NO-PREFIX)
          (ARG :OP1 '(P Q)
               :OP2 '(R Y)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "PINSRW"
          (OP :OP #xFC4 :MOD :MEM :PFX :NO-PREFIX)
          (ARG :OP1 '(P Q)
               :OP2 '(M W)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "PINSRW"
          (OP :OP #xFC4 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(R Y)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "PINSRW"
          (OP :OP #xFC4 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(M W)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "VPINSRW"
          (OP :OP #xFC4
              :VEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(R Y)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPINSRW"
          (OP :OP #xFC4
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "PEXTRW"
          (OP :OP #xFC5
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(G D)
               :OP2 '(N Q)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE)))))
    (INST "PEXTRW"
          (OP :OP #xFC5 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(G D)
               :OP2 '(U DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "VPEXTRW"
          (OP :OP #xFC5
              :VEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G D)
               :OP2 '(U DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPEXTRW"
          (OP :OP #xFC5
              :EVEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "SHUFPS"
          (OP :OP #xFC6
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          '(X86-SHUFPS-OP/EN-RMI)
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "SHUFPD"
          (OP :OP #xFC6 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          '(X86-SHUFPD-OP/EN-RMI)
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VSHUFPD"
          (OP :OP #xFC6
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VSHUFPD"
          (OP :OP #xFC6
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VSHUFPS"
          (OP :OP #xFC6
              :VEX '(:0F :NDS :128 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VSHUFPS"
          (OP :OP #xFC6
              :VEX '(:0F :NDS :256 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VSHUFPD"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFPD"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFPD"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VSHUFPS"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :128 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFPS"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :256 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFPS"
          (OP :OP #xFC6
              :EVEX '(:0F :NDS :512 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "CMPXCHG16B"
          (OP :OP #xFC7
              :REG #x1
              :MOD :MEM
              :PFX :NO-PREFIX
              ;; This opcode is obviously not encodable in non 64-bit modes, but I
              ;; won't bother to include that here --- REX bytes shouldn't even be
              ;; detected in that mode.
              :REX :W
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:CMPXCHG16B))
          (ARG :OP1 '(M DQ))
          'NIL
          '((:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "CMPXCHG8B"
          (OP :OP #xFC7
              :REG #x1
              :MOD :MEM
              :PFX :NO-PREFIX
              ;; :NOT-W also includes the case where the rex byte is absent.
              :REX :NOT-W
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:CMPXCHG16B))
          (ARG :OP1 '(M Q))
          'NIL
          '((:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMPTRLD"
          (OP :OP #xFC7
              :REG #x6
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9))
          (ARG :OP1 '(M Q))
          'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "VMCLEAR"
          (OP :OP #xFC7
              :REG #x6
              :MOD :MEM
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9))
          (ARG :OP1 '(M Q))
          'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "VMXON"
          (OP :OP #xFC7
              :REG #x6
              :MOD :MEM
              :PFX :F3
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9))
          (ARG :OP1 '(M Q))
          'NIL
          ;; BOZO Rob -- following GP only if executed outside VMX operation!
          '((:GP (GP-CPL-NOT-0))))
    (INST "VMPTRLD"
          (OP :OP #xFC7
              :REG #x7
              :MOD :MEM
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9))
          (ARG :OP1 '(M Q))
          'NIL
          '((:GP (GP-CPL-NOT-0))))
    (INST "RDRAND"
          (OP :OP #xFC7
              :REG #x6
              :MOD #x3
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:RDRAND))
          (ARG :OP1 '(R V))
          '(X86-RDRAND)
          '((:UD (UD-LOCK-USED)
                 (UD-REPS-USED))))
    ;; [Shilpi] RDRAND, with #x66 prefix, isn't listed in the Intel manuals (May
    ;; 2018 edition).  This is because all opcodes in this table other than RDRAND
    ;; throw an error if they're used with a SIMD prefix that's not listed as an
    ;; allowed mandatory prefix for that opcode.  RDRAND can be used with
    ;; :no-prefix and :66, but not :F2 or :F3 (see (ud-Reps-used) in :ud listing).
    (INST "RDRAND"
          (OP :OP #xFC7
              :REG #x6
              :MOD #x3
              :PFX :66
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:RDRAND))
          (ARG :OP1 '(R W))
          '(X86-RDRAND)
          '((:UD (UD-LOCK-USED)
                 (UD-REPS-USED))))
    (INST "RDSEED"
          (OP :OP #xFC7
              :REG #x7
              :PFX :NO-PREFIX
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:RDSEED))
          (ARG :OP1 '(R V))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-REPS-USED))))
    (INST "RDPID"
          (OP :OP #xFC7
              :REG #x7
              :PFX :F3
              :MODE :O64
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:RDPID))
          (ARG :OP1 '(R Q))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "RDPID"
          (OP :OP #xFC7
              :REG #x7
              :PFX :F3
              :MODE :I64
              :SUPERSCRIPTS '(:1A)
              :GROUP '(:GROUP-9)
              :FEAT '(:RDPID))
          (ARG :OP1 '(R D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFC8)
          (ARG :OP1 '(:RAX/EAX/R8/R8D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFC9)
          (ARG :OP1 '(:RCX/ECX/R9/R9D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCA)
          (ARG :OP1 '(:RDX/EDX/R10/R10D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCB)
          (ARG :OP1 '(:RBX/EBX/R11/R11D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCC)
          (ARG :OP1 '(:RSP/ESP/R12/R12D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCD)
          (ARG :OP1 '(:RBP/EBP/R13/R13D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCE)
          (ARG :OP1 '(:RSI/ESI/R14/R14D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "BSWAP" (OP :OP #xFCF)
          (ARG :OP1 '(:RDI/EDI/R15/R15D))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ADDSUBPD"
          (OP :OP #xFD0 :PFX :66 :FEAT '(:SSE3))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE3)))))
    (INST "ADDSUBPS"
          (OP :OP #xFD0 :PFX :F2 :FEAT '(:SSE3))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE3)))))
    (INST "VADDSUBPD"
          (OP :OP #xFD0
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDSUBPD"
          (OP :OP #xFD0
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PD)
               :OP2 '(H PD)
               :OP3 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDSUBPS"
          (OP :OP #xFD0
              :VEX '(:0F :NDS :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VADDSUBPS"
          (OP :OP #xFD0
              :VEX '(:0F :NDS :256 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V PS)
               :OP2 '(H PS)
               :OP3 '(W PS))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PSRLW"
          (OP :OP #xFD1
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLW"
          (OP :OP #xFD1 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSRLW"
          (OP :OP #xFD1
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRLW"
          (OP :OP #xFD1
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLW"
          (OP :OP #xFD1
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLW"
          (OP :OP #xFD1
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLW"
          (OP :OP #xFD1
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSRLD"
          (OP :OP #xFD2
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLD"
          (OP :OP #xFD2 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSRLD"
          (OP :OP #xFD2
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRLD"
          (OP :OP #xFD2
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLD"
          (OP :OP #xFD2
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLD"
          (OP :OP #xFD2
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLD"
          (OP :OP #xFD2
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSRLQ"
          (OP :OP #xFD3
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRLQ"
          (OP :OP #xFD3 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSRLQ"
          (OP :OP #xFD3
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRLQ"
          (OP :OP #xFD3
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLQ"
          (OP :OP #xFD3
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLQ"
          (OP :OP #xFD3
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLQ"
          (OP :OP #xFD3
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PADDQ"
          (OP :OP #xFD4
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "ADDQ"
          (OP :OP #xFD4 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDQ"
          (OP :OP #xFD4
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDQ"
          (OP :OP #xFD4
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDQ"
          (OP :OP #xFD4
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPADDQ"
          (OP :OP #xFD4
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPADDQ"
          (OP :OP #xFD4
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "PMULLW"
          (OP :OP #xFD5
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PMULLW"
          (OP :OP #xFD5 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMULLW"
          (OP :OP #xFD5
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULLW"
          (OP :OP #xFD5
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULLW"
          (OP :OP #xFD5
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULLW"
          (OP :OP #xFD5
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULLW"
          (OP :OP #xFD5
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "MOVQ"
          (OP :OP #xFD6 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(W Q) :OP2 '(V Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "MOVQ2DQ"
          (OP :OP #xFD6 :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V DQ) :OP2 '(N Q))
          'NIL
          '((:UD (EQUAL (CR0BITS->TS (CR0)) #x1)
                 (EQUAL (CR0BITS->EM (CR0)) #x1)
                 (EQUAL (CR4BITS->OSFXSR (CR4)) #x0)
                 (UD-LOCK-USED))))
    (INST "MOVDQ2Q"
          (OP :OP #xFD6 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(P Q) :OP2 '(U Q))
          'NIL
          '((:UD (EQUAL (CR0BITS->TS (CR0)) #x1)
                 (EQUAL (CR0BITS->EM (CR0)) #x1)
                 (EQUAL (CR4BITS->OSFXSR (CR4)) #x0)
                 (UD-LOCK-USED))))
    (INST "VMOVQ"
          (OP :OP #xFD6
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V Q) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMOVQ"
          (OP :OP #xFD6
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "PMOVMSKB"
          (OP :OP #xFD7
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(G D) :OP2 '(N Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-7 (:SSE)))))
    (INST "PMOVMSKB"
          (OP :OP #xFD7 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(G D) :OP2 '(U X))
          '(X86-PMOVMSKB-OP/EN-RM)
          '((:EX (CHK-EXC :TYPE-7 (:SSE2)))))
    (INST "VPMOVMSKB"
          (OP :OP #xFD7
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(G D) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX)))))
    (INST "VPMOVMSKB"
          (OP :OP #xFD7
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(G D) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "PSUBUSB"
          (OP :OP #xFD8
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBUSB"
          (OP :OP #xFD8 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBUSB"
          (OP :OP #xFD8
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBUSB"
          (OP :OP #xFD8
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBUSB"
          (OP :OP #xFD8
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSUBUSB"
          (OP :OP #xFD8
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSUBUSB"
          (OP :OP #xFD8
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512BW)))))
    (INST "PSUBUSW"
          (OP :OP #xFD9
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBUSW"
          (OP :OP #xFD9 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBUSW"
          (OP :OP #xFD9
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBUSW"
          (OP :OP #xFD9
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBUSW"
          (OP :OP #xFD9
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSUBUSW"
          (OP :OP #xFD9
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSUBUSW"
          (OP :OP #xFD9
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512BW)))))
    (INST "PMINUB"
          (OP :OP #xFDA
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PMINUB"
          (OP :OP #xFDA :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMINUB"
          (OP :OP #xFDA
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINUB"
          (OP :OP #xFDA
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINUB"
          (OP :OP #xFDA
              :EVEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINUB"
          (OP :OP #xFDA
              :EVEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINUB"
          (OP :OP #xFDA
              :EVEX '(:0F :NDS :512 :66)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PAND"
          (OP :OP #xFDB
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PAND"
          (OP :OP #xFDB :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x3))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPAND"
          (OP :OP #xFDB
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPAND"
          (OP :OP #xFDB
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPANDD"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPANDQ"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPANDD"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDD"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDQ"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDQ"
          (OP :OP #xFDB
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "PADDUSB"
          (OP :OP #xFDC
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDUSB"
          (OP :OP #xFDC :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDUSB"
          (OP :OP #xFDC
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDUSB"
          (OP :OP #xFDC
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDUSB"
          (OP :OP #xFDC
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDUSB"
          (OP :OP #xFDC
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDUSB"
          (OP :OP #xFDC
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PADDUSW"
          (OP :OP #xFDD
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDUSW"
          (OP :OP #xFDD :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDUSW"
          (OP :OP #xFDD
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDUSW"
          (OP :OP #xFDD
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDUSW"
          (OP :OP #xFDD
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDUSW"
          (OP :OP #xFDD
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDUSW"
          (OP :OP #xFDD
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMAXUB"
          (OP :OP #xFDE
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PMAXUB"
          (OP :OP #xFDE :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMAXUB"
          (OP :OP #xFDE
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXUB"
          (OP :OP #xFDE
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXUB"
          (OP :OP #xFDE
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXUB"
          (OP :OP #xFDE
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXUB"
          (OP :OP #xFDE
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PANDN"
          (OP :OP #xFDF
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PANDN"
          (OP :OP #xFDF :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #xD))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPANDN"
          (OP :OP #xFDF
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPANDN"
          (OP :OP #xFDF
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPANDND"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDND"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDND"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPANDNQ"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDNQ"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPANDNQ"
          (OP :OP #xFDF
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PAVGB"
          (OP :OP #xFE0
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PAVGB"
          (OP :OP #xFE0 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPAVGB"
          (OP :OP #xFE0
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPAVGB"
          (OP :OP #xFE0
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPAVGB"
          (OP :OP #xFE0
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPAVGB"
          (OP :OP #xFE0
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPAVGB"
          (OP :OP #xFE0
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PSRAW"
          (OP :OP #xFE1
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRAW"
          (OP :OP #xFE1 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSRAW"
          (OP :OP #xFE1
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRAW"
          (OP :OP #xFE1
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRAW"
          (OP :OP #xFE1
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRAW"
          (OP :OP #xFE1
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRAW"
          (OP :OP #xFE1
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSRAD"
          (OP :OP #xFE2
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSRAD"
          (OP :OP #xFE2 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSRAD"
          (OP :OP #xFE2
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSRAD"
          (OP :OP #xFE2
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRAD"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSRAD"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "VPSRAQ"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSRAQ"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSRAQ"
          (OP :OP #xFE2
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "PAVGW"
          (OP :OP #xFE3
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PAVGW"
          (OP :OP #xFE3 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPAVGW"
          (OP :OP #xFE3
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPAVGW"
          (OP :OP #xFE3
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPAVGW"
          (OP :OP #xFE3
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPAVGW"
          (OP :OP #xFE3
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPAVGW"
          (OP :OP #xFE3
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMULHUW"
          (OP :OP #xFE4
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PMULHUW"
          (OP :OP #xFE4 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMULHUW"
          (OP :OP #xFE4
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULHUW"
          (OP :OP #xFE4
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULHUW"
          (OP :OP #xFE4
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHUW"
          (OP :OP #xFE4
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHUW"
          (OP :OP #xFE4
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMULHW"
          (OP :OP #xFE5
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PMULHW"
          (OP :OP #xFE5 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMULHW"
          (OP :OP #xFE5
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULHW"
          (OP :OP #xFE5
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULHW"
          (OP :OP #xFE5
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHW"
          (OP :OP #xFE5
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHW"
          (OP :OP #xFE5
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "CVTTPD2DQ"
          (OP :OP #xFE6 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "CVTDQ2PD"
          (OP :OP #xFE6 :PFX :F3 :FEAT '(:SSE2))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE2)))))
    (INST "CVTPD2DQ"
          (OP :OP #xFE6 :PFX :F2 :FEAT '(:SSE2))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE2)))))
    (INST "VCVTDQ2PD"
          (OP :OP #xFE6
              :VEX '(:0F :128 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VCVTDQ2PD"
          (OP :OP #xFE6
              :VEX '(:0F :256 :F3 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VCVTPD2DQ"
          (OP :OP #xFE6
              :VEX '(:0F :128 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTPD2DQ"
          (OP :OP #xFE6
              :VEX '(:0F :256 :F2 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTTPD2DQ"
          (OP :OP #xFE6
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTTPD2DQ"
          (OP :OP #xFE6
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W PD))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VCVTDQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTDQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTDQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :128 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :256 :F2 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :512 :F2 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VCVTQQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTQQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VCVTQQ2PD"
          (OP :OP #xFE6
              :EVEX '(:0F :512 :F3 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VCVTTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VCVTTPD2DQ"
          (OP :OP #xFE6
              :EVEX '(:0F :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "MOVNTQ"
          (OP :OP #xFE7
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(M Q) :OP2 '(P Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVNTDQ"
          (OP :OP #xFE7 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(M X) :OP2 '(V X))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE2)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMOVNTDQ"
          (OP :OP #xFE7
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M X) :OP2 '(V X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTDQ"
          (OP :OP #xFE7
              :VEX '(:0F :256 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(M X) :OP2 '(V X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTDQ"
          (OP :OP #xFE7
              :EVEX '(:0F :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTDQ"
          (OP :OP #xFE7
              :EVEX '(:0F :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTDQ"
          (OP :OP #xFE7
              :EVEX '(:0F :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512F)))))
    (INST "PSUBSB"
          (OP :OP #xFE8
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBSB"
          (OP :OP #xFE8 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBSB"
          (OP :OP #xFE8
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBSB"
          (OP :OP #xFE8
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBSB"
          (OP :OP #xFE8
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBSB"
          (OP :OP #xFE8
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBSB"
          (OP :OP #xFE8
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PSUBSW"
          (OP :OP #xFE9
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBSW"
          (OP :OP #xFE9 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBSW"
          (OP :OP #xFE9
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBSW"
          (OP :OP #xFE9
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBSW"
          (OP :OP #xFE9
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBSW"
          (OP :OP #xFE9
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBSW"
          (OP :OP #xFE9
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMINSW"
          (OP :OP #xFEA
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE)))))
    (INST "PMINSW"
          (OP :OP #xFEA :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMINSW"
          (OP :OP #xFEA
              :VEX '(:0F :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINSW"
          (OP :OP #xFEA
              :VEX '(:0F :NDS :256 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINSW"
          (OP :OP #xFEA
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINSW"
          (OP :OP #xFEA
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINSW"
          (OP :OP #xFEA
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "POR"
          ;; Note: Table 22-7 does not list POR in the
          ;; "Applicable Instructions" section, but it does
          ;; list PXOR.  So this is a guess.
          (OP :OP #xFEB
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "POR"
          (OP :OP #xFEB :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x1))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPOR"
          (OP :OP #xFEB
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPOR"
          (OP :OP #xFEB
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPORD"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPORD"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPORD"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPORQ"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPORQ"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPORQ"
          (OP :OP #xFEB
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PADDSB"
          (OP :OP #xFEC
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDSB"
          (OP :OP #xFEC :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDSB"
          (OP :OP #xFEC
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDSB"
          (OP :OP #xFEC
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDSB"
          (OP :OP #xFEC
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDSB"
          (OP :OP #xFEC
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDSB"
          (OP :OP #xFEC
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PADDSW"
          (OP :OP #xFED
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDSW"
          (OP :OP #xFED :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDSW"
          (OP :OP #xFED
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDSW"
          (OP :OP #xFED
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDSW"
          (OP :OP #xFED
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDSW"
          (OP :OP #xFED
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDSW"
          (OP :OP #xFED
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMAXSW"
          (OP :OP #xFEE
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PMAXSW"
          (OP :OP #xFEE :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMAXSW"
          (OP :OP #xFEE
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXSW"
          (OP :OP #xFEE
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMAXSW"
          (OP :OP #xFEE
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXSW"
          (OP :OP #xFEE
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXSW"
          (OP :OP #xFEE
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PXOR"
          (OP :OP #xFEF
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PXOR"
          (OP :OP #xFEF :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          '(X86-ANDP?/ANDNP?/ORP?/XORP?/PAND/PANDN/POR/PXOR-OP/EN-RM
            (OPERATION . #x5))
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPXOR"
          (OP :OP #xFEF
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPXOR"
          (OP :OP #xFEF
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPXORD"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPXORD"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPXORD"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPXORQ"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPXORQ"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPXORQ"
          (OP :OP #xFEF
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "LDDQU"
          (OP :OP #xFF0 :PFX :F2 :FEAT '(:SSE3))
          (ARG :OP1 '(V X) :OP2 '(M X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE3)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VLDDQU"
          (OP :OP #xFF0
              :VEX '(:0F :128 :F2 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VLDDQU"
          (OP :OP #xFF0
              :VEX '(:0F :256 :F2 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PSLLW"
          (OP :OP #xFF1
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLW"
          (OP :OP #xFF1 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSLLW"
          (OP :OP #xFF1
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSLLW"
          (OP :OP #xFF1
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLW"
          (OP :OP #xFF1
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLW"
          (OP :OP #xFF1
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLW"
          (OP :OP #xFF1
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSLLD"
          (OP :OP #xFF2
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLD"
          (OP :OP #xFF2 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSLLD"
          (OP :OP #xFF2
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSLLD"
          (OP :OP #xFF2
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLD"
          (OP :OP #xFF2
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSLLD"
          (OP :OP #xFF2
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSLLD"
          (OP :OP #xFF2
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "PSLLQ"
          (OP :OP #xFF3
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSLLQ"
          (OP :OP #xFF3 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSLLQ"
          (OP :OP #xFF3
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSLLQ"
          (OP :OP #xFF3
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLQ"
          (OP :OP #xFF3
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSLLQ"
          (OP :OP #xFF3
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512F)))))
    (INST "VPSLLQ"
          (OP :OP #xFF3
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512F)))))
    (INST "PMULUDQ"
          (OP :OP #xFF4
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PMULUDQ"
          (OP :OP #xFF4 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMULUDQ"
          (OP :OP #xFF4
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULUDQ"
          (OP :OP #xFF4
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULUDQ"
          (OP :OP #xFF4
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULUDQ"
          (OP :OP #xFF4
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULUDQ"
          (OP :OP #xFF4
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMADDWD"
          (OP :OP #xFF5
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PMADDWD"
          (OP :OP #xFF5 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMADDWD"
          (OP :OP #xFF5
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMADDWD"
          (OP :OP #xFF5
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMADDWD"
          (OP :OP #xFF5
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMADDWD"
          (OP :OP #xFF5
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMADDWD"
          (OP :OP #xFF5
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PSADBW"
          (OP :OP #xFF6
              :PFX :NO-PREFIX
              :FEAT '(:SSE))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:SSE)))))
    (INST "PSADBW"
          (OP :OP #xFF6 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSADBW"
          (OP :OP #xFF6
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSADBW"
          (OP :OP #xFF6
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSADBW"
          (OP :OP #xFF6
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSADBW"
          (OP :OP #xFF6
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSADBW"
          (OP :OP #xFF6
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "MASKMOVQ"
          (OP :OP #xFF7
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(N Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-8 (:MMX)))))
    (INST "MASKMOVDQU"
          (OP :OP #xFF7 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V DQ) :OP2 '(U DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VMASKMOVDQU"
          (OP :OP #xFF7
              :VEX '(:0F :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(U DQ))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PSUBB"
          (OP :OP #xFF8
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBB"
          (OP :OP #xFF8 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBB"
          (OP :OP #xFF8
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBB"
          (OP :OP #xFF8
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBB"
          (OP :OP #xFF8
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBB"
          (OP :OP #xFF8
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBB"
          (OP :OP #xFF8
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PSUBW"
          (OP :OP #xFF9
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBW"
          (OP :OP #xFF9 :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBW"
          (OP :OP #xFF9
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBW"
          (OP :OP #xFF9
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBW"
          (OP :OP #xFF9
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBW"
          (OP :OP #xFF9
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSUBW"
          (OP :OP #xFF9
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PSUBD"
          (OP :OP #xFFA
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBD"
          (OP :OP #xFFA :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBD"
          (OP :OP #xFFA
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBD"
          (OP :OP #xFFA
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBD"
          (OP :OP #xFFA
              :EVEX '(:0F :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSUBD"
          (OP :OP #xFFA
              :EVEX '(:0F :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSUBD"
          (OP :OP #xFFA
              :EVEX '(:0F :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PSUBQ"
          (OP :OP #xFFB
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PSUBQ"
          (OP :OP #xFFB :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPSUBQ"
          (OP :OP #xFFB
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSUBQ"
          (OP :OP #xFFB
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSUBQ"
          (OP :OP #xFFB
              :EVEX '(:0F :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSUBQ"
          (OP :OP #xFFB
              :EVEX '(:0F :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSUBQ"
          (OP :OP #xFFB
              :EVEX '(:0F :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PADDB"
          (OP :OP #xFFC
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDB"
          (OP :OP #xFFC :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPADDB"
          (OP :OP #xFFC
              :VEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPADDB"
          (OP :OP #xFFC
              :VEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPADDB"
          (OP :OP #xFFC
              :EVEX '(:0F :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDB"
          (OP :OP #xFFC
              :EVEX '(:0F :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPADDB"
          (OP :OP #xFFC
              :EVEX '(:0F :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PADDW"
          (OP :OP #xFFD
              :PFX :NO-PREFIX
              :FEAT '(:MMX))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
    (INST "PADDW"
          (OP :OP #xFFD :PFX :66 :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       'NIL
       '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
 (INST "VPADDW"
       (OP :OP #xFFD
           :VEX '(:0F :NDS :128 :66 :WIG)
           :FEAT '(:AVX))
       (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
 (INST "VPADDW"
       (OP :OP #xFFD
           :VEX '(:0F :NDS :256 :66 :WIG)
           :FEAT '(:AVX2))
       (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
 (INST "VPADDW"
       (OP :OP #xFFD
           :EVEX '(:0F :NDS :128 :66 :WIG)
           :FEAT '(:AVX512VL :AVX512BW))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
 (INST "VPADDW"
       (OP :OP #xFFD
           :EVEX '(:0F :NDS :256 :66 :WIG)
           :FEAT '(:AVX512VL :AVX512BW))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
 (INST "VPADDW"
       (OP :OP #xFFD
           :EVEX '(:0F :NDS :512 :66 :WIG)
           :FEAT '(:AVX512BW))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
 (INST "PADDD"
       (OP :OP #xFFE
           :PFX :NO-PREFIX
           :FEAT '(:MMX))
       (ARG :OP1 '(P Q) :OP2 '(Q Q))
       'NIL
       '((:EX (CHK-EXC :TYPE-22-7 (:MMX)))))
 (INST "PADDD"
       (OP :OP #xFFE :PFX :66 :FEAT '(:SSE2))
       (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       'NIL
       '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
 (INST "VPADDD"
       (OP :OP #xFFE
           :VEX '(:0F :NDS :128 :66 :WIG)
           :FEAT '(:AVX))
       (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
 (INST "VPADDD"
       (OP :OP #xFFE
           :VEX '(:0F :NDS :256 :66 :WIG)
           :FEAT '(:AVX2))
       (ARG :OP1 '(V X)
            :OP2 '(H X)
            :OP3 '(W X))
       NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
 (INST "VPADDD"
       (OP :OP #xFFE
           :EVEX '(:0F :NDS :512 :66 :W0)
           :FEAT '(:AVX512F))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
 (INST "VPADDD"
       (OP :OP #xFFE
           :EVEX '(:0F :NDS :128 :66 :W0)
           :FEAT '(:AVX512VL :AVX512F))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
 (INST "VPADDD"
       (OP :OP #xFFE
           :EVEX '(:0F :NDS :256 :66 :W0)
           :FEAT '(:AVX512VL :AVX512F))
       NIL NIL
       '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))))

(defconst *pre-0F-38-three-byte-opcode-map*
  ;; BOZO Rob question -- should these be UD in 64-bit mode? or just ignored..
  '((INST "PSHUFB"
          (OP :OP #xF3800
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PSHUFB"
          (OP :OP #xF3800
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPSHUFB"
          (OP :OP #xF3800
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSHUFB"
          (OP :OP #xF3800
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSHUFB"
          (OP :OP #xF3800
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFB"
          (OP :OP #xF3800
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSHUFB"
          (OP :OP #xF3800
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PHADDW"
          (OP :OP #xF3801
              :PFX :NO-PREFIX
              :FEAT '(:SSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHADDW"
          (OP :OP #xF3801
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHADDW"
          (OP :OP #xF3801
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHADDW"
          (OP :OP #xF3801
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PHADDD"
          (OP :OP #xF3802
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHADDD"
          (OP :OP #xF3802
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHADDD"
          (OP :OP #xF3802
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHADDD"
          (OP :OP #xF3802
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PHADDSW"
          (OP :OP #xF3803
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHADDSW"
          (OP :OP #xF3803
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHADDSW"
          (OP :OP #xF3803
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHADDSW"
          (OP :OP #xF3803
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PMADDUBSW"
          (OP :OP #xF3804
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PMADDUBSW"
          (OP :OP #xF3804
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPMADDUBSW"
          (OP :OP #xF3804
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMADDUBSW"
          (OP :OP #xF3804
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMADDUBSW"
          (OP :OP #xF3804
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMADDUBSW"
          (OP :OP #xF3804
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMADDUBSW"
          (OP :OP #xF3804
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PHSUBW"
          (OP :OP #xF3805
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHSUBW"
          (OP :OP #xF3805
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHSUBW"
          (OP :OP #xF3805
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHSUBW"
          (OP :OP #xF3805
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PHSUBD"
          (OP :OP #xF3806
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHSUBD"
          (OP :OP #xF3806
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHSUBD"
          (OP :OP #xF3806
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHSUBD"
          (OP :OP #xF3806
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PHSUBSW"
          (OP :OP #xF3807
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PHSUBSW"
          (OP :OP #xF3807
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPHSUBSW"
          (OP :OP #xF3807
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPHSUBSW"
          (OP :OP #xF3807
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PSIGNB"
          (OP :OP #xF3808
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PSIGNB"
          (OP :OP #xF3808
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPSIGNB"
          (OP :OP #xF3808
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSIGNB"
          (OP :OP #xF3808
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PSIGNW"
          (OP :OP #xF3809
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PSIGNW"
          (OP :OP #xF3809
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPSIGNW"
          (OP :OP #xF3809
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSIGNW"
          (OP :OP #xF3809
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PSIGND"
          (OP :OP #xF380A
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PSIGND"
          (OP :OP #xF380A
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPSIGND"
          (OP :OP #xF380A
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPSIGND"
          (OP :OP #xF380A
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PMULHRSW"
          (OP :OP #xF380B
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PMULHRSW"
          (OP :OP #xF380B
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPMULHRSW"
          (OP :OP #xF380B
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULHRSW"
          (OP :OP #xF380B
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULHRSW"
          (OP :OP #xF380B
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHRSW"
          (OP :OP #xF380B
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMULHRSW"
          (OP :OP #xF380B
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPERMILPS"
          (OP :OP #xF380C
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPS"
          (OP :OP #xF380C
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPS"
          (OP :OP #xF380C
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPS"
          (OP :OP #xF380C
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPS"
          (OP :OP #xF380C
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF380D
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPD"
          (OP :OP #xF380D
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPD"
          (OP :OP #xF380D
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF380D
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF380D
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VTESTPS"
          (OP :OP #xF380E
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VTESTPS"
          (OP :OP #xF380E
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VTESTPD"
          (OP :OP #xF380F
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VTESTPD"
          (OP :OP #xF380F
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PBLENDVB"
          (OP :OP #xF3810
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMOVUSWB"
          (OP :OP #xF3810
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVUSWB"
          (OP :OP #xF3810
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVUSWB"
          (OP :OP #xF3810
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512BW)))))
    (INST "VPSRLVW"
          (OP :OP #xF3810
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLVW"
          (OP :OP #xF3810
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSRLVW"
          (OP :OP #xF3810
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPMOVUSDB"
          (OP :OP #xF3811
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSDB"
          (OP :OP #xF3811
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSDB"
          (OP :OP #xF3811
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPSRAVW"
          (OP :OP #xF3811
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSRAVW"
          (OP :OP #xF3811
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPSRAVW"
          (OP :OP #xF3811
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512BW)))))
    (INST "VPMOVUSQB"
          (OP :OP #xF3812
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQB"
          (OP :OP #xF3812
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQB"
          (OP :OP #xF3812
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPSLLVW"
          (OP :OP #xF3812
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLVW"
          (OP :OP #xF3812
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPSLLVW"
          (OP :OP #xF3812
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VCVTPH2PS"
          (OP :OP #xF3813
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:F16C :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-11 (:F16C :AVX)))))
    (INST "VCVTPH2PS"
          (OP :OP #xF3813
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:F16C :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-11 (:F16C :AVX)))))
    (INST "VPMOVUSDW"
          (OP :OP #xF3813
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSDW"
          (OP :OP #xF3813
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSDW"
          (OP :OP #xF3813
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VCVTPH2PS"
          (OP :OP #xF3813
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512VL :AVX512F)))))
    (INST "VCVTPH2PS"
          (OP :OP #xF3813
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512VL :AVX512F)))))
    (INST "VCVTPH2PS"
          (OP :OP #xF3813
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512F)))))
    (INST "BLENDVPS"
          (OP :OP #xF3814
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMOVUSQW"
          (OP :OP #xF3814
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQW"
          (OP :OP #xF3814
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQW"
          (OP :OP #xF3814
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPRORVD"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPRORVD"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPRORVD"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPRORVQ"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPRORVQ"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPRORVQ"
          (OP :OP #xF3814
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "BLENDVPD"
          (OP :OP #xF3815
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMOVUSQD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVUSQD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPROLVD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPROLVD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPROLVD"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPROLVQ"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPROLVQ"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPROLVQ"
          (OP :OP #xF3815
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPERMPS"
          (OP :OP #xF3816
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPERMPD"
          (OP :OP #xF3816
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMPD"
          (OP :OP #xF3816
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMPS"
          (OP :OP #xF3816
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMPS"
          (OP :OP #xF3816
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PTEST"
          (OP :OP #xF3817
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPTEST"
          (OP :OP #xF3817
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPTEST"
          (OP :OP #xF3817
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(W D))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(W D))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V X) :OP2 '(W D))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V X) :OP2 '(W D))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VBROADCASTSS"
          (OP :OP #xF3818
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VBROADCASTSD"
          (OP :OP #xF3819
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V QQ) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VBROADCASTSD"
          (OP :OP #xF3819
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V QQ) :OP2 '(W Q))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VBROADCASTF32X2"
          (OP :OP #xF3819
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512DQ)))))
    (INST "VBROADCASTF32X2"
          (OP :OP #xF3819
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VBROADCASTSD"
          (OP :OP #xF3819
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VBROADCASTSD"
          (OP :OP #xF3819
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VBROADCASTF128"
          (OP :OP #xF381A
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V QQ) :OP2 '(M DQ))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VBROADCASTF32X4"
          (OP :OP #xF381A
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VBROADCASTF32X4"
          (OP :OP #xF381A
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VBROADCASTF64X2"
          (OP :OP #xF381A
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512DQ)))))
    (INST "VBROADCASTF64X2"
          (OP :OP #xF381A
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VBROADCASTF32X8"
          (OP :OP #xF381B
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VBROADCASTF64X4"
          (OP :OP #xF381B
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "PABSB"
          (OP :OP #xF381C
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PABSB"
          (OP :OP #xF381C
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPABSB"
          (OP :OP #xF381C
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPABSB"
          (OP :OP #xF381C
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPABSB"
          (OP :OP #xF381C
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPABSB"
          (OP :OP #xF381C
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPABSB"
          (OP :OP #xF381C
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PABSW"
          (OP :OP #xF381D
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PABSW"
          (OP :OP #xF381D
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPABSW"
          (OP :OP #xF381D
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPABSW"
          (OP :OP #xF381D
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPABSW"
          (OP :OP #xF381D
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPABSW"
          (OP :OP #xF381D
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPABSW"
          (OP :OP #xF381D
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PABSD"
          (OP :OP #xF381E
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q) :OP2 '(Q Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PABSD"
          (OP :OP #xF381E
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X) :OP2 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPABSD"
          (OP :OP #xF381E
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPABSD"
          (OP :OP #xF381E
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPABSD"
          (OP :OP #xF381E
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPABSD"
          (OP :OP #xF381E
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPABSD"
          (OP :OP #xF381E
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPABSQ"
          (OP :OP #xF381F
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPABSQ"
          (OP :OP #xF381F
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPABSQ"
          (OP :OP #xF381F
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    ;; BOZO Rob -- do the following have UD?
    (INST "PMOVSXBW"
          (OP :OP #xF3820 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVSXBW"
          (OP :OP #xF3820 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSXBW"
          (OP :OP #xF3820
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXBW"
          (OP :OP #xF3820
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSWB"
          (OP :OP #xF3820
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVSWB"
          (OP :OP #xF3820
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVSWB"
          (OP :OP #xF3820
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512BW)))))
    (INST "VPMOVSXBW"
          (OP :OP #xF3820
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512BW)))))
    (INST "VPMOVSXBW"
          (OP :OP #xF3820
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512BW)))))
    (INST "VPMOVSXBW"
          (OP :OP #xF3820
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512BW)))))
    (INST "PMOVSXBD"
          (OP :OP #xF3821 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M D))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVSXBD"
          (OP :OP #xF3821 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSXBD"
          (OP :OP #xF3821
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXBD"
          (OP :OP #xF3821
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSDB"
          (OP :OP #xF3821
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSDB"
          (OP :OP #xF3821
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSDB"
          (OP :OP #xF3821
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVSXBD"
          (OP :OP #xF3821
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXBD"
          (OP :OP #xF3821
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXBD"
          (OP :OP #xF3821
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVSXBQ"
          (OP :OP #xF3822 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M W))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVSXBQ"
          (OP :OP #xF3822 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSXBQ"
          (OP :OP #xF3822
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXBQ"
          (OP :OP #xF3822
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSQB"
          (OP :OP #xF3822
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQB"
          (OP :OP #xF3822
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQB"
          (OP :OP #xF3822
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVSXBQ"
          (OP :OP #xF3822
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXBQ"
          (OP :OP #xF3822
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXBQ"
          (OP :OP #xF3822
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVSXWD"
          (OP :OP #xF3823 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVSXWD"
          (OP :OP #xF3823 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSXWD"
          (OP :OP #xF3823
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXWD"
          (OP :OP #xF3823
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSDW"
          (OP :OP #xF3823
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSDW"
          (OP :OP #xF3823
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSDW"
          (OP :OP #xF3823
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVSXWD"
          (OP :OP #xF3823
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXWD"
          (OP :OP #xF3823
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXWD"
          (OP :OP #xF3823
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVSXWQ"
          (OP :OP #xF3824 :MOD :MEM :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(M D))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "PMOVSXWQ"
          (OP :OP #xF3824 :MOD #x3 :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VPMOVSXWQ"
          (OP :OP #xF3824
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXWQ"
          (OP :OP #xF3824
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSQW"
          (OP :OP #xF3824
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQW"
          (OP :OP #xF3824
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQW"
          (OP :OP #xF3824
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVSXWQ"
          (OP :OP #xF3824
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXWQ"
          (OP :OP #xF3824
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXWQ"
          (OP :OP #xF3824
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
   (INST "PMOVSXDQ"
          (OP :OP #xF3825 :MOD :MEM :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(M D))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "PMOVSXDQ"
          (OP :OP #xF3825 :MOD #x3 :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VPMOVSXDQ"
          (OP :OP #xF3825
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVSXDQ"
          (OP :OP #xF3825
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVSQD"
          (OP :OP #xF3825
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQD"
          (OP :OP #xF3825
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSQD"
          (OP :OP #xF3825
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVSXDQ"
          (OP :OP #xF3825
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXDQ"
          (OP :OP #xF3825
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVSXDQ"
          (OP :OP #xF3825
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "VPTESTMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPTESTMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPTESTNMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTNMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTNMB"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :512 :F3 :W0)
              :FEAT '(:AVX512F :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F :AVX512BW)))))
    (INST "VPTESTNMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTNMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPTESTNMW"
          (OP :OP #xF3826
              :EVEX '(:0F38 :NDS :512 :F3 :W1)
              :FEAT '(:AVX512F :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F :AVX512BW)))))
    (INST "VPTESTMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPTESTMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPTESTNMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTNMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTNMD"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPTESTNMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTNMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTESTNMQ"
          (OP :OP #xF3827
              :EVEX '(:0F38 :NDS :512 :F3 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMULDQ"
          (OP :OP #xF3828
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMULDQ"
          (OP :OP #xF3828
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULDQ"
          (OP :OP #xF3828
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMOVM2B"
          (OP :OP #xF3828
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVM2B"
          (OP :OP #xF3828
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVM2B"
          (OP :OP #xF3828
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512BW)))))
    (INST "VPMOVM2W"
          (OP :OP #xF3828
              :EVEX '(:0F38 :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVM2W"
          (OP :OP #xF3828
              :EVEX '(:0F38 :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVM2W"
          (OP :OP #xF3828
              :EVEX '(:0F38 :512 :F3 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512BW)))))
    (INST "VPMULDQ"
          (OP :OP #xF3828
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULDQ"
          (OP :OP #xF3828
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULDQ"
          (OP :OP #xF3828
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PCMPEQQ"
          (OP :OP #xF3829
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPCMPEQQ"
          (OP :OP #xF3829
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPEQQ"
          (OP :OP #xF3829
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPEQQ"
          (OP :OP #xF3829
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPEQQ"
          (OP :OP #xF3829
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPEQQ"
          (OP :OP #xF3829
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMOVB2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVB2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVB2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512BW)))))
    (INST "VPMOVW2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVW2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512BW)))))
    (INST "VPMOVW2M"
          (OP :OP #xF3829
              :EVEX '(:0F38 :512 :F3 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512BW)))))
    (INST "MOVNTDQA"
          (OP :OP #xF382A
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X) :OP2 '(M X))
          'NIL
          '((:EX (CHK-EXC :TYPE-1 (:SSE4.1)))
            (:UD (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "VMOVNTDQA"
          (OP :OP #xF382A
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX)))))
    (INST "VMOVNTDQA"
          (OP :OP #xF382A
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X) :OP2 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-1 (:AVX2)))))
    (INST "VMOVNTDQA"
          (OP :OP #xF382A
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTDQA"
          (OP :OP #xF382A
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512VL :AVX512F)))))
    (INST "VMOVNTDQA"
          (OP :OP #xF382A
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E1NF (:AVX512F)))))
    (INST "VPBROADCASTMB2Q"
          (OP :OP #xF382A
              :EVEX '(:0F38 :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512CD)))))
    (INST "VPBROADCASTMB2Q"
          (OP :OP #xF382A
              :EVEX '(:0F38 :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512CD)))))
    (INST "VPBROADCASTMB2Q"
          (OP :OP #xF382A
              :EVEX '(:0F38 :512 :F3 :W1)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512CD)))))
    (INST "PACKUSDW"
          (OP :OP #xF382B
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPACKUSDW"
          (OP :OP #xF382B
              :VEX '(:0F38 :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPACKUSDW"
          (OP :OP #xF382B
              :VEX '(:0F38 :NDS :256 :66)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPACKUSDW"
          (OP :OP #xF382B
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512BW)))))
    (INST "VPACKUSDW"
          (OP :OP #xF382B
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512BW)))))
    (INST "VPACKUSDW"
          (OP :OP #xF382B
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512BW)))))
    (INST "VMASKMOVPS"
          (OP :OP #xF382C
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VMASKMOVPS"
          (OP :OP #xF382C
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VSCALEFPD"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSCALEFPD"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSCALEFPD"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VSCALEFPS"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSCALEFPS"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VSCALEFPS"
          (OP :OP #xF382C
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VMASKMOVPD"
          (OP :OP #xF382D
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VMASKMOVPD"
          (OP :OP #xF382D
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VSCALEFSD"
          (OP :OP #xF382D
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VSCALEFSS"
          (OP :OP #xF382D
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VMASKMOVPS"
          (OP :OP #xF382E
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VMASKMOVPS"
          (OP :OP #xF382E
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VMASKMOVPD"
          (OP :OP #xF382F
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VMASKMOVPD"
          (OP :OP #xF382F
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "PMOVZXBW"
          (OP :OP #xF3830 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXBW"
          (OP :OP #xF3830 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXBW"
          (OP :OP #xF3830
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVZXBW"
          (OP :OP #xF3830
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVWB"
          (OP :OP #xF3830
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVWB"
          (OP :OP #xF3830
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512BW)))))
    (INST "VPMOVWB"
          (OP :OP #xF3830
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512BW)))))
    (INST "VPMOVZXBW"
          (OP :OP #xF3830
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512BW)))))
    (INST "VPMOVZXBW"
          (OP :OP #xF3830
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512BW)))))
    (INST "VPMOVZXBW"
          (OP :OP #xF3830
              :EVEX '(:0F38 :128 :66)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512BW)))))
    (INST "PMOVZXBD"
          (OP :OP #xF3831 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M D))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXBD"
          (OP :OP #xF3831 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXBD"
          (OP :OP #xF3831
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVZXBD"
          (OP :OP #xF3831
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVDB"
          (OP :OP #xF3831
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVDB"
          (OP :OP #xF3831
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVDB"
          (OP :OP #xF3831
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVZXBD"
          (OP :OP #xF3831
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXBD"
          (OP :OP #xF3831
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXBD"
          (OP :OP #xF3831
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVZXBQ"
          (OP :OP #xF3832 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M W))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXBQ"
          (OP :OP #xF3832 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXBQ"
          (OP :OP #xF3832
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVZXBQ"
          (OP :OP #xF3832
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVQB"
          (OP :OP #xF3832
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQB"
          (OP :OP #xF3832
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQB"
          (OP :OP #xF3832
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVZXBQ"
          (OP :OP #xF3832
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXBQ"
          (OP :OP #xF3832
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXBQ"
          (OP :OP #xF3832
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVZXWD"
          (OP :OP #xF3833 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXWD"
          (OP :OP #xF3833 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXWD"
          (OP :OP #xF3833
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVZXWD"
          (OP :OP #xF3833
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVDW"
          (OP :OP #xF3833
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVDW"
          (OP :OP #xF3833
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVDW"
          (OP :OP #xF3833
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVZXWD"
          (OP :OP #xF3833
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXWD"
          (OP :OP #xF3833
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXWD"
          (OP :OP #xF3833
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVZXWQ"
          (OP :OP #xF3834 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M D))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXWQ"
          (OP :OP #xF3834 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXWQ"
          (OP :OP #xF3834
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPMOVZXWQ"
          (OP :OP #xF3834
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVQW"
          (OP :OP #xF3834
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQW"
          (OP :OP #xF3834
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQW"
          (OP :OP #xF3834
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVZXWQ"
          (OP :OP #xF3834
              :EVEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXWQ"
          (OP :OP #xF3834
              :EVEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXWQ"
          (OP :OP #xF3834
              :EVEX '(:0F38 :512 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "PMOVZXDQ"
          (OP :OP #xF3835 :MOD :MEM :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(M Q))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PMOVZXDQ"
          (OP :OP #xF3835 :MOD #x3 :PFX :66)
          (ARG :OP1 '(V X) :OP2 '(U X))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVZXDQ"
          (OP :OP #xF3835
              :VEX '(:0F38 :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(U X))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPMOVQD"
          (OP :OP #xF3835
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQD"
          (OP :OP #xF3835
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPMOVQD"
          (OP :OP #xF3835
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPMOVZXDQ"
          (OP :OP #xF3835
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXDQ"
          (OP :OP #xF3835
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512VL :AVX512F)))))
    (INST "VPMOVZXDQ"
          (OP :OP #xF3835
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E5 (:AVX512F)))))
    (INST "VPERMD"
          (OP :OP #xF3836
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPERMD"
          (OP :OP #xF3836
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMD"
          (OP :OP #xF3836
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMQ"
          (OP :OP #xF3836
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMQ"
          (OP :OP #xF3836
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PCMPGTQ"
          (OP :OP #xF3837
              :PFX :66
              :FEAT '(:SSE4.2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.2)))))
    (INST "VPCMPGTQ"
          (OP :OP #xF3837
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPCMPGTQ"
          (OP :OP #xF3837
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPCMPGTQ"
          (OP :OP #xF3837
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPGTQ"
          (OP :OP #xF3837
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPGTQ"
          (OP :OP #xF3837
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMINSB"
          (OP :OP #xF3838
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMINSB"
          (OP :OP #xF3838
              :VEX '(:0F38 :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINSB"
          (OP :OP #xF3838
              :VEX '(:0F38 :NDS :256 :66)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMINSB"
          (OP :OP #xF3838
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINSB"
          (OP :OP #xF3838
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMINSB"
          (OP :OP #xF3838
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPMOVM2D"
          (OP :OP #xF3838
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVM2D"
          (OP :OP #xF3838
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVM2D"
          (OP :OP #xF3838
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512DQ)))))
    (INST "VPMOVM2Q"
          (OP :OP #xF3838
              :EVEX '(:0F38 :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVM2Q"
          (OP :OP #xF3838
              :EVEX '(:0F38 :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVM2Q"
          (OP :OP #xF3838
              :EVEX '(:0F38 :512 :F3 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512DQ)))))
    (INST "PMINSD"
          (OP :OP #xF3839
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMINSD"
          (OP :OP #xF3839
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINSD"
          (OP :OP #xF3839
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMINSD"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINSD"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINSD"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMINSQ"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINSQ"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINSQ"
          (OP :OP #xF3839
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMOVD2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVD2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVD2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512DQ)))))
    (INST "VPMOVQ2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :128 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVQ2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :256 :F3 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512VL :AVX512DQ)))))
    (INST "VPMOVQ2M"
          (OP :OP #xF3839
              :EVEX '(:0F38 :512 :F3 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E7NM (:AVX512DQ)))))
    (INST "PMINUW"
          (OP :OP #xF383A
              :PFX :66
              :FEAT '(:SSE2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE2)))))
    (INST "VPMINUW"
          (OP :OP #xF383A
              :VEX '(:0F38 :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINUW"
          (OP :OP #xF383A
              :VEX '(:0F38 :NDS :256 :66)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPBROADCASTMW2D"
          (OP :OP #xF383A
              :EVEX '(:0F38 :128 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512CD)))))
    (INST "VPBROADCASTMW2D"
          (OP :OP #xF383A
              :EVEX '(:0F38 :256 :F3 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512CD)))))
    (INST "VPBROADCASTMW2D"
          (OP :OP #xF383A
              :EVEX '(:0F38 :512 :F3 :W0)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512CD)))))
    (INST "VPMINUW"
          (OP :OP #xF383A
              :EVEX '(:0F38 :NDS :128 :66)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512CD)))))
    (INST "VPMINUW"
          (OP :OP #xF383A
              :EVEX '(:0F38 :NDS :256 :66)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512CD)))))
    (INST "VPMINUW"
          (OP :OP #xF383A
              :EVEX '(:0F38 :NDS :512 :66)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512CD)))))
    (INST "PMINUD"
          (OP :OP #xF383B
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMINUD"
          (OP :OP #xF383B
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMINUD"
          (OP :OP #xF383B
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMINUD"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINUD"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINUD"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMINUQ"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINUQ"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMINUQ"
          (OP :OP #xF383B
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMAXSB"
          (OP :OP #xF383C
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMAXSB"
          (OP :OP #xF383C
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXSB"
          (OP :OP #xF383C
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMAXSB"
          (OP :OP #xF383C
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXSB"
          (OP :OP #xF383C
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXSB"
          (OP :OP #xF383C
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMAXSD"
          (OP :OP #xF383D
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMAXSD"
          (OP :OP #xF383D
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXSD"
          (OP :OP #xF383D
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMAXSD"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXSD"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXSD"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMAXSQ"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXSQ"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXSQ"
          (OP :OP #xF383D
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMAXUW"
          (OP :OP #xF383E
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMAXUW"
          (OP :OP #xF383E
              :VEX '(:0F38 :NDS :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXUW"
          (OP :OP #xF383E
              :VEX '(:0F38 :NDS :256 :66)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMAXUW"
          (OP :OP #xF383E
              :EVEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXUW"
          (OP :OP #xF383E
              :EVEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPMAXUW"
          (OP :OP #xF383E
              :EVEX '(:0F38 :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "PMAXUD"
          (OP :OP #xF383F
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMAXUD"
          (OP :OP #xF383F
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMAXUD"
          (OP :OP #xF383F
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMAXUD"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXUD"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXUD"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMAXUQ"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXUQ"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMAXUQ"
          (OP :OP #xF383F
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "PMULLD"
          (OP :OP #xF3840
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPMULLD"
          (OP :OP #xF3840
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPMULLD"
          (OP :OP #xF3840
              :VEX '(:0F38 :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPMULLD"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULLD"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPMULLD"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPMULLQ"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VPMULLQ"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VPMULLQ"
          (OP :OP #xF3840
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "PHMINPOSUW"
          (OP :OP #xF3841
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPHMINPOSUW"
          (OP :OP #xF3841
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VGETEXPPD"
          (OP :OP #xF3842
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETEXPPD"
          (OP :OP #xF3842
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETEXPPD"
          (OP :OP #xF3842
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VGETEXPPS"
          (OP :OP #xF3842
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETEXPPS"
          (OP :OP #xF3842
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETEXPPS"
          (OP :OP #xF3842
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VGETEXPSD"
          (OP :OP #xF3843
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VGETEXPSS"
          (OP :OP #xF3843
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VPLZCNTD"
          (OP :OP #xF3844
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPLZCNTD"
          (OP :OP #xF3844
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPLZCNTD"
          (OP :OP #xF3844
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512CD)))))
    (INST "VPLZCNTQ"
          (OP :OP #xF3844
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPLZCNTQ"
          (OP :OP #xF3844
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPLZCNTQ"
          (OP :OP #xF3844
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512CD)))))
    (INST "VPSRLVD"
          (OP :OP #xF3845
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLVD"
          (OP :OP #xF3845
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLVQ"
          (OP :OP #xF3845
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLVQ"
          (OP :OP #xF3845
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRLVD"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRLVD"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRLVD"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPSRLVQ"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRLVQ"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRLVQ"
          (OP :OP #xF3845
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPSRAVD"
          (OP :OP #xF3846
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRAVD"
          (OP :OP #xF3846
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSRAVD"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRAVD"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRAVD"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPSRAVQ"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRAVQ"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSRAVQ"
          (OP :OP #xF3846
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPSLLVD"
          (OP :OP #xF3847
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLVD"
          (OP :OP #xF3847
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLVQ"
          (OP :OP #xF3847
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLVQ"
          (OP :OP #xF3847
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPSLLVD"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSLLVD"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSLLVD"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPSLLVQ"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSLLVQ"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPSLLVQ"
          (OP :OP #xF3847
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VRCP14PD"
          (OP :OP #xF384C
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRCP14PD"
          (OP :OP #xF384C
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRCP14PD"
          (OP :OP #xF384C
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VRCP14PS"
          (OP :OP #xF384C
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRCP14PS"
          (OP :OP #xF384C
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRCP14PS"
          (OP :OP #xF384C
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VRCP14SD"
          (OP :OP #xF384D
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VRCP14SS"
          (OP :OP #xF384D
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VRSQRT14PD"
          (OP :OP #xF384E
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRSQRT14PD"
          (OP :OP #xF384E
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRSQRT14PD"
          (OP :OP #xF384E
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VRSQRT14PS"
          (OP :OP #xF384E
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRSQRT14PS"
          (OP :OP #xF384E
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VRSQRT14PS"
          (OP :OP #xF384E
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VRSQRT14SD"
          (OP :OP #xF384F
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VRSQRT14SS"
          (OP :OP #xF384F
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E10 (:AVX512F)))))
    (INST "VP4DPWSSD"
          (OP :OP #xF3852
              :EVEX '(:0F38 :DDS :512 :F2 :W0)
              :FEAT '(:AVX512_4VNNIW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_4VNNIW)))))
    (INST "VP4DPWSSDS"
          (OP :OP #xF3853
              :EVEX '(:0F38 :DDS :512 :F2 :W0)
              :FEAT '(:AVX512_4VNNIW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_4VNNIW)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF3858
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF3858
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF3858
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF3858
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF3858
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF3859
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF3859
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VBROADCASTI32x2"
          (OP :OP #xF3859
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512DQ)))))
    (INST "VBROADCASTI32x2"
          (OP :OP #xF3859
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512DQ)))))
    (INST "VBROADCASTI32x2"
          (OP :OP #xF3859
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF3859
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF3859
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF3859
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VBROADCASTI128"
          (OP :OP #xF385A
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V QQ) :OP2 '(M DQ))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VBROADCASTI32X4"
          (OP :OP #xF385A
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VBROADCASTI32X4"
          (OP :OP #xF385A
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VBROADCASTI64X2"
          (OP :OP #xF385A
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512DQ)))))
    (INST "VBROADCASTI64X2"
          (OP :OP #xF385A
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VBROADCASTI32X8"
          (OP :OP #xF385B
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VBROADCASTI64X4"
          (OP :OP #xF385B
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPBLENDMD"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPBLENDMD"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPBLENDMD"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPBLENDMQ"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPBLENDMQ"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPBLENDMQ"
          (OP :OP #xF3864
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VBLENDMPD"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VBLENDMPD"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VBLENDMPD"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VBLENDMPS"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VBLENDMPS"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VBLENDMPS"
          (OP :OP #xF3865
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPBLENDMB"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPBLENDMB"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPBLENDMB"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512BW)))))
    (INST "VPBLENDMW"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPBLENDMW"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512BW)))))
    (INST "VPBLENDMW"
          (OP :OP #xF3866
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512BW)))))
    (INST "VPERMI2B"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMI2B"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMI2B"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512_VBMI)))))
    (INST "VPERMI2W"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMI2W"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMI2W"
          (OP :OP #xF3875
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPERMI2D"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2D"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2D"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMI2Q"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2Q"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2Q"
          (OP :OP #xF3876
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMI2PD"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2PD"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2PD"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMI2PS"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2PS"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMI2PS"
          (OP :OP #xF3877
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF3878
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF3878
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF3878
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF3878
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF3878
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF3879
              :VEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF3879
              :VEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X) :OP2 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-7 (:AVX2)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF3879
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF3879
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF3879
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512BW)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF387A
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF387A
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTB"
          (OP :OP #xF387A
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF387B
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF387B
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512BW)))))
    (INST "VPBROADCASTW"
          (OP :OP #xF387B
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512BW)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF387C
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF387C
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTD"
          (OP :OP #xF387C
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF387C
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF387C
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512VL :AVX512F)))))
    (INST "VPBROADCASTQ"
          (OP :OP #xF387C
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512F)))))
    (INST "VPERMT2B"
          (OP :OP #xF387D
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMT2B"
          (OP :OP #xF387D
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMT2B"
          (OP :OP #xF387D
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512_VBMI)))))
    (INST "VPERMT2W"
          (OP :OP #xF387D
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMT2W"
          (OP :OP #xF387D
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMT2W"
          (OP :OP #xF387D
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPERMT2D"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2D"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2D"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMT2Q"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2Q"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2Q"
          (OP :OP #xF387E
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMT2PD"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2PD"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2PD"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMT2PS"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2PS"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMT2PS"
          (OP :OP #xF387F
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "INVEPT" (OP :OP #xF3880 :PFX :66)
          (ARG :OP1 '(G Y) :OP2 '(M DQ))
          'NIL
          '((:UD (UD-NOT-IN-PROT-OR-64-MODE)
                 (UD-NOT-IN-VMX-OPERATION)
                 (UD-INVEPT-NOT-SUPPORTED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))
            (:GP (GP-CPL-NOT-0))))
    (INST "INVVPID" (OP :OP #xF3881 :PFX :66)
          (ARG :OP1 '(G Y) :OP2 '(M DQ))
          'NIL
          '((:UD (UD-NOT-IN-PROT-OR-64-MODE)
                 (UD-NOT-IN-VMX-OPERATION)
                 (UD-INVVPID-NOT-SUPPORTED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))
            (:GP (GP-CPL-NOT-0))))
    (INST "INVPCID" (OP :OP #xF3882 :PFX :66)
          (ARG :OP1 '(G Y) :OP2 '(M DQ))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-INVPCID-NOT-SUPPORTED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))
            (:GP (GP-CPL-NOT-0))))
    (INST "VPMULTISHIFTQB"
          (OP :OP #xF3883
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512_VBMI :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512_VBMI :AVX512VL)))))
    (INST "VPMULTISHIFTQB"
          (OP :OP #xF3883
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512_VBMI :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512_VBMI :AVX512VL)))))
    (INST "VPMULTISHIFTQB"
          (OP :OP #xF3883
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512_VBMI)))))
    (INST "VEXPANDPD"
          (OP :OP #xF3888
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VEXPANDPD"
          (OP :OP #xF3888
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VEXPANDPD"
          (OP :OP #xF3888
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VEXPANDPS"
          (OP :OP #xF3888
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VEXPANDPS"
          (OP :OP #xF3888
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VEXPANDPS"
          (OP :OP #xF3888
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VPEXPANDD"
          (OP :OP #xF3889
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPEXPANDD"
          (OP :OP #xF3889
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPEXPANDD"
          (OP :OP #xF3889
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VPEXPANDQ"
          (OP :OP #xF3889
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPEXPANDQ"
          (OP :OP #xF3889
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPEXPANDQ"
          (OP :OP #xF3889
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VCOMPRESSPD"
          (OP :OP #xF388A
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VCOMPRESSPD"
          (OP :OP #xF388A
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VCOMPRESSPD"
          (OP :OP #xF388A
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VCOMPRESSPS"
          (OP :OP #xF388A
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VCOMPRESSPS"
          (OP :OP #xF388A
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VCOMPRESSPS"
          (OP :OP #xF388A
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VPCOMPRESSD"
          (OP :OP #xF388B
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPCOMPRESSD"
          (OP :OP #xF388B
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPCOMPRESSD"
          (OP :OP #xF388B
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VPCOMPRESSQ"
          (OP :OP #xF388B
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPCOMPRESSQ"
          (OP :OP #xF388B
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512F)))))
    (INST "VPCOMPRESSQ"
          (OP :OP #xF388B
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512F)))))
    (INST "VPMASKMOVD"
          (OP :OP #xF388C
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVD"
          (OP :OP #xF388C
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVQ"
          (OP :OP #xF388C
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVQ"
          (OP :OP #xF388C
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPERMB"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMB"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512_VBMI)))))
    (INST "VPERMB"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512_VBMI))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512_VBMI)))))
    (INST "VPERMW"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMW"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPERMW"
          (OP :OP #xF388D
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VPMASKMOVD"
          (OP :OP #xF388E
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVD"
          (OP :OP #xF388E
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVQ"
          (OP :OP #xF388E
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPMASKMOVQ"
          (OP :OP #xF388E
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX2)
              :MOD :MEM)
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(M X))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VPGATHERDD"
          (OP :OP #xF3890
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERDD"
          (OP :OP #xF3890
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERDQ"
          (OP :OP #xF3890
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERDQ"
          (OP :OP #xF3890
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERDD"
          (OP :OP #xF3890
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERDD"
          (OP :OP #xF3890
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERDD"
          (OP :OP #xF3890
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPGATHERDQ"
          (OP :OP #xF3890
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERDQ"
          (OP :OP #xF3890
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERDQ"
          (OP :OP #xF3890
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPGATHERQD"
          (OP :OP #xF3891
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERQD"
          (OP :OP #xF3891
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERQQ"
          (OP :OP #xF3891
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERQQ"
          (OP :OP #xF3891
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VPGATHERQD"
          (OP :OP #xF3891
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERQD"
          (OP :OP #xF3891
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERQD"
          (OP :OP #xF3891
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPGATHERQQ"
          (OP :OP #xF3891
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERQQ"
          (OP :OP #xF3891
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPGATHERQQ"
          (OP :OP #xF3891
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VGATHERDPD"
          (OP :OP #xF3892
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERDPD"
          (OP :OP #xF3892
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERDPS"
          (OP :OP #xF3892
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERDPS"
          (OP :OP #xF3892
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERDPD"
          (OP :OP #xF3892
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERDPD"
          (OP :OP #xF3892
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERDPD"
          (OP :OP #xF3892
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VGATHERDPS"
          (OP :OP #xF3892
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERDPS"
          (OP :OP #xF3892
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERDPS"
          (OP :OP #xF3892
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VGATHERQPD"
          (OP :OP #xF3893
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERQPD"
          (OP :OP #xF3893
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERQPS"
          (OP :OP #xF3893
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERQPS"
          (OP :OP #xF3893
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-12 (:AVX2)))))
    (INST "VGATHERQPD"
          (OP :OP #xF3893
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERQPD"
          (OP :OP #xF3893
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERQPD"
          (OP :OP #xF3893
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VGATHERQPS"
          (OP :OP #xF3893
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERQPS"
          (OP :OP #xF3893
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VGATHERQPS"
          (OP :OP #xF3893
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VFMADDSUB132PD"
          (OP :OP #xF3896
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB132PD"
          (OP :OP #xF3896
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB132PS"
          (OP :OP #xF3896
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB132PS"
          (OP :OP #xF3896
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB132PD"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB132PD"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB132PD"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADDSUB132PS"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB132PS"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB132PS"
          (OP :OP #xF3896
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD132PD"
          (OP :OP #xF3897
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD132PD"
          (OP :OP #xF3897
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD132PS"
          (OP :OP #xF3897
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD132PS"
          (OP :OP #xF3897
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD132PD"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD132PD"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD132PD"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD132PS"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD132PS"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD132PS"
          (OP :OP #xF3897
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD132PD"
          (OP :OP #xF3898
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132PD"
          (OP :OP #xF3898
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132PS"
          (OP :OP #xF3898
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132PS"
          (OP :OP #xF3898
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132PD"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD132PD"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD132PD"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD132PS"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD132PS"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD132PS"
          (OP :OP #xF3898
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD132SD"
          (OP :OP #xF3899
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132SS"
          (OP :OP #xF3899
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD132SD"
          (OP :OP #xF3899
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMADD132SS"
          (OP :OP #xF3899
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB132PD"
          (OP :OP #xF389A
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB132PD"
          (OP :OP #xF389A
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB132PS"
          (OP :OP #xF389A
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB132PS"
          (OP :OP #xF389A
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "V4FMADDPS"
          (OP :OP #xF389A
              :EVEX '(:0F38 :DDS :512 :F2 :W0)
              :FEAT '(:AVX512_4FMAPS))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512_4FMAPS)))))
    (INST "VFMSUB132PD"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB132PD"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB132PD"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB132PS"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB132PS"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB132PS"
          (OP :OP #xF389A
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB132SD"
          (OP :OP #xF389B
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB132SS"
          (OP :OP #xF389B
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "V4FMADDSS"
          (OP :OP #xF389B
              :EVEX '(:0F38 :DDS :LIG :F2 :W0)
              :FEAT '(:AVX512_4FMAPS))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512_4FMAPS)))))
    (INST "VFMSUB132SD"
          (OP :OP #xF389B
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB132SS"
          (OP :OP #xF389B
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD132PD"
          (OP :OP #xF389C
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132PD"
          (OP :OP #xF389C
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132PS"
          (OP :OP #xF389C
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132PS"
          (OP :OP #xF389C
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132PD"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD132PD"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD132PD"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMADD132PS"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD132PS"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD132PS"
          (OP :OP #xF389C
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD132SD"
          (OP :OP #xF389D
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132SS"
          (OP :OP #xF389D
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD132SD"
          (OP :OP #xF389D
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD132SS"
          (OP :OP #xF389D
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB132PD"
          (OP :OP #xF389E
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132PD"
          (OP :OP #xF389E
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132PS"
          (OP :OP #xF389E
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132PS"
          (OP :OP #xF389E
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132PD"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB132PD"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB132PD"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB132PS"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB132PS"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB132PS"
          (OP :OP #xF389E
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB132SD"
          (OP :OP #xF389F
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132SS"
          (OP :OP #xF389F
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB132SD"
          (OP :OP #xF389F
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB132SS"
          (OP :OP #xF389F
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VPSCATTERDD"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERDD"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERDD"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPSCATTERDQ"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERDQ"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERDQ"
          (OP :OP #xF38A0
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPSCATTERQD"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERQD"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERQD"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VPSCATTERQQ"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERQQ"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VPSCATTERQQ"
          (OP :OP #xF38A1
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VSCATTERDPD"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERDPD"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERDPD"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VSCATTERDPS"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERDPS"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERDPS"
          (OP :OP #xF38A2
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VSCATTERQPD"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERQPD"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERQPD"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VSCATTERQPS"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERQPS"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512VL :AVX512F)))))
    (INST "VSCATTERQPS"
          (OP :OP #xF38A3
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12 (:AVX512F)))))
    (INST "VFMADDSUB213PD"
          (OP :OP #xF38A6
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB213PD"
          (OP :OP #xF38A6
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB213PS"
          (OP :OP #xF38A6
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB213PS"
          (OP :OP #xF38A6
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB213PD"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB213PD"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB213PD"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADDSUB213PS"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB213PS"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB213PS"
          (OP :OP #xF38A6
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD213PD"
          (OP :OP #xF38A7
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD213PD"
          (OP :OP #xF38A7
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD213PS"
          (OP :OP #xF38A7
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD213PS"
          (OP :OP #xF38A7
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD213PD"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD213PD"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD213PD"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD213PS"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD213PS"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD213PS"
          (OP :OP #xF38A7
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD213PD"
          (OP :OP #xF38A8
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213PD"
          (OP :OP #xF38A8
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213PS"
          (OP :OP #xF38A8
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213PS"
          (OP :OP #xF38A8
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213PD"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD213PD"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD213PD"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD213PS"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD213PS"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD213PS"
          (OP :OP #xF38A8
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD213SD"
          (OP :OP #xF38A9
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213SS"
          (OP :OP #xF38A9
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD213SD"
          (OP :OP #xF38A9
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMADD213SS"
          (OP :OP #xF38A9
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB213PD"
          (OP :OP #xF38AA
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB213PD"
          (OP :OP #xF38AA
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB213PS"
          (OP :OP #xF38AA
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB213PS"
          (OP :OP #xF38AA
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "V4FNMADDPS"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :DDS :512 :F2 :W0)
              :FEAT '(:AVX512_4FMAPS))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512_4FMAPS)))))
    (INST "VFMSUB213PD"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB213PD"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB213PD"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB213PS"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB213PS"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB213PS"
          (OP :OP #xF38AA
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB213SD"
          (OP :OP #xF38AB
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB213SS"
          (OP :OP #xF38AB
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "V4FNMADDSS"
          (OP :OP #xF38AB
              :EVEX '(:0F38 :DDS :LIG :F2 :W0)
              :FEAT '(:AVX512_4FMAPS))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512_4FMAPS)))))
    (INST "VFMSUB213SD"
          (OP :OP #xF38AB
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB213SS"
          (OP :OP #xF38AB
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD213PD"
          (OP :OP #xF38AC
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213PD"
          (OP :OP #xF38AC
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213PS"
          (OP :OP #xF38AC
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213PS"
          (OP :OP #xF38AC
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213PD"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD213PD"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD213PD"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMADD213PS"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD213PS"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD213PS"
          (OP :OP #xF38AC
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMADD213SD"
          (OP :OP #xF38AD
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213SS"
          (OP :OP #xF38AD
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD213SD"
          (OP :OP #xF38AD
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD213SS"
          (OP :OP #xF38AD
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB213PD"
          (OP :OP #xF38AE
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213PD"
          (OP :OP #xF38AE
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213PS"
          (OP :OP #xF38AE
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213PS"
          (OP :OP #xF38AE
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213PD"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB213PD"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB213PD"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB213PS"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB213PS"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB213PS"
          (OP :OP #xF38AE
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB213SD"
          (OP :OP #xF38AF
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213SS"
          (OP :OP #xF38AF
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB213SD"
          (OP :OP #xF38AF
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB213SS"
          (OP :OP #xF38AF
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VPMADD52LUQ"
          (OP :OP #xF38B4
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512_IFMA :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA :AVX512VL)))))
    (INST "VPMADD52LUQ"
          (OP :OP #xF38B4
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512_IFMA :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA :AVX512VL)))))
    (INST "VPMADD52LUQ"
          (OP :OP #xF38B4
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512_IFMA))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA)))))
    (INST "VPMADD52HUQ"
          (OP :OP #xF38B5
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512_IFMA :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA :AVX512VL)))))
    (INST "VPMADD52HUQ"
          (OP :OP #xF38B5
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512_IFMA :AVX512VL))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA :AVX512VL)))))
    (INST "VPMADD52HUQ"
          (OP :OP #xF38B5
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512_IFMA))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512_IFMA)))))
    (INST "VFMADDSUB231PD"
          (OP :OP #xF38B6
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB231PD"
          (OP :OP #xF38B6
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB231PS"
          (OP :OP #xF38B6
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB231PS"
          (OP :OP #xF38B6
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADDSUB231PD"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB231PD"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB231PD"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADDSUB231PS"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB231PS"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADDSUB231PS"
          (OP :OP #xF38B6
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD231PD"
          (OP :OP #xF38B7
              :VEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD231PD"
          (OP :OP #xF38B7
              :VEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD231PS"
          (OP :OP #xF38B7
              :VEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD231PS"
          (OP :OP #xF38B7
              :VEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUBADD231PD"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD231PD"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD231PD"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUBADD231PS"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD231PS"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUBADD231PS"
          (OP :OP #xF38B7
              :EVEX '(:0F38 :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD231PD"
          (OP :OP #xF38B8
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231PD"
          (OP :OP #xF38B8
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231PS"
          (OP :OP #xF38B8
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231PS"
          (OP :OP #xF38B8
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231PD"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD231PD"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD231PD"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD231PS"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD231PS"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMADD231PS"
          (OP :OP #xF38B8
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMADD231SD"
          (OP :OP #xF38B9
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231SS"
          (OP :OP #xF38B9
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMADD231SD"
          (OP :OP #xF38B9
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMADD231SS"
          (OP :OP #xF38B9
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB231PD"
          (OP :OP #xF38BA
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231PD"
          (OP :OP #xF38BA
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231PS"
          (OP :OP #xF38BA
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231PS"
          (OP :OP #xF38BA
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231PD"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB231PD"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB231PD"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB231PS"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB231PS"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFMSUB231PS"
          (OP :OP #xF38BA
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFMSUB231SD"
          (OP :OP #xF38BB
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231SS"
          (OP :OP #xF38BB
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFMSUB231SD"
          (OP :OP #xF38BB
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFMSUB231SS"
          (OP :OP #xF38BB
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD231PD"
          (OP :OP #xF38BC
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231PD"
          (OP :OP #xF38BC
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231PS"
          (OP :OP #xF38BC
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231PS"
          (OP :OP #xF38BC
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231PD"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD231PD"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD231PD"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMADD231PS"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD231PS"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMADD231PS"
          (OP :OP #xF38BC
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMADD231SD"
          (OP :OP #xF38BD
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231SS"
          (OP :OP #xF38BD
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMADD231SD"
          (OP :OP #xF38BD
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMADD231SS"
          (OP :OP #xF38BD
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB231PD"
          (OP :OP #xF38BE
              :VEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231PD"
          (OP :OP #xF38BE
              :VEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231PS"
          (OP :OP #xF38BE
              :VEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231PS"
          (OP :OP #xF38BE
              :VEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231PD"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB231PD"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB231PD"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB231PS"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB231PS"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFNMSUB231PS"
          (OP :OP #xF38BE
              :EVEX '(:0F38 :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFNMSUB231SD"
          (OP :OP #xF38BF
              :VEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231SS"
          (OP :OP #xF38BF
              :VEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:FMA :AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-2 (:FMA :AVX)))))
    (INST "VFNMSUB231SD"
          (OP :OP #xF38BF
              :EVEX '(:0F38 :DDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFNMSUB231SS"
          (OP :OP #xF38BF
              :EVEX '(:0F38 :DDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VPCONFLICTD"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPCONFLICTD"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPCONFLICTD"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512CD)))))
    (INST "VPCONFLICTQ"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPCONFLICTQ"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512CD)))))
    (INST "VPCONFLICTQ"
          (OP :OP #xF38C4
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512CD))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512CD)))))
    (INST "VGATHERPF0DPS"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF0DPD"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF1DPS"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF1DPD"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF0DPS"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x5)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF0DPD"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x5)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF1DPS"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF1DPD"
          (OP :OP #xF38C6
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF0QPS"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF0QPD"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x1)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF1QPS"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VGATHERPF1QPD"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x2)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF0QPS"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x5)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF0QPD"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x5)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF1QPS"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512PF)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "VSCATTERPF1QPD"
          (OP :OP #xF38C7
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512PF)
              :REG #x6)
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E12NP (:AVX512PF)))))
    (INST "SHA1NEXTE"
          (OP :OP #xF38C8 :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "VEXP2PD"
          (OP :OP #xF38C8
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "VEXP2PS"
          (OP :OP #xF38C8
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "SHA1MSG1"
          (OP :OP #xF38C9 :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "SHA1MSG2"
          (OP :OP #xF38CA :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "VRCP28PD"
          (OP :OP #xF38CA
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "VRCP28PS"
          (OP :OP #xF38CA
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "SHA256RNDS2"
          (OP :OP #xF38CB :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "VRCP28SD"
          (OP :OP #xF38CB
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512ER)))))
    (INST "VRCP28SS"
          (OP :OP #xF38CB
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512ER)))))
    (INST "SHA256MSG1"
          (OP :OP #xF38CC :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "VRSQRT28PD"
          (OP :OP #xF38CC
              :EVEX '(:0F38 :512 :66 :W1)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "VRSQRT28PS"
          (OP :OP #xF38CC
              :EVEX '(:0F38 :512 :66 :W0)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512ER)))))
    (INST "SHA256MSG2"
          (OP :OP #xF38CD :FEAT '(:SHA))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "VRSQRT28SD"
          (OP :OP #xF38CD
              :EVEX '(:0F38 :NDS :LIG :66 :W1)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512ER)))))
    (INST "VRSQRT28SS"
          (OP :OP #xF38CD
              :EVEX '(:0F38 :NDS :LIG :66 :W0)
              :FEAT '(:AVX512ER))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512ER)))))
    (INST "AESIMC"
          (OP :OP #xF38DB
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "VAESIMC"
          (OP :OP #xF38DB
              :VEX '(:0F38 :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ) :OP2 '(W DQ))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "AESENC"
          (OP :OP #xF38DC
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "VAESENC"
          (OP :OP #xF38DC
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "AESENCAST"
          (OP :OP #xF38DD
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "VAESENCLAST"
          (OP :OP #xF38DD
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "AESDEC"
          (OP :OP #xF38DE
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "VAESDEC"
          (OP :OP #xF38DE
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "AESDECLAST"
          (OP :OP #xF38DF
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "VAESDECLAST"
          (OP :OP #xF38DF
              :VEX '(:0F38 :NDS :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "MOVBE" (OP :OP #xF38F0 :PFX :NO-PREFIX
                      :FEAT '(:MOVBE))
          (ARG :OP1 '(G Y) :OP2 '(M Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-REPNE-F2-V86-CPUID-CASE)
                 (UD-REP-F3-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVBE" (OP :OP #xF38F0 :PFX :66
                      :FEAT '(:MOVBE))
          (ARG :OP1 '(G W) :OP2 '(M W))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-REPNE-F2-V86-CPUID-CASE)
                 (UD-REP-F3-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))))
    ;; A note about the two mandatory prefixes listed for CRC (0F 38 F0) in the
    ;; Intel Opcode Map: The first three-byte opcode map lists CRC under 66 &
    ;; F2 separately, even though CRC is already listed under F2 and MOVBE
    ;; under 66.  Essentially, 66 is just a modifier prefix for CRC in this
    ;; case.  So we ignore that opcode row in our representation, because
    ;; opcode dispatch, modr/m determination, opcode coverage, etc. (which is
    ;; what these tables are used for) will still work as expected for CRC,
    ;; irrespective of whether 66 is present as a modifier or not.
    (INST "CRC32" (OP :OP #xF38F0 :PFX :F2
                      :FEAT '(:SSE4.2))
          (ARG :OP1 '(G D) :OP2 '(E B))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MOVBE" (OP :OP #xF38F1 :PFX :NO-PREFIX
                      :FEAT '(:MOVBE))
          (ARG :OP1 '(M Y) :OP2 '(G Y))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-REPNE-F2-V86-CPUID-CASE)
                 (UD-REP-F3-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "MOVBE" (OP :OP #xF38F1 :PFX :66
                      :FEAT '(:MOVBE))
          (ARG :OP1 '(M W) :OP2 '(G W))
          'NIL
          '((:UD (UD-LOCK-USED)
                 (UD-REPNE-F2-V86-CPUID-CASE)
                 (UD-REP-F3-USED)
                 (UD-MODR/M.MOD-INDICATES-REGISTER))))
    (INST "CRC32" (OP :OP #xF38F1 :PFX :F2
                      :FEAT '(:SSE4.2))
          (ARG :OP1 '(G D) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ANDN"
          (OP :OP #xF38F2
              :VEX '(:0F38 :NDS :LZ :W0)
              :FEAT '(:BMI1 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "ANDN"
          (OP :OP #xF38F2
              :VEX '(:0F38 :NDS :LZ :W1)
              :FEAT '(:BMI1 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    ;; BLSR, BLSMSK, BLSI are VEX-only instructions.
    ;; (INST "BLSR"
    ;;       (OP :OP #xF38F3
    ;;           :REG #x1
    ;;           :SUPERSCRIPTS '(:V)
    ;;           :FEAT '(:BMI2 :AVX)
    ;;           :GROUP '(:GROUP-17))
    ;;       (ARG :OP1 '(B Y) :OP2 '(E Y))
    ;;       'NIL
    ;;       '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    ;; (INST "BLSMSK"
    ;;       (OP :OP #xF38F3
    ;;           :REG #x2
    ;;           :FEAT '(:BMI2 :AVX)
    ;;           :SUPERSCRIPTS '(:V)
    ;;           :GROUP '(:GROUP-17))
    ;;       (ARG :OP1 '(B Y) :OP2 '(E Y))
    ;;       'NIL
    ;;       '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    ;; (INST "BLSI"
    ;;       (OP :OP #xF38F3
    ;;           :REG #x3
    ;;           :SUPERSCRIPTS '(:V)
    ;;           :FEAT '(:BMI2 :AVX))
    ;;       (ARG :OP1 '(B Y) :OP2 '(E Y))
    ;;       'NIL
    ;;       '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "BLSR"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W0)
              :FEAT '(:BMI1 :AVX)
              :REG #x1
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BLSR"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W1)
              :FEAT '(:BMI1 :AVX)
              :REG #x1
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BLSMSK"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W0)
              :FEAT '(:BMI1 :AVX)
              :REG #x2
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BLSMSK"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W1)
              :FEAT '(:BMI1 :AVX)
              :REG #x2
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BLSI"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W0)
              :FEAT '(:BMI1 :AVX)
              :REG #x3
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BLSI"
          (OP :OP #xF38F3
              :VEX '(:0F38 :NDD :LZ :W1)
              :FEAT '(:BMI1 :AVX)
              :REG #x3
              :GROUP '(:GROUP-17))
          (ARG :OP1 '(B Y) :OP2 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BZHI"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "BZHI"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "PDEP"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :F2 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "PDEP"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :F2 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "PEXT"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :F3 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "PEXT"
          (OP :OP #xF38F5
              :VEX '(:0F38 :NDS :LZ :F3 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(B Y)
               :OP3 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "ADCX"
          (OP :OP #xF38F6
              :PFX :66
              :FEAT '(:ADX))
          (ARG :OP1 '(G Y) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "ADOX"
          (OP :OP #xF38F6
              :PFX :F3
              :FEAT '(:ADX))
          (ARG :OP1 '(G Y) :OP2 '(E Y))
          'NIL
          '((:UD (UD-LOCK-USED))))
    (INST "MULX"
          (OP :OP #xF38F6
              :VEX '(:0F38 :NDD :LZ :F2 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(B Y)
               :OP2 '(G Y)
               :OP3 '(:RDX)
               :OP4 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "MULX"
          (OP :OP #xF38F6
              :VEX '(:0F38 :NDD :LZ :F2 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(B Y)
               :OP2 '(G Y)
               :OP3 '(:RDX)
               :OP4 '(E Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "BEXTR"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :W0)
              :FEAT '(:BMI1 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "BEXTR"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :W1)
              :FEAT '(:BMI1 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI1 :AVX)))))
    (INST "SARX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :F3 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "SARX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :F3 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "SHLX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :66 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "SHLX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :66 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "SHRX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :F2 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "SHRX"
          (OP :OP #xF38F7
              :VEX '(:0F38 :NDS :LZ :F2 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(B Y))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))))

(defconst *pre-0f-3a-three-byte-opcode-map*
  '((INST "VPERMQ"
          (OP :OP #xF3A00
              :VEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(W QQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPERMQ"
          (OP :OP #xF3A00
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMQ"
          (OP :OP #xF3A00
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMPD"
          (OP :OP #xF3A01
              :VEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(W QQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPERMPD"
          (OP :OP #xF3A01
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMPD"
          (OP :OP #xF3A01
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPBLENDD"
          (OP :OP #xF3A02
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPBLENDD"
          (OP :OP #xF3A02
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VALIGND"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VALIGNQ"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VALIGND"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VALIGNQ"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VALIGND"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VALIGNQ"
          (OP :OP #xF3A03
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMILPS"
          (OP :OP #xF3A04
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPS"
          (OP :OP #xF3A04
              :VEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPS"
          (OP :OP #xF3A04
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPS"
          (OP :OP #xF3A04
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPS"
          (OP :OP #xF3A04
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF3A05
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPD"
          (OP :OP #xF3A05
              :VEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPERMILPD"
          (OP :OP #xF3A05
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF3A05
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VPERMILPD"
          (OP :OP #xF3A05
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPERM2F128"
          (OP :OP #xF3A06
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "ROUNDPS"
          (OP :OP #xF3A08
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE4.1)))))
    (INST "VROUNDPS"
          (OP :OP #xF3A08
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VROUNDPS"
          (OP :OP #xF3A08
              :VEX '(:0F3A :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VRNDSCALEPS"
          (OP :OP #xF3A08
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VRNDSCALEPS"
          (OP :OP #xF3A08
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VRNDSCALEPS"
          (OP :OP #xF3A08
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "ROUNDPD"
          (OP :OP #xF3A09
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE4.1)))))
    (INST "VROUNDPD"
          (OP :OP #xF3A09
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VROUNDPD"
          (OP :OP #xF3A09
              :VEX '(:0F3A :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(W X)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VRNDSCALEPD"
          (OP :OP #xF3A09
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VRNDSCALEPD"
          (OP :OP #xF3A09
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VRNDSCALEPD"
          (OP :OP #xF3A09
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "ROUNDSS"
          (OP :OP #xF3A0A
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V SS)
               :OP2 '(W SS)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-3 (:SSE4.1)))))
    (INST "VROUNDSS"
          (OP :OP #xF3A0A
              :VEX '(:0F3A :NDS :LIG :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SS)
               :OP2 '(W SS)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VRNDSCALESS"
          (OP :OP #xF3A0A
              :EVEX '(:0F3A :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "ROUNDSD"
          (OP :OP #xF3A0B
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V SD)
               :OP2 '(W SD)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-3 (:SSE4.1)))))
    (INST "VROUNDSD"
          (OP :OP #xF3A0B
              :VEX '(:0F3A :NDS :LIG :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V SD)
               :OP2 '(W SD)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-3 (:AVX)))))
    (INST "VRNDSCALESD"
          (OP :OP #xF3A0B
              :EVEX '(:0F3A :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "BLENDPS"
          (OP :OP #xF3A0C
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VBLENDPS"
          (OP :OP #xF3A0C
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBLENDPS"
          (OP :OP #xF3A0C
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "BLENDPD"
          (OP :OP #xF3A0D
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VBLENDPD"
          (OP :OP #xF3A0D
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBLENDPD"
          (OP :OP #xF3A0D
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PBLENDW"
          (OP :OP #xF3A0E
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VPBLENDW"
          (OP :OP #xF3A0E
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPBLENDW"
          (OP :OP #xF3A0E
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "PALIGNR"
          (OP :OP #xF3A0F
              :PFX :NO-PREFIX
              :FEAT '(:SSSE3))
          (ARG :OP1 '(P Q)
               :OP2 '(Q Q)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "PALIGNR"
          (OP :OP #xF3A0F
              :PFX :66
              :FEAT '(:SSSE3))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSSE3)))))
    (INST "VPALIGNR"
          (OP :OP #xF3A0F
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPALIGNR"
          (OP :OP #xF3A0F
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VPALIGNR"
          (OP :OP #xF3A0F
              :EVEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPALIGNR"
          (OP :OP #xF3A0F
              :EVEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VPALIGNR"
          (OP :OP #xF3A0F
              :EVEX '(:0F3A :NDS :512 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "PEXTRB"
          (OP :OP #xF3A14 :MOD :MEM :PFX :66)
          (ARG :OP1 '(M B)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PEXTRB"
          (OP :OP #xF3A14 :MOD #x3 :PFX :66)
          (ARG :OP1 '(R D)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPEXTRB"
          (OP :OP #xF3A14
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(R D)
               :OP2 '(V DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPEXTRB"
          (OP :OP #xF3A14
              :EVEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "PEXTRW"
          (OP :OP #xF3A15 :MOD :MEM :PFX :66)
          (ARG :OP1 '(M W)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "PEXTRW"
          (OP :OP #xF3A15 :MOD #x3 :PFX :66)
          (ARG :OP1 '(R D)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:AVX2)))))
    (INST "VPEXTRW"
          (OP :OP #xF3A15
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(G D)
               :OP2 '(U DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPEXTRW"
          (OP :OP #xF3A15
              :EVEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))
    (INST "PEXTRD/Q"
          (OP :OP #xF3A16
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(E Y)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VPEXTRD"
          (OP :OP #xF3A16
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(E Y)
               :OP2 '(V DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPEXTRQ"
          (OP :OP #xF3A16
              :VEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(E Y)
               :OP2 '(V DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPEXTRD"
          (OP :OP #xF3A16
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512DQ)))))
    (INST "VPEXTRQ"
          (OP :OP #xF3A16
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512DQ)))))
    (INST "EXTRACTPS"
          (OP :OP #xF3A17
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(E D)
               :OP2 '(V DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VEXTRACTPS"
          (OP :OP #xF3A17
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(E D)
               :OP2 '(V DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VEXTRACTPS"
          (OP :OP #xF3A17
              :EVEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "VINSERTF128"
          (OP :OP #xF3A18
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VINSERTF32X4"
          (OP :OP #xF3A18
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512F)))))
    (INST "VINSERTF64X2"
          (OP :OP #xF3A18
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512DQ)))))
    (INST "VINSERTF32X4"
          (OP :OP #xF3A18
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VINSERTF64X2"
          (OP :OP #xF3A18
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VEXTRACTF128"
          (OP :OP #xF3A19
              :VEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(W DQ)
               :OP2 '(V QQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX)))))
    (INST "VEXTRACTF32X4"
          (OP :OP #xF3A19
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512F)))))
    (INST "VEXTRACTF64X2"
          (OP :OP #xF3A19
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512DQ)))))
    (INST "VEXTRACTF32x4"
          (OP :OP #xF3A19
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VEXTRACTF64X2"
          (OP :OP #xF3A19
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VINSERTF32X4"
          (OP :OP #xF3A1A
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VINSERTF64X2"
          (OP :OP #xF3A1A
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VEXTRACTF32x4"
          (OP :OP #xF3A1B
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VEXTRACTF64X2"
          (OP :OP #xF3A1B
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VCVTPS2PH"
          (OP :OP #xF3A1D
              :VEX '(:0F3A :128 :66 :W0)
              :FEAT '(:F16C :AVX))
          (ARG :OP1 '(W X)
               :OP2 '(V X)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-11 (:F16C :AVX)))))
    (INST "VCVTPS2PH"
          (OP :OP #xF3A1D
              :VEX '(:0F3A :256 :66 :W0)
              :FEAT '(:F16C :AVX))
          (ARG :OP1 '(W X)
               :OP2 '(V X)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-11 (:F16C :AVX)))))
    (INST "VCVTPS2PH"
          (OP :OP #xF3A1D
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2PH"
          (OP :OP #xF3A1D
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512VL :AVX512F)))))
    (INST "VCVTPS2PH"
          (OP :OP #xF3A1D
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E11 (:AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1E
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPD"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPCMPQ"
          (OP :OP #xF3A1F
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))

    (INST "PINSRB"
          (OP :OP #xF3A20
              :PFX :66
              :MOD #x3
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(R Y)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))

    (INST "PINSRB"
          (OP :OP #xF3A20
              :PFX :66
              :MOD :MEM
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(M B)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VPINSRB"
          (OP :OP #xF3A20
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(R Y)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPINSRB"
          (OP :OP #xF3A20
              :EVEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512BW)))))

    (INST "INSERTPS"
          (OP :OP #xF3A21
              :PFX :66
              :MOD :MEM
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(M D)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))

    (INST "INSERTPS"
          (OP :OP #xF3A21
              :PFX :66
              :MOD #x3
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(U DQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VINSERTPS"
          (OP :OP #xF3A21
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD :MEM)
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(M D)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VINSERTPS"
          (OP :OP #xF3A21
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX)
              :MOD #x3)
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(U DQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VINSERTPS"
          (OP :OP #xF3A21
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512F)))))
    (INST "PINSRD/Q"
          (OP :OP #xF3A22
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(E Y)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-5 (:SSE4.1)))))
    (INST "VPINSRD"
          (OP :OP #xF3A22
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(E Y)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPINSRQ"
          (OP :OP #xF3A22
              :VEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(E Y)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-5 (:AVX)))))
    (INST "VPINSRD"
          (OP :OP #xF3A22
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512DQ)))))
    (INST "VPINSRQ"
          (OP :OP #xF3A22
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E9NF (:AVX512DQ)))))
    (INST "VSHUFF32X4"
          (OP :OP #xF3A23
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFF64X2"
          (OP :OP #xF3A23
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFF32x4"
          (OP :OP #xF3A23
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VSHUFF64x2"
          (OP :OP #xF3A23
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VPTERNLOGD"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTERNLOGQ"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTERNLOGD"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTERNLOGQ"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512F)))))
    (INST "VPTERNLOGD"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VPTERNLOGQ"
          (OP :OP #xF3A25
              :EVEX '(:0F3A :DDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512F)))))
    (INST "VGETMANTPD"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETMANTPD"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETMANTPD"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VGETMANTPS"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETMANTPS"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VGETMANTPS"
          (OP :OP #xF3A26
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VGETMANTSD"
          (OP :OP #xF3A27
              :EVEX '(:0F3A :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VGETMANTSS"
          (OP :OP #xF3A27
              :EVEX '(:0F3A :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "KSHIFTRB"
          (OP :OP #xF3A30
              :VEX '(:0F3A :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KSHIFTRW"
          (OP :OP #xF3A30
              :VEX '(:0F3A :L0 :66 :W1)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-R/M W)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "KSHIFTRD"
          (OP :OP #xF3A31
              :VEX '(:0F3A :L0 :66 :W0)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KSHIFTRQ"
          (OP :OP #xF3A31
              :VEX '(:0F3A :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-R/M Q)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KSHIFTLB"
          (OP :OP #xF3A32
              :VEX '(:0F3A :L0 :66 :W0)
              :FEAT '(:AVX512DQ)
              :MOD #x3)
          (ARG :OP1 '(K-REG B)
               :OP2 '(K-R/M B)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512DQ)))))
    (INST "KSHIFTLW"
          (OP :OP #xF3A32
              :VEX '(:0F3A :L0 :66 :W1)
              :FEAT '(:AVX512F)
              :MOD #x3)
          (ARG :OP1 '(K-REG W)
               :OP2 '(K-R/M W)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512F)))))
    (INST "KSHIFTLD"
          (OP :OP #xF3A33
              :VEX '(:0F3A :L0 :66 :W0)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG D)
               :OP2 '(K-R/M D)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "KSHIFTLQ"
          (OP :OP #xF3A33
              :VEX '(:0F3A :L0 :66 :W1)
              :FEAT '(:AVX512BW)
              :MOD #x3)
          (ARG :OP1 '(K-REG Q)
               :OP2 '(K-R/M Q)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-K20 (:AVX512BW)))))
    (INST "VINSERTI128"
          (OP :OP #xF3A38
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VINSERTI32X4"
          (OP :OP #xF3A38
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512F)))))
    (INST "VINSERTI64X2"
          (OP :OP #xF3A38
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512DQ)))))
    (INST "VINSERTI32X4"
          (OP :OP #xF3A38
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VINSERTI64X2"
          (OP :OP #xF3A38
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VEXTRACTI128"
          (OP :OP #xF3A39
              :VEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(W DQ)
               :OP2 '(V QQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VEXTRACTI32X4"
          (OP :OP #xF3A39
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512F)))))
    (INST "VEXTRACTI64X2"
          (OP :OP #xF3A39
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512VL :AVX512DQ)))))
    (INST "VEXTRACTI32x4"
          (OP :OP #xF3A39
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VEXTRACTI64X2"
          (OP :OP #xF3A39
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VINSERTI32X4"
          (OP :OP #xF3A3A
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VINSERTI64X2"
          (OP :OP #xF3A3A
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VEXTRACTI32x4"
          (OP :OP #xF3A3B
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512DQ)))))
    (INST "VEXTRACTI64X2"
          (OP :OP #xF3A3B
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6NF (:AVX512F)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3E
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3E
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3E
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPCMPW"
          (OP :OP #xF3A3E
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPW"
          (OP :OP #xF3A3E
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPB"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "VPCMPW"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPW"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512VL :AVX512BW)))))
    (INST "VPCMPW"
          (OP :OP #xF3A3F
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4.NB (:AVX512BW)))))
    (INST "DPPS"
          (OP :OP #xF3A40
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE4.1)))))
    (INST "VDPPS"
          (OP :OP #xF3A40
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "VDPPS"
          (OP :OP #xF3A40
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "DPPD"
          (OP :OP #xF3A41
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-2 (:SSE4.1)))))
    (INST "VDPPD"
          (OP :OP #xF3A41
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-2 (:AVX)))))
    (INST "MPSADBW"
          (OP :OP #xF3A42
              :PFX :66
              :FEAT '(:SSE4.1))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.1)))))
    (INST "VMPSADBW"
          (OP :OP #xF3A42
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VMPSADBW"
          (OP :OP #xF3A42
              :VEX '(:0F3A :NDS :256 :66 :WIG)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VDBPSADBW"
          (OP :OP #xF3A42
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VDBPSADBW"
          (OP :OP #xF3A42
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512VL :AVX512BW)))))
    (INST "VDBPSADBW"
          (OP :OP #xF3A42
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512BW))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF.NB (:AVX512BW)))))
    (INST "VSHUFI32X4"
          (OP :OP #xF3A43
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFI64X2"
          (OP :OP #xF3A43
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512VL :AVX512F)))))
    (INST "VSHUFI32x4"
          (OP :OP #xF3A43
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "VSHUFI64x2"
          (OP :OP #xF3A43
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4NF (:AVX512F)))))
    (INST "PCLMULQDQ"
          (OP :OP #xF3A44
              :PFX :66
              :FEAT '(:PCLMULQDQ))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ)
               :OP4 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:PCLMULQDQ)))))
    (INST "VPCLMULQDQ"
          (OP :OP #xF3A44
              :VEX '(:0F3A :NDS :128 :66 :WIG)
              :FEAT '(:PCLMULQDQ :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(H DQ)
               :OP3 '(W DQ)
               :OP4 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:PCLMULQDQ :AVX)))))
    (INST "VPERM2I128"
          (OP :OP #xF3A46
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V QQ)
               :OP2 '(H QQ)
               :OP3 '(W QQ)
               :OP4 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-6 (:AVX2)))))
    (INST "VBLENDVPS"
          (OP :OP #xF3A4A
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBLENDVPS"
          (OP :OP #xF3A4A
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBLENDVPD"
          (OP :OP #xF3A4B
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VBLENDVPD"
          (OP :OP #xF3A4B
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPBLENDVB"
          (OP :OP #xF3A4C
              :VEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VPBLENDVB"
          (OP :OP #xF3A4C
              :VEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX2))
          (ARG :OP1 '(V X)
               :OP2 '(H X)
               :OP3 '(W X)
               :OP4 '(L X))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX2)))))
    (INST "VRANGEPD"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VRANGEPD"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VRANGEPD"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VRANGEPS"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VRANGEPS"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VRANGEPS"
          (OP :OP #xF3A50
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VRANGESD"
          (OP :OP #xF3A51
              :EVEX '(:0F3A :NDS :LIG :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512DQ)))))
    (INST "VRANGESS"
          (OP :OP #xF3A51
              :EVEX '(:0F3A :NDS :LIG :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512DQ)))))
    (INST "VFIXUPIMMPD"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFIXUPIMMPD"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFIXUPIMMPD"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :512 :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFIXUPIMMPS"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :512 :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512F)))))
    (INST "VFIXUPIMMPS"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFIXUPIMMPS"
          (OP :OP #xF3A54
              :EVEX '(:0F3A :NDS :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512F)))))
    (INST "VFIXUPIMMSD"
          (OP :OP #xF3A55
              :EVEX '(:0F3A :NDS :LIG :66 :W1)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VFIXUPIMMSS"
          (OP :OP #xF3A55
              :EVEX '(:0F3A :NDS :LIG :66 :W0)
              :FEAT '(:AVX512F))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512F)))))
    (INST "VREDUCEPD"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VREDUCEPD"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VREDUCEPD"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VREDUCEPS"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VREDUCEPS"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512VL :AVX512DQ)))))
    (INST "VREDUCEPS"
          (OP :OP #xF3A56
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E2 (:AVX512DQ)))))
    (INST "VREDUCESS"
          (OP :OP #xF3A57
              :EVEX '(:0F3A :NDS :LIG :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512DQ)))))
    (INST "VREDUCESD"
          (OP :OP #xF3A57
              :EVEX '(:0F3A :NDS :LIG :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E3 (:AVX512DQ)))))
    (INST "PCMPESTRM"
          (OP :OP #xF3A60
              :PFX :66
              :FEAT '(:SSE4.2))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.2)))))
    (INST "VPCMPESTRM"
          (OP :OP #xF3A60
              :VEX '(:0F3A :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PCMPESTRI"
          (OP :OP #xF3A61
              :PFX :66
              :FEAT '(:SSE4.2))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.2)))))
    (INST "VPCMPESTRI"
          (OP :OP #xF3A61
              :VEX '(:0F3A :128 :66)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PCMPISTRM"
          (OP :OP #xF3A62
              :PFX :66
              :FEAT '(:SSE4.2))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.2)))))
    (INST "VPCMPISTRM"
          (OP :OP #xF3A62
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "PCMPISTRI"
          (OP :OP #xF3A63
              :PFX :66
              :FEAT '(:SSE4.2))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SSE4.2)))))
    (INST "VPCMPISTRI"
          (OP :OP #xF3A63
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          NIL '((:EX (CHK-EXC :TYPE-4 (:AVX)))))
    (INST "VFPCLASSPD"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :128 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VFPCLASSPD"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :256 :66 :W1)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VFPCLASSPD"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :512 :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VFPCLASSPS"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :128 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VFPCLASSPS"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :256 :66 :W0)
              :FEAT '(:AVX512VL :AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512VL :AVX512DQ)))))
    (INST "VFPCLASSPS"
          (OP :OP #xF3A66
              :EVEX '(:0F3A :512 :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E4 (:AVX512DQ)))))
    (INST "VFPCLASSSD"
          (OP :OP #xF3A67
              :EVEX '(:0F3A :LIG :66 :W1)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "VFPCLASSSS"
          (OP :OP #xF3A67
              :EVEX '(:0F3A :LIG :66 :W0)
              :FEAT '(:AVX512DQ))
          NIL NIL
          '((:EX (CHK-EXC :TYPE-E6 (:AVX512DQ)))))
    (INST "SHA1RNDS4"
          (OP :OP #xF3ACC :FEAT '(:SHA))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:SHA)))))
    (INST "AESKEYGENASSIST"
          (OP :OP #xF3ADF
              :PFX :66
              :FEAT '(:AES))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          'NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES)))))
    (INST "AESKEYGENASSIST"
          (OP :OP #xF3ADF
              :VEX '(:0F3A :128 :66 :WIG)
              :FEAT '(:AES :AVX))
          (ARG :OP1 '(V DQ)
               :OP2 '(W DQ)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-4 (:AES :AVX)))))
    (INST "RORX"
          (OP :OP #xF3AF0
              :VEX '(:0F3A :LZ :F2 :W0)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))
    (INST "RORX"
          (OP :OP #xF3AF0
              :VEX '(:0F3A :LZ :F2 :W1)
              :FEAT '(:BMI2 :AVX))
          (ARG :OP1 '(G Y)
               :OP2 '(E Y)
               :OP3 '(I B))
          NIL
          '((:EX (CHK-EXC :TYPE-13 (:BMI2 :AVX)))))))

;; ----------------------------------------------------------------------

(define eval-pre-map (x state)
   :mode :program
   (if (atom x)
       (mv nil x state)
     (b* (((mv ?erp val state)
           (acl2::trans-eval
            (car x)
            'eval-pre-map state t))
          ;; (car val) is stobjs-out.
          ;; (- (cw "~%~p0~%" (inst-p (cdr val))))
          ((mv erp rest state)
           (eval-pre-map (cdr x) state))
          (all (cons (cdr val) rest))
          (erp (or erp (if (inst-list-p all) nil t))))
       (mv erp all state))))

(make-event
 (mv-let (one-byte-opcode-map
          two-byte-opcode-map
          0F-38-three-byte-opcode-map
          0F-3A-three-byte-opcode-map
          state)
   (b* (((mv ?erp one-byte-map state)
         (eval-pre-map *pre-one-byte-opcode-map* state))
        ((mv ?erp two-byte-map state)
         (eval-pre-map *pre-two-byte-opcode-map* state))
        ((mv ?erp 0F-38-three-byte-map state)
         (eval-pre-map *pre-0F-38-three-byte-opcode-map* state))
        ((mv ?erp 0F-3A-three-byte-map state)
         (eval-pre-map *pre-0F-3A-three-byte-opcode-map* state)))
     (mv one-byte-map two-byte-map
         0F-38-three-byte-map 0F-3A-three-byte-map
         state))
   (mv nil
       `(progn
          (defconst *one-byte-opcode-map*         ',one-byte-opcode-map)
          (defconst *two-byte-opcode-map*         ',two-byte-opcode-map)
          (defconst *0F-38-three-byte-opcode-map* ',0F-38-three-byte-opcode-map)
          (defconst *0F-3A-three-byte-opcode-map* ',0F-3A-three-byte-opcode-map))
       state)))

(defthm inst-list-p-of-maps
  (and (inst-list-p *one-byte-opcode-map*)
       (inst-list-p *two-byte-opcode-map*)
       (inst-list-p *0F-38-three-byte-opcode-map*)
       (inst-list-p *0F-3A-three-byte-opcode-map*)))

;; ----------------------------------------------------------------------

;; Creating documentation for the implemented opcodes:

(defconst *x86isa-printconfig*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 16
   :print-radix t
   :print-lowercase t))

(defconst *x86isa-printconfig-uppercase*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 16
   :print-radix t
   :print-lowercase nil))

(defconst *x86isa-printconfig-base-10*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 10
   :print-radix nil
   :print-lowercase nil))

(defconst *x86isa-printconfig-base-10-lowercase*
  (str::make-printconfig
   :home-package (pkg-witness "X86ISA")
   :print-base 10
   :print-radix nil
   :print-lowercase t))

(define create-inst-doc ((inst inst-p)
                         &key
                         ((fn-ok? booleanp
                                  "Include information about the semantic
                          function in the documentation or not")
                          't)
                         ((arg-ok? booleanp
                                   "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                          'nil))

  :guard-hints (("Goal" :in-theory (e/d () (subseq))))
  :returns (inst-doc-string stringp)

  :prepwork

  ((define symbol-list-to-string ((lst symbol-listp))
     :returns (newstr stringp :hyp :guard)
     (if (atom lst)
         ""
       (if (eql (len lst) 1)
           (str::cat ":" (symbol-name (car lst)))
         (str::cat ":" (symbol-name (car lst)) " "
                   (symbol-list-to-string (cdr lst))))))

   (define create-extra-info-doc-string (info
                                         (text stringp))
     :returns (doc stringp :hyp :guard)

     (if info
         (let* ((info-string (cond ((symbolp info)
                                    (str::cat ":" (symbol-name info)))
                                   ((symbol-listp info)
                                    (symbol-list-to-string info))
                                   (t
                                    (str::pretty
                                     info
                                     :config
                                     *x86isa-printconfig-base-10*)))))
           (str::cat "<tr><td> @('" text "') </td>"
                     "<td> @('" info-string "') </td> </tr>"))
       ""))

   (define create-extra-info-doc ((opcode strict-opcode-p))
     :returns (doc stringp :hyp :guard)

     (b* (((opcode opcode))
          (feat-doc  (create-extra-info-doc-string opcode.feat ":FEAT "))
          (vex-doc   (create-extra-info-doc-string opcode.vex  ":VEX "))
          (evex-doc  (create-extra-info-doc-string opcode.evex ":EVEX "))
          (pfx-doc   (create-extra-info-doc-string opcode.pfx  ":PFX "))
          (mode-doc  (create-extra-info-doc-string opcode.mode ":MODE "))
          (reg-doc   (create-extra-info-doc-string opcode.reg  ":REG "))
          (mod-doc   (create-extra-info-doc-string opcode.mod  ":MOD "))
          (r/m-doc   (create-extra-info-doc-string opcode.r/m  ":R/M "))
          (rex-doc   (create-extra-info-doc-string opcode.rex  ":REX "))
          (extra-info (str::cat "<table>"
                                mode-doc pfx-doc reg-doc
                                mod-doc r/m-doc rex-doc
                                vex-doc evex-doc feat-doc
                                "</table>")))
       extra-info))

   (define gen-addressing-method-code-doc ((z-info alistp))
     ;; (gen-addressing-method-code-doc *Z-addressing-method-info*)
     :prepwork
     ((define get-addressing-method-doc ((code addressing-method-code-p))
        :returns (str stringp)
        (b* ((alst (cdr (assoc-equal code *Z-addressing-method-info*)))
             (doc (cdr (assoc-equal :doc alst)))
             ((unless doc) ""))
          doc)))
     (if (endp z-info)
         nil
       (b* ((code (caar z-info))
            ((unless (addressing-method-code-p code))
             (er hard? __function__ "~% Bad code ~x0 encountered! ~%" code))
            (codestr (str::pretty code :config *x86isa-printconfig-base-10*))
            (docstr (str::cat "@(' " codestr "'): " (get-addressing-method-doc code)))
            (topic-name (intern$ (str::cat codestr "-Z-ADDRESSING-METHOD") "X86ISA"))
            (form `((defxdoc ,topic-name
                      ;; We intentionally don't define a parent here.  We can
                      ;; wrap the call of this function inside an appropriate
                      ;; defsection if we want to generate addressing method
                      ;; information.
                      :long ,docstr)))
            (rest (gen-addressing-method-code-doc (cdr z-info))))
         (append form rest))))

   (define gen-operand-type-code-doc ((info alistp))
     ;; (gen-operand-type-code-doc *operand-type-code-info*)
     :prepwork
     ((define get-operand-type-code-doc ((code operand-type-code-p))
        :returns (str stringp)
        (b* ((alst (cdr (assoc-equal code *operand-type-code-info*)))
             (doc (cdr (assoc-equal :doc alst)))
             ((unless doc) ""))
          doc)))
     (if (endp info)
         nil
       (b* ((code (caar info))
            ((unless (operand-type-code-p code))
             (er hard? __function__ "~% Bad code ~x0 encountered! ~%" code))
            (codestr (str::pretty code :config *x86isa-printconfig-base-10-lowercase*))
            (docstr (str::cat "@(' " codestr "'): " (get-operand-type-code-doc code)))
            (topic-name (intern$
                         (str::upcase-string (str::cat codestr "-OPERAND-TYPE-CODE"))
                         "X86ISA"))
            (form `((defxdoc ,topic-name
                      ;; We intentionally don't define a parent here.  We can
                      ;; wrap the call of this function inside an appropriate
                      ;; defsection if we want to generate operand code type
                      ;; information.
                      :long ,docstr)))
            (rest (gen-operand-type-code-doc (cdr info))))
         (append form rest))))

   (define create-arg-doc ((x operand-type-p))
     :returns (xstr stringp)
     (cond
      ((atom x) " ")
      ((eql (len x) 1)
       (b* ((possible-code (nth 0 x))
            (codestr (str::pretty possible-code :config *x86isa-printconfig-base-10*))
            (topic-name (str::cat codestr "-Z-ADDRESSING-METHOD")))
         (if (addressing-method-code-p possible-code)
             (str::cat "[<a href=\"index.html?topic=X86ISA____" topic-name "\">" codestr "</a>] ")
           (str::cat "[@('" codestr "')] "))))
      ((eql (len x) 2)
       (b* ((addressing-mode (nth 0 x))
            (addressing-mode-str ;; Addressing Method Code in Upper Case
             (str::pretty addressing-mode :config *x86isa-printconfig-base-10*))
            (addressing-mode-topic-name
             (str::cat addressing-mode-str "-Z-ADDRESSING-METHOD"))
            (operand-code (nth 1 x))
            (operand-code-str ;; Operand Type Code in Lower Case
             (str::pretty operand-code :config *x86isa-printconfig-base-10-lowercase*))
            (operand-code-topic-name
             (str::upcase-string (str::cat operand-code-str "-OPERAND-TYPE-CODE"))))
         (str::cat
          "[<a href=\"index.html?topic=X86ISA____" addressing-mode-topic-name "\">"
          addressing-mode-str
          "</a> - <a href=\"index.html?topic=X86ISA____" operand-code-topic-name "\">"
          operand-code-str "</a>] ")))
      (t " ")))

   (define create-args-doc ((operands maybe-operands-p))
     :prepwork ((local (in-theory (e/d (maybe-operands-p) ()))))
     :returns (docstr stringp)
     (b* (((unless operands)
           ;; Instruction does not require any operands.
           "<td> </td>")
          ((operands operands))
          (op1 (create-arg-doc operands.op1))
          ((if (eql operands.op2 nil))
           (str::cat "<td> " op1 " </td>"))
          (op2 (create-arg-doc operands.op2))
          ((if (eql operands.op3 nil))
           (str::cat "<td> " op1 ", " op2 " </td>"))
          (op3 (create-arg-doc operands.op3))
          ((if (eql operands.op4 nil))
           (str::cat "<td> " op1 ", " op2 ", " op3 " </td>"))
          (op4 (create-arg-doc operands.op4)))
       (str::cat "<td> " op1 ", " op2 ", " op3 ", " op4 " </td>")))

   (defthm inst-p-implies-mnemonic-p
     (implies (inst-p x)
              (mnemonic-p (inst->mnemonic x)))
     :hints (("Goal" :in-theory (e/d (inst-p) ())))
     :rule-classes :forward-chaining)

   (defthm inst-p-implies-mnemonic-p-alt
     (implies (and (inst-p x)
                   (not (stringp (inst->mnemonic x))))
              ;; (keywordp (inst->mnemonic x))
              (symbolp (inst->mnemonic x)))
     :hints (("Goal"
              :use ((:instance inst-p-implies-mnemonic-p))
              :in-theory (e/d (mnemonic-p inst->mnemonic)
                              (inst-p-implies-mnemonic-p)))))

   (defthm inst-p-implies-consp-fn
     (implies (and (inst-p x)
                   (inst->fn x))
              (consp (inst->fn x)))
     :hints (("Goal" :in-theory (e/d (fn-desc-p inst->fn fn-desc-p) ())))))

  (b* (((inst inst))
       (opcode inst.opcode)
       ((opcode opcode))
       ;; We only add the low 8 bits of the opcode in the documentation for
       ;; three reasons: (1) to save horizontal space in the table; (2) the
       ;; table headings will list whether we're dealing with one-, two-, or
       ;; three-byte map, and in the last two cases, will mention whether the
       ;; opcode bytes begin with 0F_38 or 0F_3A; and (3) VEX- and EVEX-encoded
       ;; opcodes don't really have two- or three-byte opcodes because the map
       ;; is encoded in the VEX/EVEX prefixes, so it can be misleading to list
       ;; their opcode as two or three bytes long.
       (opcode-byte (loghead 8 opcode.op))
       (mnemonic (if (stringp inst.mnemonic)
                     inst.mnemonic
                   (symbol-name inst.mnemonic)))
       (fn-info  (if (and fn-ok? inst.fn)
                     (if (eql (car inst.fn) :NO-INSTRUCTION)
                         "@('NO INSTRUCTION')"
                       (concatenate
                        'string
                        "@(tsee "
                        (str::pretty (car inst.fn) :config *x86isa-printconfig*)
                        ") "
                        (if (cdr inst.fn)
                            (concatenate
                             'string
                             "-- <br/><tt>"
                             (str::pretty (cdr inst.fn)
                                          :config *x86isa-printconfig*)
                             "</tt>")
                          "")))
                   ""))
       (fn-info (if fn-ok?
                    (concatenate
                     'string
                     " <td> " fn-info                 " </td> ")
                  ""))
       ;; --------------------------------------------------
       ;; Constructing extra-info documentation:
       (extra-info (create-extra-info-doc opcode))
       ;; --------------------------------------------------
       ;; Constructing operands' documentation, if necessary:
       (arg-str (if arg-ok? (create-args-doc inst.operands) ""))
       ;; --------------------------------------------------
       (doc-string
        (concatenate
         'string
         "<tr> "
         " <td> " (subseq (str::hexify-width opcode-byte 2) 3 nil) " </td> "
         " <td> " mnemonic                " </td> "
         " <td> " extra-info              " </td> "
                  arg-str
                  fn-info
         "</tr>")))
    doc-string))

(define create-insts-doc-aux ((inst-lst inst-list-p)
                              &key
                              ((fn-ok? booleanp
                                       "Include information about the semantic
                          function in the documentation or not")
                               't)
                              ((arg-ok? booleanp
                                        "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                               'nil))

  :returns (insts-doc-string stringp)

  (if (endp inst-lst)
      ""
    (concatenate
     'string
     (create-inst-doc (car inst-lst) :fn-ok? fn-ok? :arg-ok? arg-ok?)
     (create-insts-doc-aux (cdr inst-lst) :fn-ok? fn-ok? :arg-ok? arg-ok?))))

(define create-insts-doc ((inst-lst inst-list-p)
                          &key
                          ((fn-ok? booleanp
                                   "Include information about the semantic
                          function in the documentation or not")
                           't)
                          ((arg-ok? booleanp
                                    "Include information about the
                          operands (@('inst.operands') field) in the
                          documentation or not")
                           'nil))

  :returns (insts-doc-string stringp)

  (b* ((insts-doc-string (create-insts-doc-aux
                          inst-lst :fn-ok? fn-ok? :arg-ok? arg-ok?))
       (table-header-1 "<th> Opcode </th>")
       (table-header-2 "<th> Mnemonic </th>")
       (table-header-3 "<th> Other Information </th>")
       (table-header-4 (if fn-ok?
                           "<th> Semantic Function </th>"
                         ""))
       (table-header-5 (if arg-ok?
                           "<th> Operands </th>"
                         ""))
       (table-header (concatenate
                      'string "<tr> "
                      table-header-1 table-header-2
                      table-header-3 table-header-4
                      table-header-5
                      " </tr>")))
    (concatenate
     'string
     "<table> " table-header insts-doc-string " </table>")))

(define select-opcode-map ((map-key keywordp))
  :parents (filtering-instructions)
  :guard (member-equal
          map-key
          '(:one-byte
            :two-byte
            :0F-38-three-byte
            :0F-3A-three-byte
            :vex-0F :vex-0F-38 :vex-0F-3A
            :evex-0F :evex-0F-38 :evex-0F-3A))
  :returns (inst-lst inst-list-p :hyp :guard)
  (case map-key
    (:one-byte *one-byte-opcode-map*)
    ((:two-byte :vex-0F :evex-0F) *two-byte-opcode-map*)
    ((:0F-38-three-byte :vex-0F-38 :evex-0F-38) *0F-38-three-byte-opcode-map*)
    ((:0F-3A-three-byte :vex-0F-3A :evex-0F-3A) *0F-3A-three-byte-opcode-map*)))

(make-event
 ;; To generate ALL the instructions, including the unimplemented ones, set
 ;; :fn? to nil in the following forms.
 (b* ((one (create-insts-doc
            (select-insts *one-byte-opcode-map*
                          :get/rem :get
                          :fn? t)))
      (two (create-insts-doc
            (select-insts *two-byte-opcode-map*
                          :get/rem :get
                          :fn? t)))
      (three-1 (create-insts-doc
                (select-insts *0F-38-three-byte-opcode-map*
                              :get/rem :get
                              :fn? t)))
      (three-2 (create-insts-doc
                (select-insts *0F-3A-three-byte-opcode-map*
                              :get/rem :get
                              :fn? t))))
   `(progn
      (defsection one-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is one byte long"
        :long ,one)
      (defsection two-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is two bytes long,
       beginning with @('0F'); includes VEX/EVEX instructions too"
        :long ,two)
      (defsection 0F-38-three-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is three bytes
       long, beginning with @('0F_38'); includes VEX/EVEX instructions too"
        :long ,three-1)
      (defsection 0F-3A-three-byte-opcodes-map
        :parents (implemented-opcodes)
        :short "List of <b>implemented</b> instructions whose opcode is three bytes
       long, beginning with @('0F_3A'); includes VEX/EVEX instructions too"
        :long ,three-2))))


(defsection implemented-opcodes
  :parents (x86isa instructions x86-decoder opcode-maps)
  :short "Intel Opcodes Supported in @('x86isa')"
  :long
  "<p>We support decoding of all the x86 instructions in the one-, two-, and
 three-byte opcode maps, including the AVX/AVX2/AVX512 extensions.  However, a
 fraction of those are actually implemented in this model --- when we say
 <i>implemented</i> instructions, we mean instructions that have a semantic function
 that models its effects on the machine's state.</p>

 <p>For a listing of all such supported instructions, see @(see
 one-byte-opcodes-map), @(see two-byte-opcodes-map), @(see
 0f-38-three-byte-opcodes-map), and @(see 0f-3a-three-byte-opcodes-map).</p>

 <p>For a readable version of all the opcode maps, see constants like
  @('*pre-one-byte-opcode-map*') in the book @('inst-listing.lisp').  These are
  the constants to edit in order to add new instructions, etc. in the future.
  The dispatch, modr/m and prefixes computation, and generation of
  documentation is done automatically from these constants.</p>")

;; ----------------------------------------------------------------------
