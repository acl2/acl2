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

(in-package "X86ISA")

(include-book "sys-view/marking-view-top" :dir :proof-utils)

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/signed-byte-p" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; ======================================================================

;; Introducing the system-level program:

;; Note this is not exactly tools/execution/examples/zeroCopy/modifyPagingEntry.c
;; It has been patched to add an invlpg instruction, without which this program
;; is incorrect. This program lacked that before and was proven correct on a
;; previous version of the model that didn't model any TLB semantics. Rather than
;; modifying and recompiling the C code, I patched the binary because I wanted to
;; make sure that the binary changed as little as possible so that I could minimize the
;; work necessary to fix the proofs. I don't know what compiler was used to compile
;; this code initially, and a modern compiler would likely generate significantly
;; different code.

;; Some oddities: One would expect the stack to be grown at the start of
;; the program. However, it appears the compiler decided to take advantage of the
;; redzone (a region immediately past the stack pointer that the calling convention
;; guarantees will be preserved by interrupt handlers, etc.). The compiler eliminated
;; all use of the stack except where it was forced to use it due to the inline asm. One
;; would expect it to use [rsp - 0x8] (and indeed modern gcc does), but it chose to use
;; [rsp - 0x18]. Thus, the only parts of the stack we care about are the 8 byte regions
;; at [rsp - 0x18] and [rsp] since the former is used to store cr3 briefly and the
;; latter is used for the return pointer.

;; ┌ 257: fcn.00000000 (int64_t arg1, int64_t arg2);
;; │           ; arg int64_t arg1 @ rdi
;; │           ; arg int64_t arg2 @ rsi
;; │           0x00000000      0f20d8         mov rax, cr3
;; │           0x00000003      48894424e8     mov qword [rsp - 0x18], rax
;; │           0x00000008      488b5424e8     mov rdx, qword [rsp - 0x18]
;; │           0x0000000d      4889f8         mov rax, rdi                ; arg1
;; │           0x00000010      48c1e824       shr rax, 0x24
;; │           0x00000014      25f80f0000     and eax, 0xff8              ; 4088
;; │           0x00000019      4881e200f0..   and rdx, 0xfffffffffffff000
;; │           0x00000020      4809d0         or rax, rdx
;; │           0x00000023      488b00         mov rax, qword [rax]
;; │           0x00000026      a801           test al, 1
;; │       ┌─< 0x00000028      0f84d2000000   je 0x100
;; │       │   0x0000002e      48c1e80c       shr rax, 0xc
;; │       │   0x00000032      49b8ffffff..   movabs r8, 0xffffffffff     ; 1099511627775
;; │       │   0x0000003c      4889f9         mov rcx, rdi                ; arg1
;; │       │   0x0000003f      4c21c0         and rax, r8
;; │       │   0x00000042      48c1e91b       shr rcx, 0x1b
;; │       │   0x00000046      81e1f80f0000   and ecx, 0xff8              ; 4088
;; │       │   0x0000004c      48c1e00c       shl rax, 0xc
;; │       │   0x00000050      4809c8         or rax, rcx
;; │       │   0x00000053      488b00         mov rax, qword [rax]
;; │       │   0x00000056      4889c1         mov rcx, rax
;; │       │   0x00000059      81e181000000   and ecx, 0x81
;; │       │   0x0000005f      4881f98100..   cmp rcx, 0x81
;; │      ┌──< 0x00000066      0f8594000000   jne 0x100
;; │      ││   0x0000006c      4889f1         mov rcx, rsi                ; arg2
;; │      ││   0x0000006f      49b9000000..   movabs r9, 0xfffffc0000000
;; │      ││   0x00000079      48c1e924       shr rcx, 0x24
;; │      ││   0x0000007d      4921c1         and r9, rax
;; │      ││   0x00000080      81e1f80f0000   and ecx, 0xff8              ; 4088
;; │      ││   0x00000086      4809d1         or rcx, rdx
;; │      ││   0x00000089      488b01         mov rax, qword [rcx]
;; │      ││   0x0000008c      a801           test al, 1
;; │     ┌───< 0x0000008e      7470           je 0x100
;; │     │││   0x00000090      48c1e80c       shr rax, 0xc
;; │     │││   0x00000094      4889f2         mov rdx, rsi                ; arg2
;; │     │││   0x00000097      4c21c0         and rax, r8
;; │     │││   0x0000009a      48c1ea1b       shr rdx, 0x1b
;; │     │││   0x0000009e      81e2f80f0000   and edx, 0xff8              ; 4088
;; │     │││   0x000000a4      48c1e00c       shl rax, 0xc
;; │     │││   0x000000a8      4809d0         or rax, rdx
;; │     │││   0x000000ab      48baffffff..   movabs rdx, 0xfff000003fffffff
;; │     │││   0x000000b5      482310         and rdx, qword [rax]
;; │     │││   0x000000b8      4c09ca         or rdx, r9
;; │     │││   0x000000bb      488910         mov qword [rax], rdx
;; │     │││   0x000000be      0f013e         invlpg byte [rsi]
;; │     │││   0x000000c1      4889d0         mov rax, rdx
;; │     │││   0x000000c4      2581000000     and eax, 0x81
;; │     │││   0x000000c9      483d81000000   cmp rax, 0x81
;; │    ┌────< 0x000000cf      7532           jne 0x103
;; │    ││││   0x000000d1      48b8000000..   movabs rax, 0xfffffc0000000
;; │    ││││   0x000000db      81e6ffffff3f   and esi, 0x3fffffff
;; │    ││││   0x000000e1      81e7ffffff3f   and edi, 0x3fffffff
;; │    ││││   0x000000e7      4821c2         and rdx, rax
;; │    ││││   0x000000ea      4c09cf         or rdi, r9
;; │    ││││   0x000000ed      31c0           xor eax, eax
;; │    ││││   0x000000ef      4809f2         or rdx, rsi
;; │    ││││   0x000000f2      4839d7         cmp rdi, rdx
;; │    ││││   0x000000f5      0f94c0         sete al
;; │    ││││   0x000000f8      c3             ret
;;      ││││   0x000000f9      0f1f800000..   nop dword [rax]
;; │    ││││   ; CODE XREFS from fcn.00000000 @ 0x28(x), 0x66(x), 0x8e(x)
;; │    │└└└─> 0x00000100      48c7c0ffff..   mov rax, 0xffffffffffffffff
;; └           0x00000107      c3             ret
;;             0x00000108      0f1f840000..   nop dword [rax + rax]

(defconst *rewire_dst_to_src*
          '(#xF #x20 #xD8 #x48 #x89 #x44 #x24
            #xE8 #x48 #x8B #x54 #x24 #xE8 #x48
            #x89 #xF8 #x48 #xC1 #xE8 #x24 #x25
            #xF8 #xF #x0 #x0 #x48 #x81 #xE2 #x0
            #xF0 #xFF #xFF #x48 #x9 #xD0 #x48
            #x8B #x0 #xA8 #x1 #xF #x84 #xD2 #x0
            #x0 #x0 #x48 #xC1 #xE8 #xC #x49 #xB8
            #xFF #xFF #xFF #xFF #xFF #x0 #x0 #x0
            #x48 #x89 #xF9 #x4C #x21 #xC0 #x48
            #xC1 #xE9 #x1B #x81 #xE1 #xF8 #xF
            #x0 #x0 #x48 #xC1 #xE0 #xC #x48 #x9
            #xC8 #x48 #x8B #x0 #x48 #x89 #xC1
            #x81 #xE1 #x81 #x0 #x0 #x0 #x48 #x81
            #xF9 #x81 #x0 #x0 #x0 #xF #x85 #x94
            #x0 #x0 #x0 #x48 #x89 #xF1 #x49 #xB9
            #x0 #x0 #x0 #xC0 #xFF #xFF #xF #x0
            #x48 #xC1 #xE9 #x24 #x49 #x21 #xC1
            #x81 #xE1 #xF8 #xF #x0 #x0 #x48 #x9
            #xD1 #x48 #x8B #x1 #xA8 #x1 #x74
            #x70 #x48 #xC1 #xE8 #xC #x48 #x89
            #xF2 #x4C #x21 #xC0 #x48 #xC1 #xEA
            #x1B #x81 #xE2 #xF8 #xF #x0 #x0 #x48
            #xC1 #xE0 #xC #x48 #x9 #xD0 #x48 #xBA
            #xFF #xFF #xFF #x3F #x0 #x0 #xF0 #xFF
            #x48 #x23 #x10 #x4C #x9 #xCA #x48
            #x89 #x10 #xF #x1 #x3E #x48 #x89 #xD0
            #x25 #x81 #x0 #x0 #x0 #x48 #x3D #x81
            #x0 #x0 #x0 #x75 #x32 #x48 #xB8 #x0
            #x0 #x0 #xC0 #xFF #xFF #xF #x0 #x81
            #xE6 #xFF #xFF #xFF #x3F #x81 #xE7
            #xFF #xFF #xFF #x3F #x48 #x21 #xC2
            #x4C #x9 #xCF #x31 #xC0 #x48 #x9 #xF2
            #x48 #x39 #xD7 #xF #x94 #xC0 #xC3
            #xF #x1F #x80 #x0 #x0 #x0 #x0 #x48
            #xC7 #xC0 #xFF #xFF #xFF #xFF #xC3
            #xF #x1F #x84 #x0 #x0 #x0 #x0 #x0))


(defconst *rewire_dst_to_src-len* (len *rewire_dst_to_src*))

(defun rewire_dst_to_src-clk-1-to-45 () 45)

(defun rewire_dst_to_src-clk-46-to-59 () 14)

(defun rewire_dst_to_src-clk ()
  (clk+ (rewire_dst_to_src-clk-1-to-45) (rewire_dst_to_src-clk-46-to-59)))

;; ======================================================================

;; Control printing:
(acl2::add-untranslate-pattern-function
 (program-at (xr :rip nil x86)
             '(15 32 216 72 137 68 36 232 72 139 84 36 232
                  72 137 248 72 193 232 36 37 248 15 0 0
                  72 129 226 0 240 255 255 72 9 208 72 139
                  0 168 1 15 132 210 0 0 0 72 193 232 12
                  73 184 255 255 255 255 255 0 0 0 72 137
                  249 76 33 192 72 193 233 27 129 225 248
                  15 0 0 72 193 224 12 72 9 200 72 139 0
                  72 137 193 129 225 129 0 0 0 72 129 249
                  129 0 0 0 15 133 148 0 0 0 72 137 241
                  73 185 0 0 0 192 255 255 15 0 72 193 233
                  36 73 33 193 129 225 248 15 0 0 72 9 209
                  72 139 1 168 1 116 112 72 193 232 12 72
                  137 242 76 33 192 72 193 234 27 129 226
                  248 15 0 0 72 193 224 12 72 9 208 72 186
                  255 255 255 63 0 0 240 255 72 35 16 76
                  9 202 72 137 16 72 137 208 37 129 0 0 0
                  72 61 129 0 0 0 117 50 72 184 0 0 0 192
                  255 255 15 0 129 230 255 255 255 63 129
                  231 255 255 255 63 72 33 194 76 9 207
                  49 192 72 9 242 72 57 215 15 148 192 195
                  102 46 15 31 132 0 0 0 0 0 72 199 192
                  255 255 255 255 195 15 31 132 0 0 0 0 0)
             x86)
 (program-at (xr :rip nil x86)
             *rewire_dst_to_src*
             x86))

(acl2::add-untranslate-pattern-function
 (program-at-alt (xr :rip nil x86)
                 '(15 32 216 72 137 68 36 232 72 139 84 36 232
                      72 137 248 72 193 232 36 37 248 15 0 0
                      72 129 226 0 240 255 255 72 9 208 72 139
                      0 168 1 15 132 210 0 0 0 72 193 232 12
                      73 184 255 255 255 255 255 0 0 0 72 137
                      249 76 33 192 72 193 233 27 129 225 248
                      15 0 0 72 193 224 12 72 9 200 72 139 0
                      72 137 193 129 225 129 0 0 0 72 129 249
                      129 0 0 0 15 133 148 0 0 0 72 137 241
                      73 185 0 0 0 192 255 255 15 0 72 193 233
                      36 73 33 193 129 225 248 15 0 0 72 9 209
                      72 139 1 168 1 116 112 72 193 232 12 72
                      137 242 76 33 192 72 193 234 27 129 226
                      248 15 0 0 72 193 224 12 72 9 208 72 186
                      255 255 255 63 0 0 240 255 72 35 16 76
                      9 202 72 137 16 72 137 208 37 129 0 0 0
                      72 61 129 0 0 0 117 50 72 184 0 0 0 192
                      255 255 15 0 129 230 255 255 255 63 129
                      231 255 255 255 63 72 33 194 76 9 207
                      49 192 72 9 242 72 57 215 15 148 192 195
                      102 46 15 31 132 0 0 0 0 0 72 199 192
                      255 255 255 255 195 15 31 132 0 0 0 0 0)
                 x86)
 (program-at-alt (xr :rip nil x86)
                 *rewire_dst_to_src*
                 x86))

;; ======================================================================

(defthm disjoint-p$-implies-disjoint-p
  (implies (disjoint-p$ x y)
           (disjoint-p x y))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$) ()))))

;; ======================================================================

;; Lemmas to deal with some tedious arithmetic stuff:

(defthm loghead-negative
  (implies (and (syntaxp (and (quotep n)
                              (< (cadr n) 0)))
                (< n 0)
                (integerp n))
           (equal (loghead n x) 0)))

(defthm unsigned-byte-p-1-bool->bit
  (unsigned-byte-p 1 (acl2::bool->bit x)))

(defthm-using-gl canonical-address-p-of-lin-addr+7
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 3 lin-addr) 0))
  :concl (canonical-address-p (+ 7 lin-addr))
  :g-bindings
  (gl::auto-bindings (:nat lin-addr 64)))

(defun-nx pdpt-base-addr (lin-addr x86)
  ;; Note that an existing function page-dir-ptr-table-base-addr is
  ;; defined in terms of rm-low-64, and hence, doesn't help for this
  ;; proof.
  (ash (loghead 40 (logtail
                    12
                    (mv-nth 1 (rb 8
                                  (pml4-table-entry-addr
                                   lin-addr (pml4-table-base-addr x86))
                                  :r x86))))
       12))

;; The following is really a consequence of keeping
;; pdpt-base-addr enabled.
(defthm unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
  (implies (unsigned-byte-p 64 x)
           (unsigned-byte-p 52 (ash (loghead 40 (logtail 12 x)) 12))))

(defthm-using-gl pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (equal (pml4-table-entry-addr v-addr (ash (loghead 40 (logtail 12 cr3)) 12))
                (logior (logand -4096 (logext 64 cr3))
                        (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(defthm-using-gl canonical-address-p-pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (canonical-address-p
          (logior (logand -4096 (logext 64 cr3))
                  (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(defthm-using-gl remove-logext-from-pml4-table-entry-addr-to-C-program-optimized-form-1
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (logand 4088 (loghead 28 (logtail 36 v-addr))))
                (logand 4088 (loghead 28 (logtail 36 v-addr))))
  :g-bindings
  (gl::auto-bindings (:nat v-addr 64)))

(defthm-using-gl remove-logext-from-pml4-table-entry-addr-to-C-program-optimized-form-2
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (loghead 28 (logtail 36 v-addr)))
                (loghead 28 (logtail 36 v-addr)))
  :g-bindings
  (gl::auto-bindings (:nat v-addr 64)))

(defthm-using-gl page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (loghead 12 base-addr) 0)
            (unsigned-byte-p #.*physical-address-size* base-addr))
  :concl (equal (page-dir-ptr-table-entry-addr v-addr base-addr)
                (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                        base-addr))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat base-addr 64))))

;; (defthm canonical-address-p-page-dir-ptr-table-entry-addr-to-C-program-optimized-form
;;   (implies (logbitp 7 (mv-nth 1 (rb
;;                                  8
;;                                  (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
;;                                          (ash (loghead 40 (logtail 12 val)) 12))
;;                                  :r x86)))
;;            (canonical-address-p
;;             (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
;;                     (ash (loghead 40 (logtail 12 val)) 12)))))

(defthm-using-gl remove-logext-from-page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (loghead 32 (logtail 27 v-addr)))
                (loghead 32 (logtail 27 v-addr)))
  :g-bindings
  (gl::auto-bindings (:nat v-addr 64)))

(defthm-using-gl page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-1
  :hyp (and (equal (part-select entry :low 7 :width 1) 1)
            (equal (part-select entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 entry))
  :concl (equal (zf-spec
                 (loghead 64 (+ -129 (logand 129 (logext 64 (loghead 32 entry))))))
                1)
  :g-bindings
  (gl::auto-bindings (:nat entry 64)))

(defthm-using-gl page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-2
  :hyp (and (equal (part-select source-entry :low 7 :width 1) 1)
            (equal (part-select source-entry :low 0 :width 1) 1)
            (equal (part-select destination-entry :low 7 :width 1) 1)
            (equal (part-select destination-entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 source-entry)
            (unsigned-byte-p 64 destination-entry))
  :concl (equal (zf-spec
                 (loghead 64
                          (+
                           -129
                           (logand 129 (logior
                                        (logext 64 (loghead 30 destination-entry))
                                        (logand 3221225472 (logext 64 (loghead 32 source-entry))))))))
                1)
  :g-bindings
  (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

(defthm-using-gl page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-3
  :hyp (and (unsigned-byte-p 64 source-entry)
            (unsigned-byte-p 64 destination-entry))
  :concl (equal
          (zf-spec
           (loghead 64 (+ (logand 4503598553628672 (logext 64 source-entry))
                          (- (logand 4503598553628672
                                     (logior (logand -4503598553628673 (logext 64 destination-entry))
                                             (logand 4503598553628672 (logext 64 source-entry))))))))
          1)
  :g-bindings
  (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

(defthm-using-gl remove-logext-from-ash-loghead-40-expr
  :hyp (unsigned-byte-p 64 n)
  :concl (equal (logext 64 (ash (loghead 40 (logtail 12 n)) 12))
                (ash (loghead 40 (logtail 12 n)) 12))
  :g-bindings
  (gl::auto-bindings (:nat n 64)))

(defthm-using-gl remove-logext-from-logand-and-ctri
  :hyp (unsigned-byte-p 64 n)
  :concl (equal (logext 64 (logand -4096 (logext 64 n)))
                (logand -4096 (logext 64 n)))
  :g-bindings
  (gl::auto-bindings (:nat n 64)))

(def-gl-thm dest-pdpte-is-of-physical-address-size
  :hyp (and (signed-byte-p 64 reg)
            (unsigned-byte-p 64 val))
  :concl (unsigned-byte-p
          #.*physical-address-size*
          (logior (logand 4088 (loghead 32 (logtail 27 reg)))
                  (ash (loghead 40 (logtail 12 val)) 12)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat reg 64) (:nat val 64))))

(def-gl-thm unsigned-byte-p-64-of-dest-pdpte-modified-value
  :hyp (and (unsigned-byte-p 64 val-1)
            (unsigned-byte-p 64 val-2))
  :concl (unsigned-byte-p 64 (logior (logand 18442240475155922943 val-1)
                                     (logand 4503598553628672 val-2)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat val-1 64) (:nat val-2 64))))

;; ======================================================================

(def-ruleset rewire_dst_to_src-disable
  '((:type-prescription natp-pml4-table-entry-addr)
    (:rewrite acl2::consp-when-member-equal-of-atom-listp)
    (:rewrite ia32e-la-to-pa-xw-state)
    (:rewrite r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
    (:linear adding-7-to-pml4-table-entry-addr)
    (:linear *physical-address-size*p-pml4-table-entry-addr)
    (:rewrite acl2::equal-of-booleans-rewrite)
    (:rewrite loghead-unequal)
    (:rewrite negative-logand-to-positive-logand-with-integerp-x)
    (:definition combine-bytes)
    (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
    (:rewrite xr-ia32e-la-to-pa)
    (:rewrite acl2::nfix-when-not-natp)
    (:rewrite acl2::nfix-when-natp)
    ;; (:linear combine-bytes-size-for-rml64-app-view)
    (:rewrite acl2::natp-when-integerp)
    (:rewrite acl2::natp-when-gte-0)
    (:rewrite 4k-aligned-physical-address-helper)
    (:rewrite bitops::signed-byte-p-of-logtail)
    (:linear adding-7-to-page-dir-ptr-table-entry-addr)
    (:linear *physical-address-size*p-page-dir-ptr-table-entry-addr)
    (:type-prescription adding-7-to-pml4-table-entry-addr)
    (:type-prescription adding-7-to-page-dir-ptr-table-entry-addr)
    (:rewrite acl2::signed-byte-p-logext)
    (:type-prescription booleanp)
    (:rewrite loghead-64-n64-to-i64-canonical-address)
    (:type-prescription pml4-table-base-addr)
    (:rewrite get-prefixes-opener-lemma-group-4-prefix)
    (:rewrite get-prefixes-opener-lemma-group-3-prefix)
    (:rewrite get-prefixes-opener-lemma-group-2-prefix)
    (:rewrite get-prefixes-opener-lemma-group-1-prefix)
    (:rewrite get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-view)
    (:rewrite get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-view)
    (:rewrite get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-view)
    (:rewrite get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-view)
    (:definition member-p)
    (:linear unsigned-byte-p-of-combine-bytes)
    (:type-prescription acl2::|x < y  =>  0 < -x+y|)
    (:rewrite default-+-2)
    (:rewrite acl2::natp-rw)
    (:rewrite ia32e-la-to-pa-lower-12-bits)
    (:rewrite default-+-1)
    (:rewrite acl2::ash-0)
    (:rewrite acl2::zip-open)
    (:rewrite loghead-of-non-integerp)
    (:rewrite canonical-address-p-limits-thm-3)
    (:rewrite canonical-address-p-limits-thm-2)
    (:rewrite zf-spec-thm)
    (:linear acl2::loghead-upper-bound)
    (:linear bitops::logior-<-0-linear-2)
    (:linear size-of-combine-bytes)
    (:rewrite disjoint-p-subset-p)
    (:definition binary-append)
    (:rewrite member-p-of-subset-is-member-p-of-superset)
    (:rewrite member-p-cdr)
    (:rewrite bitops::unsigned-byte-p-incr)
    (:rewrite acl2::difference-unsigned-byte-p)
    (:rewrite acl2::append-when-not-consp)
    (:rewrite acl2::ifix-when-not-integerp)
    (:rewrite bitops::basic-unsigned-byte-p-of-+)
    (:rewrite disjoint-p-append-1)
    (:rewrite default-<-1)
    (:rewrite default-car)
    (:rewrite default-cdr)
    (:meta acl2::cancel_plus-lessp-correct)
    (:definition nthcdr)
    (:rewrite subset-p-cdr-y)
    (:rewrite ia32e-la-to-pa-lower-12-bits-value-of-address-when-error)
    (:rewrite default-<-2)
    (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
    (:meta acl2::cancel_plus-equal-correct)
    (:definition nth)
    (:rewrite subset-p-reflexive)
    (:meta acl2::cancel_times-equal-correct)
    (:rewrite set::sets-are-true-lists)
    (:definition true-listp)
    (:rewrite cdr-append-is-append-cdr)
    (:type-prescription bitops::logtail-natp)
    (:rewrite subset-p-cdr-x)
    (:rewrite bitops::logbitp-nonzero-of-bit)
    (:rewrite set::nonempty-means-set)
    (:type-prescription xw)
    (:type-prescription natp-combine-bytes)
    (:type-prescription true-listp)
    (:rewrite unsigned-byte-p-of-logtail)
    (:rewrite bitops::logbitp-when-bitmaskp)
    (:type-prescription all-xlation-governing-entries-paddrs)
    (:type-prescription set::setp-type)
    (:type-prescription set::emptyp-type)
    (:rewrite acl2::equal-constant-+)
    (:definition byte-listp)
    (:rewrite unsigned-byte-p-of-ash)
    (:rewrite bitops::normalize-logbitp-when-mods-equal)
    (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
    (:rewrite car-of-append)
    (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
    (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
    (:type-prescription consp-append)
    (:type-prescription bitops::logand-natp-type-2)
    (:definition acons)
    (:rewrite unsigned-byte-p-of-combine-bytes)
    (:rewrite unsigned-byte-p-of-logior)
    (:type-prescription natp)
    (:rewrite set::in-set)
    (:type-prescription acl2::logtail-type)
    (:rewrite acl2::member-of-cons)
    (:rewrite rationalp-implies-acl2-numberp)
    (:type-prescription bitops::ash-natp-type)
    (:type-prescription combine-bytes)
    (:definition n08p$inline)
    (:definition len)
    (:rewrite xr-and-ia32e-la-to-pa-page-directory-in-non-marking-view)
    (:rewrite bitops::logsquash-of-loghead-zero)
    (:rewrite default-unary-minus)
    (:type-prescription acl2::true-listp-append)
    (:linear bitops::upper-bound-of-logand . 2)
    (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
    (:rewrite logand-redundant)
    (:linear bitops::logand->=-0-linear-2)
    (:linear bitops::upper-bound-of-logand . 1)
    (:linear bitops::logand->=-0-linear-1)
    (:linear mv-nth-1-idiv-spec)
    (:linear mv-nth-1-div-spec)
    (:rewrite unsigned-byte-p-of-logand-2)
    (:linear acl2::expt->-1)
    (:rewrite acl2::unsigned-byte-p-loghead)
    (:type-prescription zip)
    (:linear bitops::logand-<-0-linear)
    (:rewrite bitops::logior-fold-consts)
    (:linear <=-logior)
    (:linear member-p-pos-value)
    (:linear member-p-pos-1-value)
    (:linear bitops::logior->=-0-linear)
    (:rewrite no-duplicates-p-and-append)
    (:rewrite acl2::subsetp-member . 2)
    (:rewrite acl2::subsetp-member . 1)
    (:type-prescription wr32$inline)
    (:rewrite unsigned-byte-p-of-logand-1)
    (:rewrite subset-p-cons-member-p-lemma)
    (:rewrite member-p-of-not-a-consp)
    (:rewrite get-prefixes-opener-lemma-zero-cnt)
    (:rewrite acl2::expt-with-violated-guards)
    (:rewrite bitops::basic-signed-byte-p-of-+)
    (:type-prescription ash)
    (:linear acl2::expt-is-increasing-for-base>1)
    (:definition member-equal)
    (:linear bitops::logior-<-0-linear-1)
    (:linear bitops::upper-bound-of-logior-for-naturals)
    (:linear bitops::expt-2-lower-bound-by-logbitp)
    open-qword-paddr-list
    cdr-create-canonical-address-list
    subset-p-cons-2
    (:definition addr-range)
    (:rewrite loghead-negative)
    (:rewrite member-p-cons)
    (:rewrite consp-of-create-canonical-address-list)
    (:rewrite car-create-canonical-address-list)
    (:type-prescription gather-all-paging-structure-qword-addresses)
    (:rewrite neg-addr-range=nil)
    (:definition no-duplicates-p)
    (:rewrite acl2::remove-duplicates-equal-when-atom)
    (:rewrite consp-mv-nth-1-las-to-pas)
    (:rewrite subset-p-of-nil)
    (:rewrite
     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
    (:rewrite get-prefixes-alt-opener-lemma-zero-cnt)
    (:rewrite member-p-of-nil)
    (:type-prescription bitops::part-select-width-low$inline)
    (:rewrite acl2::alistp-when-hons-duplicity-alist-p)
    (:rewrite
     mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
    (:rewrite car-mv-nth-1-las-to-pas)
    (:rewrite acl2::zp-when-integerp)
    (:type-prescription acl2::hons-duplicity-alist-p)
    (:type-prescription consp-mv-nth-1-las-to-pas)
    (:rewrite gl::nonnil-symbol-listp-true-listp)
    (:rewrite subset-p-two-create-canonical-address-lists-same-base-address)
    (:rewrite ia32e-la-to-pa-in-app-view)
    (:rewrite acl2::zp-when-gt-0)
    (:rewrite acl2::logtail-identity)
    (:type-prescription acl2::nonnil-symbol-listp)
    (:rewrite acl2::hons-duplicity-alist-p-when-not-consp)
    (:rewrite acl2::consp-of-car-when-atom-listp)
    (:rewrite acl2::logext-identity)
    (:rewrite member-p-and-mult-8-qword-paddr-listp)
    (:rewrite cdr-canonical-address-listp)
    (:rewrite x86-run-halted)
    x86-fetch-decode-execute-opener
    mv-nth-1-ia32e-la-to-pa-when-error
    mv-nth-1-las-to-pas-when-error
    bitops::logand-with-negated-bitmask
    xlate-equiv-memory-and-xr-mem-from-rest-of-memory
    disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
    unsigned-byte-p))

(def-ruleset rewire_dst_to_src-disable-more
  '(mv-nth-0-las-to-pas-subset-p
    (:rewrite disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
    (:type-prescription rm-low-64-logand-logior-helper-1)
    (:type-prescription n64p$inline)
    (:definition strip-cars)
    (:rewrite bitops::signed-byte-p-monotonicity)
    (:linear mv-nth-1-gpr-sbb-spec-8)
    (:linear mv-nth-1-gpr-add-spec-8)
    (:linear mv-nth-1-gpr-adc-spec-8)
    (:rewrite acl2::subsetp-member . 3)
    (:rewrite acl2::zp-open)
    (:type-prescription subsetp-equal)
    (:type-prescription acl2::|x < y  =>  0 < y-x|)
    (:linear mv-nth-1-gpr-xor-spec-8)
    (:linear acl2::index-of-<-len)
    (:type-prescription x86-step-unimplemented)
    (:type-prescription !rgfi-size$inline)
    (:rewrite canonical-address-p-limits-thm-4)
    (:linear mv-nth-2-gpr-sbb-spec-8)
    (:linear mv-nth-2-gpr-add-spec-8)
    (:linear mv-nth-2-gpr-adc-spec-8)
    (:rewrite bitops::basic-signed-byte-p-of-binary-minus)
    (:rewrite acl2::subsetp-member . 4)
    (:rewrite acl2::member-when-atom)
    (:linear mv-nth-2-gpr-xor-spec-8)
    (:type-prescription n08p$inline)
    (:rewrite cdr-strip-cars-is-strip-cars-cdr)
    (:type-prescription strip-cars)
    (:rewrite signed-byte-p-limits-thm)
    (:rewrite canonical-address-p-and-signed-byte-p-64p-limits-1)
    (:rewrite bitops::logbitp-of-loghead-out-of-bounds)
    (:type-prescription bitops::natp-part-install-width-low)))

;; ======================================================================

;; Assumptions for the effects theorems:

(defun-nx x86-state-okp (x86)
  (and
   (x86p x86)
   ;; We will not set the interrupt flag after
   ;; executing the next instruction
   (not (set-interrupt-flag-next x86))
   (equal (xr :ms nil x86) nil)
   (equal (xr :fault nil x86) nil)
   (64-bit-modep x86)
   (not (alignment-checking-enabled-p x86))
   (not (app-view x86))
   (marking-view x86)
   ;; The peripherals are disabled
   (not (enable-peripherals x86))
   ;; Current Privilege Level == 0.
   (equal (cpl x86) 0)
   ;; CR3's reserved bits must be zero (MBZ).
   (equal (logtail 40 (ctri *cr3* x86)) 0)))

(defun-nx program-ok-p (x86)
  (and
   ;; Program addresses are canonical.
   (canonical-address-p (+ *rewire_dst_to_src-len* (xr :rip nil x86)))
   ;; Program is located at linear address (rip x86) in the memory.
   (program-at (xr :rip nil x86) *rewire_dst_to_src* x86)
   ;; We have a consistent tlb for the program memory
   (tlb-consistent-n *rewire_dst_to_src-len* (rip x86) :x x86)
   ;; No errors encountered while translating the linear addresses
   ;; where the program is located.
   (not (mv-nth 0 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86)))
   ;; The following precondition was not required in the non-marking
   ;; view: physical addresses corresponding to the program are
   ;; disjoint from the paging structure physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))))

(defun-nx program-alt-ok-p (x86)
  (and
   ;; Program addresses are canonical.
   (canonical-address-p (+ *rewire_dst_to_src-len* (xr :rip nil x86)))
   ;; We have a consistent tlb for the program memory
   (tlb-consistent-n (len *rewire_dst_to_src*) (rip x86) :x x86)
   ;; Program is located at linear address (rip x86) in the memory.
   (program-at-alt (xr :rip nil x86) *rewire_dst_to_src* x86)
   ;; No errors encountered while translating the linear addresses
   ;; where the program is located.
   (not (mv-nth 0 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86)))
   ;; The following precondition was not required in the non-marking
   ;; view: physical addresses corresponding to the program are
   ;; disjoint from the paging structure physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))))

(defthmd program-alt-ok-p-and-program-ok-p
  (implies (x86-state-okp x86)
           (equal (program-alt-ok-p x86)
                  (program-ok-p x86)))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(defun-nx stack-ok-p (x86)
  (and
   ;; Stack addresses are canonical.
   (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
   (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
   ;; We have a consistent tlb for the stack memory
   (tlb-consistent-n 8 (+ -24 (xr :rgf *rsp* x86)) :r x86)
   (tlb-consistent-n 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)
   ;; Writing to stack: No errors encountered while translating the
   ;; linear addresses corresponding to the program stack.
   (not (mv-nth 0 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; Reading from stack: No errors encountered while translating the
   ;; linear addresses corresponding to the stack.
   (not (mv-nth 0 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :r x86)))
   ;; Reading from stack: The stack is located in a contiguous region
   ;; of memory --- no overlaps among physical addresses of the stack.
   ;; I need this hypothesis so that the lemma
   ;; rb-wb-equal-in-sys-view can fire successfully.
   (no-duplicates-p
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :r x86)))

   ;; The following precondition was not required in the non-marking
   ;; view: physical addresses corresponding to the stack are disjoint
   ;; from the paging structures physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))))

(defun-nx program-and-stack-no-interfere-p (x86)
  (and
   ;; The physical addresses corresponding to the program and stack
   ;; are disjoint.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86)))

   ;; The following precondition was not required in the non-marking
   ;; view: the stack physical addresses are disjoint from the
   ;; program's translation-governing addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (all-xlation-governing-entries-paddrs
     *rewire_dst_to_src-len* (xr :rip nil x86) x86))))

(defun-nx source-addresses-ok-p (x86)
  (and
   ;; TLB is consistent for source addresses
   (tlb-consistent-n *2^30* (xr :rgf *rdi* x86) :r x86)
   ;; Source addresses are canonical.
   (canonical-address-p (xr :rgf *rdi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
   ;; Source address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
   ;; No errors encountered while translating the source linear
   ;; addresses.
   (not (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86)))))

(defun-nx source-PML4TE-ok-p (x86)
  (and
    ;; PML4TE addresses have consistent tlb
   (tlb-consistent-n 8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)) :r x86)
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0
                (las-to-pas
                 8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
                 :r x86)))
   ;; PML4TE has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (mv-nth
      1
      (rb
       8
       (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
       :r x86)))
    1)
   ;; The PML4TE physical addresses are disjoint from their own
   ;; translation-governing addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))))

(defun-nx source-PDPTE-ok-p (x86)
  (and
   ;; PDPTE addresses have consistent tlb
   (tlb-consistent-n 8 (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
                                                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     :r x86)
   ;; PDPTE linear addresses are canonical.
   (canonical-address-p
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rdi* x86)
     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
   (canonical-address-p
    (+ 7 (page-dir-ptr-table-entry-addr
          (xr :rgf *rdi* x86)
          (pdpt-base-addr (xr :rgf *rdi* x86) x86))))
   ;; No errors encountered while translating the PDPTE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   8
                   (page-dir-ptr-table-entry-addr
                    (xr :rgf *rdi* x86)
                    (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                   :r x86)))
   ;; PDPTE does not have the P or PS bit cleared (i.e., the
   ;; entry is present and it points to a 1G page).
   (equal (part-select
           (mv-nth 1
                   (rb
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rdi* x86)
                     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                    :r x86))
           :low 0 :width 1)
          1)
   (equal (part-select
           (mv-nth 1
                   (rb
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rdi* x86)
                     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                    :r x86))
           :low 7 :width 1)
          1)
   ;; The source PDPTE physical addresses are disjoint from their own
   ;; translation-governing addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
     x86))))

(defun-nx source-PML4TE-and-stack-no-interfere-p (x86)
  (and
   ;; The stack physical addresses are disjoint from the PML4TE
   ;; physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r x86)))
   ;; The source PML4TE physical addresses are disjoint from the
   ;; translation-governing addresses of the stack.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (+ -24 (xr :rgf *rsp* x86))
     x86))
   ;; The stack physical addresses are disjoint from the
   ;; translation-governing addresses of the source PML4TE.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))))

(defun-nx source-PML4TE-and-program-no-interfere-p (x86)
  ;; The source PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    *rewire_dst_to_src-len* (xr :rip nil x86) x86)))

(defun-nx source-PDPTE-and-stack-no-interfere-p (x86)
  (and
   ;; The stack physical addresses are disjoint from the source PDPTE
   ;; physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86))
               :r x86)))
   ;; The PDPTE physical addresses are disjoint from the
   ;; translation-governing addresses of the stack.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (+ -24 (xr :rgf *rsp* x86)) x86))))

(defun-nx source-PDPTE-and-program-no-interfere-p (x86)
  ;; The PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (page-dir-ptr-table-entry-addr
               (xr :rgf *rdi* x86)
               (pdpt-base-addr (xr :rgf *rdi* x86) x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    *rewire_dst_to_src-len* (xr :rip nil x86) x86)))

(defun-nx source-PDPTE-and-source-PML4E-no-interfere-p (x86)
  ;; The source PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the source PML4E.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (page-dir-ptr-table-entry-addr
               (xr :rgf *rdi* x86)
               (pdpt-base-addr (xr :rgf *rdi* x86) x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx destination-addresses-ok-p (x86)
  (and
   ;; TLB is consistent for destination addresses
   (tlb-consistent-n *2^30* (xr :rgf *rsi* x86) :2 x86)
   ;; Destination addresses are canonical.
   (canonical-address-p (xr :rgf *rsi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
   ;; Destination address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
   ;; No errors encountered while translating the destination
   ;; linear addresses.
   (not (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r x86)))))

(defun-nx destination-PML4TE-ok-p (x86)
  (and
   ;; PML4TE addresses have consistent tlb
   (tlb-consistent-n 8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)) :r x86)
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
                   :r x86)))
   ;; PML4TE has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (mv-nth
      1
      (rb
       8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
       :r x86)))
    1)
   ;; PML4TE has PS = 0.
   (equal
    (part-select
     (mv-nth
      1
      (rb
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
       :r x86))
     :low 7 :width 1)
    0)
   ;; The destination PML4TE physical addresses are disjoint from
   ;; their own translation-governing addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)) x86))))

(defun-nx destination-PDPTE-ok-p (x86)
  (and
   ;; PDPTE addresses have consistent tlb
   (tlb-consistent-n 8 (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
                                                      (pdpt-base-addr (xr :rgf *rsi* x86)
                                                                      x86))
                     :r x86)
   (tlb-consistent-n 8 (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
                                                      (pdpt-base-addr (xr :rgf *rsi* x86)
                                                                      x86))
                     :w x86)
   ;; PDPTE linear addresses are canonical.
   (canonical-address-p
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rsi* x86)
     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
   (canonical-address-p
    (+ 7 (page-dir-ptr-table-entry-addr
          (xr :rgf *rsi* x86)
          (pdpt-base-addr (xr :rgf *rsi* x86) x86))))
   ;; No errors encountered while translating the PDPTE linear
   ;; addresses on behalf of a read.
   (not (mv-nth 0 (las-to-pas
                   8
                   (page-dir-ptr-table-entry-addr
                    (xr :rgf *rsi* x86)
                    (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                   :r x86)))
   ;; No errors encountered while translating the PDPTE linear
   ;; addresses on behalf of a write.
   (not (mv-nth 0 (las-to-pas
                   8
                   (page-dir-ptr-table-entry-addr
                    (xr :rgf *rsi* x86)
                    (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                   :w x86)))
   ;; Destination PDPTE does not have the P or PS bit cleared (i.e.,
   ;; the entry is present and it points to a 1G page).
   (equal (part-select
           (mv-nth 1
                   (rb
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                    :r x86))
           :low 0 :width 1)
          1)
   (equal (part-select
           (mv-nth 1
                   (rb
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                    :r x86))
           :low 7 :width 1)
          1)
   ;; The physical addresses corresponding to the destination PDPTE
   ;; are disjoint from their own translation-governing addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))

(defun-nx destination-PML4TE-and-stack-no-interfere-p (x86)
  (and
   ;; The stack physical addresses are disjoint from the destination
   ;; PML4TE physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
               :r x86)))
   ;; The destination PML4TE physical addresses are disjoint from the
   ;; translation-governing addresses of the stack.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (+ -24 (xr :rgf *rsp* x86)) x86))
   ;; The stack physical addresses are disjoint from the
   ;; translation-governing addresses of the destination PML4TE.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (all-xlation-governing-entries-paddrs
     8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)) x86))))

(defun-nx destination-PML4TE-and-program-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    *rewire_dst_to_src-len* (xr :rip nil x86) x86)))

(defun-nx destination-PML4TE-and-source-PML4TE-no-interfere-p (x86)
  ;; The destination PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the source PML4TE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx destination-PML4TE-and-source-PDPTE-no-interfere-p (x86)
  ;; The destination PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the source PDPTE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rdi* x86)
     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    x86)))

(defun-nx destination-PDPTE-and-source-PML4E-no-interfere-p (x86)
  ;; The destination PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the source PML4TE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (page-dir-ptr-table-entry-addr
               (xr :rgf *rsi* x86)
               (pdpt-base-addr (xr :rgf *rsi* x86) x86))
              :w x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx destination-PDPTE-and-source-PDPTE-no-interfere-p (x86)
  ;; The destination PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the source PDPTE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (page-dir-ptr-table-entry-addr
               (xr :rgf *rsi* x86)
               (pdpt-base-addr (xr :rgf *rsi* x86) x86))
              :w x86))
   (all-xlation-governing-entries-paddrs
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rdi* x86)
     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    x86)))

(defun-nx destination-PDPTE-and-destination-PML4TE-no-interfere-p (x86)
  ;; The destination PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the destination PML4TE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              8
              (page-dir-ptr-table-entry-addr
               (xr :rgf *rsi* x86)
               (pdpt-base-addr (xr :rgf *rsi* x86) x86))
              :w x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx destination-PDPTE-and-stack-no-interfere-p (x86)
  (and
   ;; The stack physical addresses are disjoint from the destination
   ;; PDPTE physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86)))
   ;; The destination PDPTE physical addresses are disjoint from the
   ;; translation-governing addresses of the stack.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (+ -24 (xr :rgf *rsp* x86)) x86))
   ;; The stack physical addresses are disjoint from the
   ;; translation-governing addresses of the destination PDPTE.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))

(defun-nx destination-PDPTE-and-program-no-interfere-p (x86)
  ;; We need these assumptions because the destination PDPTE is
  ;; modified, and we need to make sure that this modification does
  ;; not affect the program in any way.
  (and
   ;; The destination PDPTE physical addresses are disjoint from the
   ;; physical addresses of the program.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86)))
   ;; The destination PDPTE physical addresses are disjoint from the
   ;; translation-governing addresses of the program.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (all-xlation-governing-entries-paddrs
     *rewire_dst_to_src-len* (xr :rip nil x86) x86))
   ;; The program physical addresses are disjoint from the
   ;; translation-governing addresses of the destination PDPTE.
   (disjoint-p$
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))

(defun-nx return-address-ok-p (x86)
  ;; Return address on the stack is canonical.
  (canonical-address-p
   (logext 64 (mv-nth 1 (rb  8 (xr :rgf *rsp* x86) :r x86)))))

(defun-nx stack-containing-return-address-ok-p (x86)
  (and
   ;; The return address region has consistent tlb
   (tlb-consistent-n 8 (xr :rgf *rsp* x86) :r x86)

   ;; Reading the return address from stack doesn't cause any errors.
   (not (mv-nth 0 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86)))

   ;; !!! disjoint-p vs disjoint-p$
   ;; Physical return addresses are disjoint from their own
   ;; translation-governing addresses.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
    (all-xlation-governing-entries-paddrs 8 (xr :rgf *rsp* x86) x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
    (all-xlation-governing-entries-paddrs 8 (xr :rgf *rsp* x86) x86))))

(defun-nx stack-containing-return-address-and-program-no-interfere-p (x86)
  ;; Physical addresses on the stack corresponding to the return
  ;; address are disjoint from the translation-governing addresses of
  ;; the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
   (all-xlation-governing-entries-paddrs
    *rewire_dst_to_src-len* (xr :rip nil x86) x86)))

(defun-nx stack-containing-return-address-and-source-PML4E-no-interfere-p (x86)
  ;; Physical addresses on the stack corresponding to the return
  ;; address are disjoint from the translation-governing addresses of
  ;; the source PML4E.
  (disjoint-p$
   (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx stack-containing-return-address-and-source-PDPTE-no-interfere-p (x86)
  ;; Physical addresses on the stack corresponding to the return
  ;; address are disjoint from the translation-governing addresses of
  ;; the source PDPTE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rdi* x86)
     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    x86)))

(defun-nx stack-containing-return-address-and-destination-PML4E-no-interfere-p (x86)
  ;; Physical addresses on the stack corresponding to the return
  ;; address are disjoint from the translation-governing addresses of
  ;; the destination PML4E.
  (disjoint-p$
   (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx stack-containing-return-address-and-destination-PDPTE-no-interfere-p (x86)
  (and
   ;; !!! disjoint-p vs disjoint-p$
   ;; Destination PDPTE physical addresses are disjoint from the
   ;; translation-governing addresses of the stack containing the
   ;; return address.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8 (xr :rgf *rsp* x86) x86))
   ;; The destination PDPTE physical addresses are disjoint from the
   ;; stack containing the return address.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86)))
   ;; Stack containing the return address is disjoint from the
   ;; translation-governing addresses of the destination PDPTE.
   (disjoint-p$
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))

(defun-nx stack-containing-return-address-and-rest-of-the-stack-no-interfere-p (x86)
  ;; !!! disjoint-p vs disjoint-p$
  (and
   ;; Physical addresses on the stack corresponding to the return
   ;; address are disjoint from the translation-governing addresses of
   ;; the rest of the stack.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r  x86))
    (all-xlation-governing-entries-paddrs
     8 (+ -24 (xr :rgf *rsp* x86)) x86))
   ;; The rest of the stack is disjoint from the physical addresses on
   ;; the stack corresponding to the return address.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86)))))

;; ======================================================================

;; Some helpful lemmas:

(defthm xlate-equiv-structures-and-rflags-ac
  (and
   (xlate-equiv-structures
    (xw :rflags nil
        (rflagsBits$inline
         cf res1 pf res2 af res3 zf sf tf intf df of iopl nt res4 rf vm
         (rflagsbits->ac$inline (xr :rflags nil x86))
         vif vip id res5)
        x86)
    (double-rewrite x86))
   (xlate-equiv-structures
    x86
    (xw :rflags nil
        (rflagsBits$inline
         cf res1 pf res2 af res3 zf sf tf intf df of iopl nt res4 rf vm
         (rflagsbits->ac$inline (xr :rflags nil x86))
         vif vip id res5)
        x86)))
  :hints (("Goal"
           :in-theory (e/d (xlate-equiv-structures) ()))))

(defthm xlate-equiv-memory-and-rflags-ac
  (implies (and (64-bit-modep (double-rewrite x86))
                (not (xr :app-view nil (double-rewrite x86))))
           (and
            (xlate-equiv-memory
             (xw :rflags nil
                 (rflagsBits$inline
                  cf res1 pf res2 af res3 zf sf tf intf df of iopl nt res4 rf vm
                  (rflagsbits->ac$inline (xr :rflags nil x86))
                  vif vip id res5)
                 x86)
             (double-rewrite x86))
            (xlate-equiv-memory
             x86
             (xw :rflags nil
                 (rflagsBits$inline
                  cf res1 pf res2 af res3 zf sf tf intf df of iopl nt res4 rf vm
                  (rflagsbits->ac$inline (xr :rflags nil x86))
                  vif vip id res5)
                 x86))))
  :hints (("Goal"
           :in-theory (e/d (xlate-equiv-memory) ()))))

;; ----------------------------------------------------------------------
