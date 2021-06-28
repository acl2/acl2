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

(include-book "sys-view/non-marking-view-top" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

;; Introducing the system-level program:

;;  1 mov %cr3,%rax
;;  2 mov %rax,-0x18(%rsp)
;;  3 mov -0x18(%rsp),%rdx
;;  4 mov %rdi,%rax
;;  5 shr $0x24,%rax
;;  6 and $0xff8,%eax
;;  7 and $0xfffffffffffff000,%rdx
;;  8 or %rdx,%rax
;;  9 mov (%rax),%rax
;; 10 test $0x1,%al
;; 11 je 400780 <rewire_dst_to_src+0x100>
;; 12 shr $0xc,%rax
;; 13 movabs $0xffffffffff,%r8
;; 14 mov %rdi,%rcx
;; 15 and %r8,%rax
;; 16 shr $0x1b,%rcx
;; 17 and $0xff8,%ecx
;; 18 shl $0xc,%rax
;; 19 or %rcx,%rax
;; 20 mov (%rax),%rax
;; 21 mov %rax,%rcx
;; 22 and $0x81,%ecx
;; 23 cmp $0x81,%rcx
;; 24 jne 400780 <rewire_dst_to_src+0x100>
;; 25 mov %rsi,%rcx
;; 26 movabs $0xfffffc0000000,%r9
;; 27 shr $0x24,%rcx
;; 28 and %rax,%r9
;; 29 and $0xff8,%ecx
;; 30 or %rdx,%rcx
;; 31 mov (%rcx),%rax
;; 32 test $0x1,%al
;; 33 je 400780 <rewire_dst_to_src+0x100>
;; 34 shr $0xc,%rax
;; 35 mov %rsi,%rdx
;; 36 and %r8,%rax
;; 37 shr $0x1b,%rdx
;; 38 and $0xff8,%edx
;; 39 shl $0xc,%rax
;; 40 or %rdx,%rax
;; 41 movabs $0xfff000003fffffff,%rdx
;; 42 and (%rax),%rdx
;; 43 or %r9,%rdx
;; 44 mov %rdx,(%rax)
;; 45 mov %rdx,%rax
;; 46 and $0x81,%eax
;; 47 cmp $0x81,%rax
;; 48 jne 400780 <rewire_dst_to_src+0x100>
;; 49 movabs $0xfffffc0000000,%rax
;; 50 and $0x3fffffff,%esi
;; 51 and $0x3fffffff,%edi
;; 52 and %rax,%rdx
;; 53 or %r9,%rdi
;; 54 xor %eax,%eax
;; 55 or %rsi,%rdx
;; 56 cmp %rdx,%rdi
;; 57 sete %al
;; 58 retq
;; 59 nopw %cs:0x0(%rax,%rax,1)
;; 60 mov $0xffffffffffffffff,%rax
;; 61 retq
;; 62 nopl 0x0(%rax,%rax,1)

(defconst *rewire_dst_to_src*

  '(#xF #x20 #xD8 #x48 #x89 #x44 #x24 #xE8
        #x48 #x8B #x54 #x24 #xE8 #x48 #x89 #xF8
        #x48 #xC1 #xE8 #x24 #x25 #xF8 #xF #x0
        #x0 #x48 #x81 #xE2 #x0 #xF0 #xFF #xFF
        #x48 #x9 #xD0 #x48 #x8B #x0 #xA8 #x1
        #xF #x84 #xD2 #x0 #x0 #x0 #x48 #xC1 #xE8
        #xC #x49 #xB8 #xFF #xFF #xFF #xFF #xFF
        #x0 #x0 #x0 #x48 #x89 #xF9 #x4C #x21
        #xC0 #x48 #xC1 #xE9 #x1B #x81 #xE1 #xF8
        #xF #x0 #x0 #x48 #xC1 #xE0 #xC #x48 #x9
        #xC8 #x48 #x8B #x0 #x48 #x89 #xC1 #x81
        #xE1 #x81 #x0 #x0 #x0 #x48 #x81 #xF9
        #x81 #x0 #x0 #x0 #xF #x85 #x94 #x0 #x0
        #x0 #x48 #x89 #xF1 #x49 #xB9 #x0 #x0 #x0
        #xC0 #xFF #xFF #xF #x0 #x48 #xC1 #xE9
        #x24 #x49 #x21 #xC1 #x81 #xE1 #xF8 #xF
        #x0 #x0 #x48 #x9 #xD1 #x48 #x8B #x1 #xA8
        #x1 #x74 #x70 #x48 #xC1 #xE8 #xC #x48
        #x89 #xF2 #x4C #x21 #xC0 #x48 #xC1 #xEA
        #x1B #x81 #xE2 #xF8 #xF #x0 #x0 #x48
        #xC1 #xE0 #xC #x48 #x9 #xD0 #x48 #xBA
        #xFF #xFF #xFF #x3F #x0 #x0 #xF0 #xFF
        #x48 #x23 #x10 #x4C #x9 #xCA #x48 #x89
        #x10 #x48 #x89 #xD0 #x25 #x81 #x0 #x0
        #x0 #x48 #x3D #x81 #x0 #x0 #x0 #x75 #x32
        #x48 #xB8 #x0 #x0 #x0 #xC0 #xFF #xFF
        #xF #x0 #x81 #xE6 #xFF #xFF #xFF #x3F
        #x81 #xE7 #xFF #xFF #xFF #x3F #x48 #x21
        #xC2 #x4C #x9 #xCF #x31 #xC0 #x48 #x9
        #xF2 #x48 #x39 #xD7 #xF #x94 #xC0 #xC3
        #x66 #x2E #xF #x1F #x84 #x0 #x0 #x0 #x0
        #x0 #x48 #xC7 #xC0 #xFF #xFF #xFF #xFF
        #xC3 #xF #x1F #x84 #x0 #x0 #x0 #x0 #x0))

(defconst *rewire_dst_to_src-len* (len *rewire_dst_to_src*))

(defun rewire_dst_to_src-clk () 58)

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
 (program-at (xr :rip nil x86) *rewire_dst_to_src* x86))

;; ======================================================================

;; Proof of rewire_dst_to_src effects theorem:

(defthm loghead-negative
  (implies (and (syntaxp (and (quotep n)
                              (< (cadr n) 0)))
                (< n 0)
                (integerp n))
           (equal (loghead n x) 0)))

(define pml4t-base-addr (x86)
  :enabled t
  (ash (cr3Bits->pdb (ctri *cr3* x86)) 12)
  ///

  (defthm-unsigned-byte-p n52p-of-pml4t-base-addr
    :hyp (x86p x86)
    :bound #.*physical-address-size*
    :concl (pml4t-base-addr x86))

  (defthm pml4t-base-addr-and-mv-nth-1-wb
    (equal (pml4t-base-addr (mv-nth 1 (wb n-w write-addr w value x86)))
           (pml4t-base-addr x86))))

(defun-nx pdpt-base-addr (lin-addr x86)
  (ash (loghead 40 (logtail 12
                            (mv-nth 1 (rb
                                       8 (pml4-table-entry-addr lin-addr (pml4t-base-addr x86))
                                       :r x86))))
       12))

;; The following is really a consequence of keeping
;; pdpt-base-addr enabled.
(defthm unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
  (implies (unsigned-byte-p 64 x)
           (unsigned-byte-p #.*physical-address-size*
                            (ash (loghead 40 (logtail 12 x)) 12))))

(defthm pdpt-base-addr-and-mv-nth-1-wb
  (implies (and
            (separate-mapped-mem :r 8   (pml4-table-entry-addr lin-addr (pml4t-base-addr x86))
                                 :w n-w write-addr
                                 x86)
            (disjoint-p
             (all-xlation-governing-entries-paddrs
              8 (pml4-table-entry-addr lin-addr (pml4t-base-addr x86)) x86)
             (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
            (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
            (not (app-view x86))
            (not (marking-view x86)))
           (equal (pdpt-base-addr lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
                  (pdpt-base-addr lin-addr x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* () ()))))

(defthm-using-gl pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (equal (pml4-table-entry-addr v-addr (ash (loghead 40 (logtail 12 cr3)) 12))
                (logior (logand -4096 (logext 64 cr3))
                        (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(defthm-using-gl page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (loghead 12 base-addr) 0)
            (unsigned-byte-p #.*physical-address-size* base-addr))
  :concl (equal (page-dir-ptr-table-entry-addr v-addr base-addr)
                (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                        base-addr))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat base-addr 64))))

(defthm-using-gl page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-1
  :hyp (and (equal (part-select entry :low 7 :width 1) 1)
            (equal (part-select entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 entry))
  :concl (equal (zf-spec (loghead 64 (+ -129 (logand 129 (loghead 32 entry))))) 1)
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
                                        (loghead 30 destination-entry)
                                        (logand 3221225472 (loghead 32 source-entry)))))))
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

;; ======================================================================

;; Assumptions:

(defun-nx x86-state-okp (x86)
  (and
   (x86p x86)
   (equal (xr :ms nil x86) nil)
   (equal (xr :fault nil x86) nil)
   (64-bit-modep x86)
   (not (alignment-checking-enabled-p x86))
   (not (app-view x86))
   (not (marking-view x86))
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
   ;; No errors encountered while translating the linear addresses
   ;; where the program is located.
   (not (mv-nth 0 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86)))))

(defun-nx stack-ok-p (x86)
  (and
   ;; Stack addresses are canonical.
   (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
   (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
   ;; Writing to stack: No errors encountered while translating the
   ;; linear addresses corresponding to the program stack.
   (not (mv-nth 0 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; Reading from stack: No errors encountered while translating the
   ;; linear addresses corresponding to the stack.
   (not (mv-nth 0 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :r x86)))
   ;; Reading from stack: The stack is located in a contiguous region
   ;; of memory --- no overlaps among physical addresses of the
   ;; stack.
   ;; I need this hypothesis so that the lemma
   ;; rb-wb-equal-in-non-marking-view can fire.
   (no-duplicates-p
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :r x86)))
   ;; Translation-governing addresses of the stack are disjoint from
   ;; the physical addresses of the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs 8 (+ -24 (xr :rgf *rsp* x86)) x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx source-addresses-ok-p (x86)
  (and
   ;; Source addresses are canonical.
   (canonical-address-p (xr :rgf *rdi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
   ;; Source address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
   ;; No errors encountered while translating the source linear
   ;; addresses.
   (not (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86)))))

(defun-nx destination-addresses-ok-p (x86)
  (and
   ;; Destination addresses are canonical.
   (canonical-address-p (xr :rgf *rsi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
   ;; Destination address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
   ;; No errors encountered while translating the destination
   ;; linear addresses.
   (not (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r x86)))))

(defun-nx source-PML4TE-ok-p (x86)
  (and
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86)))
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86))
                   :r x86)))
   ;; PML4TE has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (mv-nth
      1
      (rb 8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86)) :r x86)))
    1)))

(defun-nx source-PDPTE-ok-p (x86)
  (and
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
          1)))

(defun-nx destination-PML4TE-ok-p (x86)
  (and
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86)))
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))
                   :r x86)))
   ;; PML4TE is has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (mv-nth
      1
      (rb
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))
       :r x86)))
    1)))

(defun-nx destination-PDPTE-ok-p (x86)
  (and
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
          1)))

(defun-nx return-instruction-address-ok-p (x86)
  (and
   ;; Return address on the stack is canonical.
   (canonical-address-p
    (logext 64 (mv-nth 1 (rb 8 (xr :rgf *rsp* x86) :r x86))))
   ;; Reading from stack for the final ret instruction doesn't cause
   ;; errors.
   (not (mv-nth 0 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86)))))

(defun-nx program-and-stack-no-interfere-p (x86)
  (and
   ;; The physical addresses corresponding to the program and stack
   ;; are disjoint.
   (disjoint-p
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; Translation-governing addresses of the program are disjoint from
   ;; the physical addresses of the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs *rewire_dst_to_src-len* (xr :rip nil x86) x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx source-PML4TE-and-stack-no-intefere-p (x86)
  (and
   ;; The translation-governing addresses of PML4TE addresses are
   ;; disjoint from the physical addresses corresponding to the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs
     8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86)) x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; The PML4TE physical addresses are disjoint from the
   ;; stack physical addresses.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86))
                          :r x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx source-PDPTE-and-stack-no-interfere-p (x86)
  (and
   ;; The translation-governing addresses of PDPTE addresses are
   ;; disjoint from the physical addresses corresponding to the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86) (pdpt-base-addr (xr :rgf *rdi* x86) x86))
     x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; The PDPTE physical addresses are disjoint from the stack
   ;; physical addresses.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86))
               :r x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx destination-PML4TE-and-stack-no-interfere-p (x86)
  (and
   ;; The translation-governing addresses of PML4TE addresses are
   ;; disjoint from the physical addresses corresponding to the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs
     8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86)) x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; The PML4TE physical addresses are disjoint from the stack
   ;; physical addresses.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))
               :r x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx destination-PDPTE-and-stack-no-interfere-p (x86)
  (and
   ;; The translation-governing addresses of PDPTE addresses are
   ;; disjoint from the physical addresses corresponding to the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   ;; The destination PDPTE is disjoint from the stack.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx destination-PDPTE-and-program-no-interfere-p (x86)
  ;; We need these assumptions because the destination PDPTE is
  ;; modified, and we need to make sure that this modification does
  ;; not affect the program in any way.
  (and
   ;; The physical addresses corresponding to the program are disjoint
   ;; from those of the PDPTE (on behalf of a write).
   (disjoint-p
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip nil x86) :x x86))
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86)))

   ;; Translation-governing addresses of the program are disjoint from
   ;; the PDPTE physical addresses (on behalf of a write).
   (disjoint-p
    (all-xlation-governing-entries-paddrs *rewire_dst_to_src-len* (xr :rip nil x86) x86)
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w  x86)))))

(defun-nx ret-instruction-and-destination-PDPTE-no-interfere-p (x86)
  (and
   ;; The translation-governing addresses of the ret address are
   ;; disjoint from the destination PDPTE.
   (disjoint-p
    (all-xlation-governing-entries-paddrs 8 (xr :rgf *rsp* x86) x86)
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86) (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86)))

   ;; The destination PDPTE is disjoint from the ret address
   ;; on the stack.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86)))))

(defun-nx return-address-and-stack-no-interfere-p (x86)
  (and
   ;; The ret address on the stack is disjoint from the rest of the
   ;; stack.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (xr :rgf *rsp* x86) :r x86))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))

   ;; The translation-governing addresses of the return address on the
   ;; stack are disjoint from the physical addresses of the rest of
   ;; the stack.
   (disjoint-p
    (all-xlation-governing-entries-paddrs 8 (xr :rgf *rsp* x86) x86)
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))))

(defun-nx well-formedness-assumptions (x86)
  (and
   (x86-state-okp x86)
   (program-ok-p x86)
   (stack-ok-p x86)
   (source-addresses-ok-p x86)
   (destination-addresses-ok-p x86)
   (source-PML4TE-ok-p x86)
   (source-PDPTE-ok-p x86)
   (destination-PML4TE-ok-p x86)
   (destination-PDPTE-ok-p x86)
   (return-instruction-address-ok-p x86)))

(defun-nx non-interference-assumptions (x86)
  (and
   (program-and-stack-no-interfere-p x86)
   (source-PML4TE-and-stack-no-intefere-p x86)
   (source-PDPTE-and-stack-no-interfere-p x86)
   (destination-PML4TE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p x86)
   (ret-instruction-and-destination-PDPTE-no-interfere-p x86)
   (return-address-and-stack-no-interfere-p x86)))

(defun-nx rewire_dst_to_src-assumptions (x86)
  (and (well-formedness-assumptions x86)
       (non-interference-assumptions x86)))

;; ======================================================================

;; ACL2's default ancestors-check prevents
;; program-at-wb-disjoint-in-non-marking-view from being used.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(def-ruleset rewire_dst_to_src-disable
  '((:rewrite ia32e-la-to-pa-lower-12-bits-error)
    (:rewrite
     disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)
    (:type-prescription natp-pml4-table-entry-addr)
    (:rewrite acl2::consp-when-member-equal-of-atom-listp)
    (:rewrite ia32e-la-to-pa-xw-state)
    (:rewrite r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
    (:linear adding-7-to-pml4-table-entry-addr)
    (:linear *physical-address-size*p-pml4-table-entry-addr)
    ;; (:rewrite las-to-pas-xw-state)
    (:rewrite acl2::equal-of-booleans-rewrite)
    (:rewrite loghead-unequal)
    (:rewrite negative-logand-to-positive-logand-with-integerp-x)
    (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
    (:rewrite xr-ia32e-la-to-pa)
    (:rewrite acl2::nfix-when-not-natp)
    (:rewrite acl2::nfix-when-natp)
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
    (:type-prescription pml4t-base-addr)
    (:rewrite get-prefixes-opener-lemma-group-4-prefix)
    (:rewrite get-prefixes-opener-lemma-group-3-prefix)
    (:rewrite get-prefixes-opener-lemma-group-2-prefix)
    (:rewrite get-prefixes-opener-lemma-group-1-prefix)
    (:definition member-p)
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
    (:type-prescription true-listp)
    (:rewrite unsigned-byte-p-of-logtail)
    (:rewrite bitops::logbitp-when-bitmaskp)
    (:type-prescription all-xlation-governing-entries-paddrs)
    (:type-prescription set::setp-type)
    (:type-prescription set::empty-type)
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
    (:rewrite unsigned-byte-p-of-logior)
    (:type-prescription natp)
    (:rewrite set::in-set)
    (:type-prescription acl2::logtail-type)
    (:rewrite acl2::member-of-cons)
    (:rewrite rationalp-implies-acl2-numberp)
    (:type-prescription bitops::ash-natp-type)
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
    mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view
    mv-nth-1-ia32e-la-to-pa-when-error
    mv-nth-1-las-to-pas-when-error
    ;; bitops::logand-with-bitmask
    bitops::logand-with-negated-bitmask
    unsigned-byte-p
    force (force)))

(defthm rewire_dst_to_src-effects
  (implies (rewire_dst_to_src-assumptions x86)
           (equal (x86-run (rewire_dst_to_src-clk) x86)
                  (XW
                   :RGF *RAX* 1
                   (XW
                    :RGF *RCX*
                    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))
                    ;; (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                    ;;         (LOGAND 4088
                    ;;                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                    (XW
                     :RGF *RDX*
                     (LOGAND
                      4503598553628672
                      (LOGIOR
                       (LOGAND
                        -4503598553628673
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rsi* x86)
                            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                           ;; (LOGIOR
                           ;;  (LOGAND 4088
                           ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           ;;  (ASH
                           ;;   (LOGHEAD
                           ;;    40
                           ;;    (LOGTAIL
                           ;;     12
                           ;;     (MV-NTH
                           ;;      1
                           ;;      (RB
                           ;;       8
                           ;;       (LOGIOR
                           ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           ;;        (LOGAND 4088
                           ;;                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                           ;;       :R X86))))
                           ;;   12))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           ;; (LOGIOR
                           ;;  (LOGAND 4088
                           ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                           ;;  (ASH
                           ;;   (LOGHEAD
                           ;;    40
                           ;;    (LOGTAIL
                           ;;     12
                           ;;     (MV-NTH
                           ;;      1
                           ;;      (RB
                           ;;       8
                           ;;       (LOGIOR
                           ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           ;;        (LOGAND 4088
                           ;;                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                           ;;       :R X86))))
                           ;;   12))
                           :R X86))))))
                     (XW
                      :RGF *RSP* (+ 8 (XR :RGF *RSP* X86))
                      (XW
                       :RGF *RSI* 0
                       (XW
                        :RGF *RDI*
                        (LOGAND
                         4503598553628672
                         (LOGEXT
                          64
                          (MV-NTH
                           1
                           (RB
                            8
                            (page-dir-ptr-table-entry-addr
                             (xr :rgf *rdi* x86)
                             (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                            ;; (LOGIOR
                            ;;  (LOGAND 4088
                            ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                            ;;  (ASH
                            ;;   (LOGHEAD
                            ;;    40
                            ;;    (LOGTAIL
                            ;;     12
                            ;;     (MV-NTH
                            ;;      1
                            ;;      (RB
                            ;;       8
                            ;;       (LOGIOR
                            ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            ;;        (LOGAND 4088
                            ;;                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                            ;;       :R X86))))
                            ;;   12))
                            :R X86))))
                        (XW
                         :RGF *R8* 1099511627775
                         (XW
                          :RGF *R9*
                          (LOGAND
                           4503598553628672
                           (LOGEXT
                            64
                            (MV-NTH
                             1
                             (RB
                              8
                              (page-dir-ptr-table-entry-addr
                               (xr :rgf *rdi* x86)
                               (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                              ;; (LOGIOR
                              ;;  (LOGAND 4088
                              ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                              ;;  (ASH
                              ;;   (LOGHEAD
                              ;;    40
                              ;;    (LOGTAIL
                              ;;     12
                              ;;     (MV-NTH
                              ;;      1
                              ;;      (RB
                              ;;       8
                              ;;       (LOGIOR
                              ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              ;;        (LOGAND 4088
                              ;;                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                              ;;       :R X86))))
                              ;;   12))
                              :R X86))))
                          (XW
                           :RIP nil
                           (LOGEXT 64
                                   (MV-NTH 1 (RB 8 (XR :RGF *RSP* X86) :R X86)))
                           (XW
                            :UNDEF nil (+ 46 (NFIX (XR :UNDEF nil X86)))
                            (XW
                             :RFLAGS nil
                             (RFLAGSBITS
                              (BOOL->BIT
                               (<
                                (LOGAND
                                 4503598553628672
                                 (MV-NTH
                                  1
                                  (RB
                                   8
                                   (LOGIOR
                                    (LOGAND 4088
                                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                    (ASH
                                     (LOGHEAD
                                      40
                                      (LOGTAIL
                                       12
                                       (MV-NTH
                                        1
                                        (RB
                                         8
                                         (LOGIOR
                                          (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                          (LOGAND
                                           4088
                                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                         :R X86))))
                                     12))
                                   :R X86)))
                                (LOGAND
                                 4503598553628672
                                 (LOGIOR
                                  (LOGAND
                                   18442240475155922943
                                   (MV-NTH
                                    1
                                    (RB
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (MV-NTH
                                          1
                                          (RB
                                           8
                                           (LOGIOR
                                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                           :R X86))))
                                       12))
                                     :R X86)))
                                  (LOGAND
                                   4503598553628672
                                   (MV-NTH
                                    1
                                    (RB
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (MV-NTH
                                          1
                                          (RB
                                           8
                                           (LOGIOR
                                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                           :R X86))))
                                       12))
                                     :R X86)))))))
                              (RFLAGSBITS->RES1 (XR :RFLAGS nil X86))
                              (PF-SPEC64
                               (LOGHEAD
                                64
                                (+
                                 (LOGAND
                                  4503598553628672
                                  (LOGEXT
                                   64
                                   (MV-NTH
                                    1
                                    (RB
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (MV-NTH
                                          1
                                          (RB
                                           8
                                           (LOGIOR
                                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                           :R X86))))
                                       12))
                                     :R X86))))
                                 (-
                                  (LOGAND
                                   4503598553628672
                                   (LOGIOR
                                    (LOGAND
                                     -4503598553628673
                                     (LOGEXT
                                      64
                                      (MV-NTH
                                       1
                                       (RB
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          4088
                                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                         (ASH
                                          (LOGHEAD
                                           40
                                           (LOGTAIL
                                            12
                                            (MV-NTH
                                             1
                                             (RB
                                              8
                                              (LOGIOR
                                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                              :R X86))))
                                          12))
                                        :R X86))))
                                    (LOGAND
                                     4503598553628672
                                     (LOGEXT
                                      64
                                      (MV-NTH
                                       1
                                       (RB
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          4088
                                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                         (ASH
                                          (LOGHEAD
                                           40
                                           (LOGTAIL
                                            12
                                            (MV-NTH
                                             1
                                             (RB
                                              8
                                              (LOGIOR
                                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                              :R X86))))
                                          12))
                                        :R X86))))))))))
                              (RFLAGSBITS->RES2 (XR :RFLAGS nil X86))
                              (SUB-AF-SPEC64
                               (LOGAND
                                4503598553628672
                                (MV-NTH
                                 1
                                 (RB
                                  8
                                  (LOGIOR
                                   (LOGAND 4088
                                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                   (ASH
                                    (LOGHEAD
                                     40
                                     (LOGTAIL
                                      12
                                      (MV-NTH
                                       1
                                       (RB
                                        8
                                        (LOGIOR
                                         (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                         (LOGAND
                                          4088
                                          (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                        :R X86))))
                                    12))
                                  :R X86)))
                               (LOGAND
                                4503598553628672
                                (LOGIOR
                                 (LOGAND
                                  18442240475155922943
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND 4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (MV-NTH
                                         1
                                         (RB
                                          8
                                          (LOGIOR
                                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                           (LOGAND
                                            4088
                                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                          :R X86))))
                                      12))
                                    :R X86)))
                                 (LOGAND
                                  4503598553628672
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND 4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (MV-NTH
                                         1
                                         (RB
                                          8
                                          (LOGIOR
                                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                           (LOGAND
                                            4088
                                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                          :R X86))))
                                      12))
                                    :R X86))))))
                              (RFLAGSBITS->RES3 (XR :RFLAGS nil X86))
                              1
                              (SF-SPEC64
                               (LOGHEAD
                                64
                                (+
                                 (LOGAND
                                  4503598553628672
                                  (LOGEXT
                                   64
                                   (MV-NTH
                                    1
                                    (RB
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (MV-NTH
                                          1
                                          (RB
                                           8
                                           (LOGIOR
                                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                           :R X86))))
                                       12))
                                     :R X86))))
                                 (-
                                  (LOGAND
                                   4503598553628672
                                   (LOGIOR
                                    (LOGAND
                                     -4503598553628673
                                     (LOGEXT
                                      64
                                      (MV-NTH
                                       1
                                       (RB
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          4088
                                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                         (ASH
                                          (LOGHEAD
                                           40
                                           (LOGTAIL
                                            12
                                            (MV-NTH
                                             1
                                             (RB
                                              8
                                              (LOGIOR
                                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                              :R X86))))
                                          12))
                                        :R X86))))
                                    (LOGAND
                                     4503598553628672
                                     (LOGEXT
                                      64
                                      (MV-NTH
                                       1
                                       (RB
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          4088
                                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                         (ASH
                                          (LOGHEAD
                                           40
                                           (LOGTAIL
                                            12
                                            (MV-NTH
                                             1
                                             (RB
                                              8
                                              (LOGIOR
                                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                              :R X86))))
                                          12))
                                        :R X86))))))))))
                              (RFLAGSBITS->TF (XR :RFLAGS nil X86))
                              (RFLAGSBITS->INTF (XR :RFLAGS nil X86))
                              (RFLAGSBITS->DF (XR :RFLAGS nil X86))
                              (OF-SPEC64
                               (+
                                (LOGAND
                                 4503598553628672
                                 (LOGEXT
                                  64
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND 4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (MV-NTH
                                         1
                                         (RB
                                          8
                                          (LOGIOR
                                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                           (LOGAND
                                            4088
                                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                          :R X86))))
                                      12))
                                    :R X86))))
                                (-
                                 (LOGAND
                                  4503598553628672
                                  (LOGIOR
                                   (LOGAND
                                    -4503598553628673
                                    (LOGEXT
                                     64
                                     (MV-NTH
                                      1
                                      (RB
                                       8
                                       (LOGIOR
                                        (LOGAND
                                         4088
                                         (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                        (ASH
                                         (LOGHEAD
                                          40
                                          (LOGTAIL
                                           12
                                           (MV-NTH
                                            1
                                            (RB
                                             8
                                             (LOGIOR
                                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                              (LOGAND
                                               4088
                                               (LOGHEAD
                                                28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                             :R X86))))
                                         12))
                                       :R X86))))
                                   (LOGAND
                                    4503598553628672
                                    (LOGEXT
                                     64
                                     (MV-NTH
                                      1
                                      (RB
                                       8
                                       (LOGIOR
                                        (LOGAND
                                         4088
                                         (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                        (ASH
                                         (LOGHEAD
                                          40
                                          (LOGTAIL
                                           12
                                           (MV-NTH
                                            1
                                            (RB
                                             8
                                             (LOGIOR
                                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                              (LOGAND
                                               4088
                                               (LOGHEAD
                                                28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                             :R X86))))
                                         12))
                                       :R X86)))))))))
                              (RFLAGSBITS->IOPL (XR :RFLAGS nil X86))
                              (RFLAGSBITS->NT (XR :RFLAGS nil X86))
                              (RFLAGSBITS->RES4 (XR :RFLAGS nil X86))
                              (RFLAGSBITS->RF (XR :RFLAGS nil X86))
                              (RFLAGSBITS->VM (XR :RFLAGS nil X86))
                              (RFLAGSBITS->AC (XR :RFLAGS nil X86))
                              (RFLAGSBITS->VIF (XR :RFLAGS nil X86))
                              (RFLAGSBITS->VIP (XR :RFLAGS nil X86))
                              (RFLAGSBITS->ID (XR :RFLAGS nil X86))
                              (RFLAGSBITS->RES5 (XR :RFLAGS nil X86)))
                             (MV-NTH
                              1
                              (WB
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rsi* x86)
                                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                               ;; (LOGIOR
                               ;;  (LOGAND 4088
                               ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                               ;;  (ASH
                               ;;   (LOGHEAD
                               ;;    40
                               ;;    (LOGTAIL
                               ;;     12
                               ;;     (MV-NTH
                               ;;      1
                               ;;      (RB
                               ;;       8
                               ;;       (LOGIOR
                               ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                               ;;        (LOGAND 4088
                               ;;                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                               ;;       :R X86))))
                               ;;   12))
                               :W
                               (LOGIOR
                                (LOGAND
                                 18442240475155922943
                                 (MV-NTH
                                  1
                                  (RB
                                   8
                                   (page-dir-ptr-table-entry-addr
                                    (xr :rgf *rsi* x86)
                                    (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                                   ;; (LOGIOR
                                   ;;  (LOGAND 4088
                                   ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                   ;;  (ASH
                                   ;;   (LOGHEAD
                                   ;;    40
                                   ;;    (LOGTAIL
                                   ;;     12
                                   ;;     (MV-NTH
                                   ;;      1
                                   ;;      (RB
                                   ;;       8
                                   ;;       (LOGIOR
                                   ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   ;;        (LOGAND
                                   ;;         4088
                                   ;;         (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                   ;;       :R X86))))
                                   ;;   12))
                                   :R X86)))
                                (LOGAND
                                 4503598553628672
                                 (MV-NTH
                                  1
                                  (RB
                                   8
                                   (page-dir-ptr-table-entry-addr
                                    (xr :rgf *rdi* x86)
                                    (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                   ;; (LOGIOR
                                   ;;  (LOGAND 4088
                                   ;;          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                   ;;  (ASH
                                   ;;   (LOGHEAD
                                   ;;    40
                                   ;;    (LOGTAIL
                                   ;;     12
                                   ;;     (MV-NTH
                                   ;;      1
                                   ;;      (RB
                                   ;;       8
                                   ;;       (LOGIOR
                                   ;;        (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   ;;        (LOGAND
                                   ;;         4088
                                   ;;         (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                   ;;       :R X86))))
                                   ;;   12))
                                   :R X86))))
                               (MV-NTH 1
                                       (WB 8 (+ -24 (XR :RGF *RSP* X86))
                                           :W (XR :CTR *CR3* X86)
                                           X86)))))))))))))))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             rflag-RoWs-enables
                             cr3bits->pdb
                             segment-selectorbits->rpl

                             x86-operation-mode
                             shr-spec
                             shr-spec-64
                             sal/shl-spec
                             sal/shl-spec-64
                             gpr-and-spec-1
                             gpr-and-spec-4
                             gpr-and-spec-8
                             gpr-sub-spec-8
                             gpr-or-spec-8
                             gpr-xor-spec-4
                             jcc/cmovcc/setcc-spec
                             one-byte-opcode-execute
                             two-byte-opcode-decode-and-execute
                             x86-operand-from-modr/m-and-sib-bytes
                             check-instruction-length
                             x86-effective-addr-when-64-bit-modep
                             x86-effective-addr-32/64
                             x86-effective-addr-from-sib
                             x86-operand-to-reg/mem
                             rr08 rr32 rr64 wr08 wr32 wr64
                             riml08 riml32 riml64
                             rme-size wme-size
                             rime-size wime-size
                             write-user-rflags
                             pos
                             member-p
                             subset-p
                             rb-wb-equal-in-non-marking-view
                             select-segment-register)

                            (rewire_dst_to_src-disable
                             ;; Unnecessary here, and too expensive...
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))


;; ======================================================================

(encapsulate
  ()

  (defthm-using-gl rb-and-rm-low-64-for-direct-map-helper
    :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
              (n08p e) (n08p f) (n08p g) (n08p h))
    :concl (equal (logior a (ash b 8)
                          (ash (logior c (ash d 8)) 16)
                          (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
                  (logior a
                          (ash (logior b
                                       (ash (logior c
                                                    (ash
                                                     (logior d
                                                             (ash
                                                              (logior
                                                               e
                                                               (ash
                                                                (logior
                                                                 f
                                                                 (ash (logior g (ash h 8)) 8))
                                                                8)) 8)) 8)) 8)) 8)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
           (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

  (defthm-using-gl rml64-direct-map-helper
    :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
              (n08p e) (n08p f) (n08p g) (n08p h))
    :concl (equal
            (logior
             a
             (ash (logior
                   b
                   (ash (logior
                         c
                         (ash (logior
                               d
                               (ash (logior
                                     e
                                     (ash (logior f (ash (logior g (ash h 8)) 8))
                                          8))
                                    8))
                              8))
                        8))
                  8))
            (logior a (ash b 8)
                    (ash (logior c (ash d 8)) 16)
                    (ash (logior e (ash f 8) (ash (logior g (ash h 8)) 16)) 32)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
           (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

  (defthm rb-and-rm-low-64-for-direct-map
    (implies (and
              (equal
               (mv-nth 1 (las-to-pas 8 direct-mapped-addr r-w-x x86))
               (addr-range 8 direct-mapped-addr))
              (not (marking-view x86))
              (not (app-view x86))
              (x86p x86))
             (equal (mv-nth 1 (rb 8 direct-mapped-addr r-w-x x86))
                    (rm-low-64 direct-mapped-addr x86)))
    :hints (("Goal" :in-theory (e/d* (rb
                                      rm-low-64
                                      rm-low-32
                                      read-from-physical-memory
                                      rb-and-rm-low-64-for-direct-map-helper)
                                     ()))))

  (in-theory (e/d () (rb-and-rm-low-64-for-direct-map-helper
                      rml64-direct-map-helper))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((p-addrs (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
       (page-dir-ptr-table-entry
        (mv-nth 1 (rb 8 (page-dir-ptr-table-entry-addr lin-addr base-addr) :r x86))))
    (implies (and
              ;; page-dir-ptr-table-entry-addr is directly mapped.
              (equal
               (mv-nth
                1
                (las-to-pas
                 8 (page-dir-ptr-table-entry-addr lin-addr base-addr) :r x86))
               p-addrs)
              (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86)))
              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (unsigned-byte-p 64 value)
              (not (marking-view x86))
              (not (app-view x86))
              (x86p x86))
             ;; ia32e-la-to-pa-page-dir-ptr-table returns the physical
             ;; address corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs value x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs value x86)))
                         (logior (loghead 30 lin-addr)
                                 (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             ia32e-pdpte-1gb-pagebits->page)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((pml4-table-entry-addr (pml4-table-entry-addr lin-addr base-addr))
       (pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
       (pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
       (p-addrs (addr-range 8 page-dir-ptr-table-entry-addr)))
    (implies (and
              ;; PML4E and PDPTE are direct mapped.
              (equal
               (mv-nth
                1 (las-to-pas 8 pml4-table-entry-addr :r x86))
               (addr-range 8 pml4-table-entry-addr))
              (equal
               (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
               p-addrs)
              (disjoint-p (addr-range 8 pml4-table-entry-addr)
                          (addr-range 8 page-dir-ptr-table-entry-addr))
              (not (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))

              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1 G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (unsigned-byte-p 64 value)
              (not (app-view x86))
              (not (marking-view x86))
              (x86p x86))
             ;; ia32e-la-to-pa-pml4-table returns the physical address
             ;; corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs value x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs value x86)))
                         (logior (loghead 30 lin-addr)
                                 (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table
                             ia32e-pml4ebits->pdpt)
                            (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((pml4t-base-addr (pml4t-base-addr x86))
       (pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
       (pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
       (pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
       (p-addrs (addr-range 8 page-dir-ptr-table-entry-addr)))
    (implies (and
              ;; PML4E and PDPTE are direct mapped.
              (equal
               (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
               (addr-range 8 pml4-table-entry-addr))
              (equal
               (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
               p-addrs)
              (disjoint-p (addr-range 8 pml4-table-entry-addr)
                          (addr-range 8 page-dir-ptr-table-entry-addr))
              (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1 G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (unsigned-byte-p 64 value)
              (canonical-address-p lin-addr)
              (not (app-view x86))
              (not (marking-view x86))
              (x86p x86))
             ;; ia32e-la-to-pa returns the physical address
             ;; corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and
              (equal
               (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                         (write-to-physical-memory p-addrs value x86)))
               nil)
              (equal
               (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                         (write-to-physical-memory p-addrs value x86)))
               (logior (loghead 30 lin-addr)
                       (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :use ((:instance
                  ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                  (base-addr (ash (cr3Bits->pdb (ctri *cr3* x86)) 12))
                  (wp (cr0Bits->wp (n32 (ctri *cr0* x86))))
                  (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                  (smap (loghead 1 (bool->bit (logbitp 21 (xr :ctr *cr4* x86)))))
                  (ac (bool->bit (logbitp 18 (xr :rflags nil x86))))
                  (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))
                  (r-w-x r-w-x)
                  (cpl (cpl x86))
                  (x86 x86)))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa
                             cr3bits->pdb
                             cr0bits->wp
                             cr4bits->smep
                             cr4bits->smap
                             ia32_eferbits->nxe
                             segment-selectorbits->rpl
                             rflagsbits->ac)
                            (ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             not
                             force (force))))))

(defthm ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    ;; PML4E and PDPTE are direct mapped.
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 write-addr :w x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4t-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present value))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write value))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor value))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable value))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size value))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select value :low 13 :high 29))
    (unsigned-byte-p 64 value)
    (canonical-address-p lin-addr)
    (not (app-view x86))
    (not (marking-view x86))
    (x86p x86))
   ;; ia32e-la-to-pa returns the physical address corresponding to
   ;; "lin-addr" after the PDPTE corresponding to this "lin-addr" has
   ;; been modified --- the new PDPTE is "value".
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                     (mv-nth 1 (wb 8 write-addr w value x86))))
           nil)
    (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                     (mv-nth 1 (wb 8 write-addr w value x86))))
           (logior (loghead 30 lin-addr)
                   (ash (loghead 22 (logtail 30 value)) 30)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             wb)
                            (ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             not
                             force (force))))))

(defthm-using-gl same-pml4-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (physical-address-p pml4t-base-addr)
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (pml4-table-entry-addr (+ n lin-addr) pml4t-base-addr)
                (pml4-table-entry-addr lin-addr pml4t-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pml4t-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl same-pdp-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (unsigned-byte-p 30 n)
            (physical-address-p pdpt-base-addr)
            (canonical-address-p lin-addr)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (page-dir-ptr-table-entry-addr
                 (+ n lin-addr) pdpt-base-addr)
                (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pdpt-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl loghead-30-of-1G-aligned-lin-addr-+-n-1
  :hyp (and (canonical-address-p lin-addr)
            (canonical-address-p (+ n lin-addr))
            (equal (loghead 30 lin-addr) 0)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 (+ n lin-addr)) n)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl loghead-30-of-1G-aligned-lin-addr-+-n-2
  :hyp (and (equal (loghead 30 (+ n lin-addr)) n)
            (canonical-address-p (+ n lin-addr))
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 lin-addr) 0)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(defthm-using-gl logior-to-+-for-ash-x-30
  :hyp (and (unsigned-byte-p 22 x)
            (unsigned-byte-p 30 n))
  :concl (equal (logior n (ash x 30)) (+ n (ash x 30)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64) (:nat x 64))))

(defthm mv-nth-0-ia32e-la-to-pa-page-dir-ptr-table-for-same-1G-page
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    ;; PDPTE is direct mapped.
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr pdpt-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pdpt-base-addr)
    (equal (loghead 12 pdpt-base-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 0
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) pdpt-base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))
          nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                                   (commutativity-of-+
                                    not
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                                    bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-0-ia32e-la-to-pa-pml4-table-for-same-1G-page
  (implies
   (and
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    ;; PML4E and PDPTE are direct mapped.
    (equal
     (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                    lin-addr pml4t-base-addr wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4t-base-addr)
    (equal (loghead 12 pml4t-base-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 0
                  (ia32e-la-to-pa-pml4-table
                   (+ n lin-addr) pml4t-base-addr
                   wp smep smap ac nxe r-w-x cpl x86))
          nil))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                             ia32e-pml4ebits->pdpt)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-0-ia32e-la-to-pa-for-same-1G-page
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal
     (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 0 (ia32e-la-to-pa (+ n lin-addr) r-w-x x86)) nil))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthm-using-gl open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 lin-addr m))
            (integerp m)
            (<= m 1073741824)
            (natp iteration)
            (equal (loghead 30 lin-addr) 0))
  :concl (and (equal (loghead 30 (+ iteration lin-addr)) iteration)
              (canonical-address-p (+ iteration lin-addr)))
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(defthm-using-gl open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
  :hyp (and (< iteration m)
            (integerp m)
            (<= m 1073741824)
            (natp iteration))
  :concl (unsigned-byte-p 30 iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat iteration 64) (:nat m 64))))

(defthm-using-gl canonical-address-p-of-last-address-of-page
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 30 lin-addr) 0))
  :concl (canonical-address-p (+ -1 *2^30* lin-addr))
  :g-bindings (gl::auto-bindings (:nat lin-addr 64)))

(define las-to-pas-alt ((iteration natp)
                        (n         natp)
                        (lin-addr  integerp)
                        (r-w-x    :type (member :r :w :x))
                        x86)
  :enabled t
  :measure (nfix (- n iteration))
  :guard
  (and (<= iteration n)
       (canonical-address-p (+ n lin-addr))
       (not (app-view x86)))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p) ())))
  :returns (mv flg
               (p-addrs  true-listp :rule-classes (:rewrite :type-prescription))
               (x86      x86p :hyp (x86p x86)))

  (if (zp (- n iteration))
      (mv nil nil x86)
    (b* (((unless (canonical-address-p (+ iteration lin-addr)))
          (mv t nil x86))
         ((mv flg p-addr x86)
          (ia32e-la-to-pa (+ iteration lin-addr) r-w-x x86))
         ((when flg) (mv flg nil x86))
         ((mv flgs p-addrs x86)
          (las-to-pas-alt (1+ iteration) n lin-addr r-w-x x86)))
      (mv flgs (if flgs nil (cons p-addr p-addrs)) x86)))

  ///

  (local (in-theory (e/d* (las-to-pas) ())))

  (defthmd las-to-pas-alt-is-las-to-pas
    (and
     (equal (mv-nth 0 (las-to-pas-alt iteration n lin-addr r-w-x x86))
            (mv-nth 0 (las-to-pas (- n iteration) (+ iteration lin-addr) r-w-x x86)))
     (equal (mv-nth 1 (las-to-pas-alt iteration n lin-addr r-w-x x86))
            (mv-nth 1 (las-to-pas (- n iteration) (+ iteration lin-addr) r-w-x x86)))
     (equal (mv-nth 2 (las-to-pas-alt iteration n lin-addr r-w-x x86))
            (mv-nth 2 (las-to-pas (- n iteration) (+ iteration lin-addr) r-w-x x86))))))

(defthmd open-mv-nth-0-las-to-pas-for-same-1G-page-general
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 m lin-addr))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 0 (las-to-pas-alt iteration m lin-addr r-w-x x86))
          nil))
  :hints (("Goal"
           :induct (las-to-pas-alt iteration m lin-addr r-w-x x86)
           :in-theory (e/d* (las-to-pas
                             canonical-address-p
                             mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2)
                            (not
                             pml4t-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))
          (if (equal (car id) '(0 1))
              '(:use ((:instance open-mv-nth-0-las-to-pas-for-same-1G-page-general-1)))
            nil)))

(defthm open-mv-nth-0-las-to-pas-for-same-1G-page
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 0 (las-to-pas *2^30* lin-addr r-w-x x86)) nil))
  :hints (("Goal"
           :use ((:instance open-mv-nth-0-las-to-pas-for-same-1G-page-general
                            (m *2^30*) (iteration 0))
                 (:instance canonical-address-p-of-last-address-of-page))
           :in-theory (e/d* (las-to-pas
                             las-to-pas-alt-is-las-to-pas)
                            (canonical-address-p-of-last-address-of-page
                             not
                             pml4t-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthm mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-for-same-1G-page
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    ;; PDPTE is direct mapped.
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr pdpt-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pdpt-base-addr)
    (equal (loghead 12 pdpt-base-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 1
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) pdpt-base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    ia32e-pdpte-1gb-pagebits->page)
                                   (commutativity-of-+
                                    not
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                                    bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-1-ia32e-la-to-pa-pml4-table-for-same-1G-page
  (implies
   (and
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    ;; PML4E and PDPTE are direct mapped.
    (equal
     (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                    lin-addr pml4t-base-addr
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4t-base-addr)
    (equal (loghead 12 pml4t-base-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 1
                  (ia32e-la-to-pa-pml4-table
                   (+ n lin-addr) pml4t-base-addr
                   wp smep smap ac nxe r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                             ia32e-pml4ebits->pdpt)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-1-ia32e-la-to-pa-for-same-1G-page
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal
     (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 1 (ia32e-la-to-pa (+ n lin-addr) r-w-x x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthmd open-mv-nth-1-las-to-pas-for-same-1G-page-general
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal
     (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (marking-view x86))
    (x86p x86))
   (equal (mv-nth 1 (las-to-pas-alt iteration m lin-addr r-w-x x86))
          (addr-range
           (+ (- iteration) m)
           (+ iteration
              (ash
               (loghead 22
                        (logtail 30
                                 (rm-low-64
                                  (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                  x86)))
               30)))))
  :hints (("Goal"
           :induct (las-to-pas-alt iteration m lin-addr r-w-x x86)
           :in-theory (e/d* (las-to-pas
                             ;; open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general
                             mv-nth-1-ia32e-la-to-pa-for-same-1G-page)
                            (not
                             pml4t-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthm open-mv-nth-1-las-to-pas-for-same-1G-page
  (implies
   (and (equal pml4t-base-addr (pml4t-base-addr x86))
        (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
        (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
        (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
        (equal page-dir-ptr-table-entry-addr
               (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
        (equal page-dir-ptr-table-entry
               (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
        (equal
         (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
         (addr-range 8 pml4-table-entry-addr))
        (equal
         (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
         (addr-range 8 page-dir-ptr-table-entry-addr))
        (equal (page-size page-dir-ptr-table-entry) 1)
        (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
        (canonical-address-p lin-addr)
        (equal (loghead 30 lin-addr) 0)
        (not (marking-view x86))
        (x86p x86))
   (equal (mv-nth 1 (las-to-pas *2^30* lin-addr r-w-x x86))
          (addr-range
           *2^30*
           (ash
            (loghead 22
                     (logtail 30
                              (rm-low-64
                               (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                               x86)))
            30))))
  :hints (("Goal"
           :use ((:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general
                            (m *2^30*) (iteration 0))
                 (:instance canonical-address-p-of-last-address-of-page))
           :in-theory (e/d* (las-to-pas
                             las-to-pas-alt-is-las-to-pas)
                            (canonical-address-p-of-last-address-of-page
                             not
                             pml4t-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthmd las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 write-addr :w x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4t-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present value))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write value))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor value))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable value))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size value))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select value :low 13 :high 29))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (unsigned-byte-p 64 value)
    (not (app-view x86))
    (not (marking-view x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is value.
   (and
    (equal (mv-nth 0 (las-to-pas-alt
                      iteration m lin-addr r-w-x (mv-nth 1 (wb 8 write-addr w value x86))))
           nil)
    (equal (mv-nth 1 (las-to-pas-alt
                      iteration m lin-addr r-w-x (mv-nth 1 (wb 8 write-addr w value x86))))
           (addr-range
            (+ (- iteration) m)
            (+ iteration (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal" :do-not '(preprocess)
           :induct (las-to-pas-alt iteration m lin-addr r-w-x x86)
           :in-theory (e/d*
                       (disjoint-p
                        member-p
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general
                        mv-nth-1-ia32e-la-to-pa-for-same-1G-page)
                       (mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-view
                        page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                        page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                        bitops::logand-with-negated-bitmask
                        force (force)
                        not)))))

(defthm las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 write-addr :w x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4t-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present value))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write value))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor value))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable value))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size value))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select value :low 13 :high 29))
    (unsigned-byte-p 64 value)
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (not (marking-view x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is value.
   (and
    (equal (mv-nth 0 (las-to-pas *2^30* lin-addr r-w-x
                                 (mv-nth 1 (wb 8 write-addr w value x86))))
           nil)
    (equal (mv-nth 1 (las-to-pas *2^30* lin-addr r-w-x
                                 (mv-nth 1 (wb 8 write-addr w value x86))))
           (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30)))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :use ((:instance las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
                            (m *2^30*)
                            (iteration 0))
                 (:instance canonical-address-p-of-last-address-of-page))
           :in-theory (e/d* (las-to-pas-alt-is-las-to-pas
                             las-to-pas)
                            (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

(defthm read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-view
  (b* ((pml4t-base-addr (pml4t-base-addr x86))
       (pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
       (pdpt-base-addr
        (pdpt-base-addr lin-addr x86))
       (page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86))))
    (implies
     (and
      ;; PML4E and PDPTE are direct mapped.
      (equal
       (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
       (addr-range 8 pml4-table-entry-addr))
      (equal
       (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
       (addr-range 8 page-dir-ptr-table-entry-addr))
      (equal (mv-nth 1 (las-to-pas 8 write-addr :w x86))
             (addr-range 8 page-dir-ptr-table-entry-addr))
      ;; The physical addresses pointed to by the new PDPTE (i.e.,
      ;; containing "value") are disjoint from the physical addresses
      ;; corresponding to the PDPTE itself.
      (disjoint-p
       (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
       (addr-range 8 page-dir-ptr-table-entry-addr))
      (disjoint-p
       (addr-range 8 (pml4-table-entry-addr lin-addr pml4t-base-addr))
       (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
      (not (mv-nth 0 (las-to-pas 8 write-addr :w x86)))
      (equal (page-present page-dir-ptr-table-entry)
             (page-present value))
      (equal (page-read-write page-dir-ptr-table-entry)
             (page-read-write value))
      (equal (page-user-supervisor page-dir-ptr-table-entry)
             (page-user-supervisor value))
      (equal (page-execute-disable page-dir-ptr-table-entry)
             (page-execute-disable value))
      (equal (page-size page-dir-ptr-table-entry)
             (page-size value))
      (equal (page-size page-dir-ptr-table-entry) 1)
      (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
             (part-select value :low 13 :high 29))
      (unsigned-byte-p 64 value)
      (canonical-address-p lin-addr)
      (canonical-address-p (+ -1 *2^30* lin-addr))
      ;; 1G-aligned linear address
      (equal (loghead 30 lin-addr) 0)
      (not (app-view x86))
      (not (marking-view x86))
      (x86p x86))
     (equal (read-from-physical-memory
             (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
             (mv-nth 1 (wb 8 write-addr w value x86)))
            (read-from-physical-memory
             (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
             x86))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory (e/d* (disjoint-p
                             member-p
                             wb
                             page-dir-ptr-table-entry-addr
                             pml4-table-entry-addr)
                            (n01p-pf-spec16
                             size-of-read-from-physical-memory
                             read-from-physical-memory
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not
                             rewire_dst_to_src-disable)))))

(defthm rb-wb-equal-with-modified-1G-page-map-in-system-level-non-marking-view
  (implies
   (and
    (equal pml4t-base-addr (pml4t-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4t-base-addr))
    (equal pml4-table-entry (mv-nth 1 (rb 8 pml4-table-entry-addr :r x86)))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (mv-nth 1 (rb 8 page-dir-ptr-table-entry-addr :r x86)))
    (equal (mv-nth 1 (las-to-pas 8 pml4-table-entry-addr :r x86))
           (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1 (las-to-pas 8 page-dir-ptr-table-entry-addr :r x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas 8 write-addr :w x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4t-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (disjoint-p
     (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
     (mv-nth 1 (las-to-pas 8 write-addr :w x86)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
    (not (mv-nth 0 (las-to-pas 8 write-addr :w x86)))
    (not (mv-nth 0 (las-to-pas *2^30* lin-addr r-w-x x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present value))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write value))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor value))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable value))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size value))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select value :low 13 :high 29))
    (unsigned-byte-p 64 value)
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (app-view x86))
    (not (marking-view x86))
    (x86p x86))
   (and (equal (mv-nth 0 (rb *2^30* lin-addr r-w-x
                             (mv-nth 1 (wb 8 write-addr w value x86))))
               nil)
        (equal (mv-nth 1 (rb *2^30* lin-addr r-w-x
                             (mv-nth 1 (wb 8 write-addr w value x86))))
               (read-from-physical-memory
                (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
                x86))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :use
           ((:instance read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-view)
            (:instance canonical-address-p-of-last-address-of-page))
           :in-theory (e/d* (rb disjoint-p member-p)
                            (read-from-physical-memory
                             read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-view
                             wb
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

(defthm-using-gl entry-attributes-unchanged-when-destination-PDPTE-modified
  :hyp (and (unsigned-byte-p 64 dest-pdpte)
            (unsigned-byte-p 64 src-pdpte))
  :concl (and
          (equal (page-present (logior (logand 18442240475155922943 dest-pdpte)
                                       (logand 4503598553628672 src-pdpte)))
                 (page-present dest-pdpte))
          (equal (page-read-write (logior (logand 18442240475155922943 dest-pdpte)
                                          (logand 4503598553628672 src-pdpte)))
                 (page-read-write dest-pdpte))
          (equal (page-user-supervisor (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-user-supervisor dest-pdpte))
          (equal (page-execute-disable (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-execute-disable dest-pdpte))
          (equal (page-size (logior (logand 18442240475155922943 dest-pdpte)
                                    (logand 4503598553628672 src-pdpte)))
                 (page-size dest-pdpte)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat src-pdpte 64) (:nat dest-pdpte 64))))

(defthm rb-of-1G-in-terms-of-read-from-physical-memory
  (implies (and (not (app-view x86))
                (not (marking-view x86)))
           (equal
            (mv-nth 1 (rb n (xr :rgf *rdi* x86) :r x86))
            (read-from-physical-memory
             (mv-nth 1 (las-to-pas n (xr :rgf *rdi* x86) :r x86)) x86)))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (rb-wb-equal-in-non-marking-view
                             pos member-p subset-p
                             page-size
                             rb
                             mv-nth-2-las-to-pas-system-level-non-marking-view)

                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)

                             pml4t-base-addr
                             pdpt-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             acl2::ash-0
                             acl2::zip-open
                             acl2::member-of-cons
                             open-mv-nth-0-las-to-pas-for-same-1g-page
                             open-mv-nth-1-las-to-pas-for-same-1g-page
                             rb-1
                             car-mv-nth-1-las-to-pas
                             (:linear mv-nth-1-idiv-spec)
                             (:linear mv-nth-1-div-spec)
                             (:rewrite acl2::equal-of-booleans-rewrite)
                             (:linear acl2::expt->-1)
                             (:rewrite acl2::loghead-identity)
                             (:rewrite consp-mv-nth-1-las-to-pas)

                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

;; ----------------------------------------------------------------------

(defun-nx direct-mapped-paging-entries-p (x86)
  ;; Direct map for paging structures, specifically source and
  ;; destination PML4E and PDPTE.
  (and
   ;; Source:
   (equal (mv-nth 1 (las-to-pas
                     8
                     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86))
                     :r x86))
          (addr-range
           8
           (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4t-base-addr x86))))

   (equal
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86))
               :r x86))
    (addr-range
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))))

   ;; Destination:
   (equal
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))
               :r x86))
    (addr-range
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86))))

   (equal
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (addr-range
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))

(defun-nx source-physical-addresses-and-destination-PDPTE-no-interfere-p (x86)
  ;; The source physical addresses are disjoint from the the physical
  ;; addresses of the destination PDPTE.
  (disjoint-p
   (addr-range *2^30*
               (ash (loghead 22 (logtail 30
                                         (rm-low-64
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rdi* x86)
                                           (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                          x86)))
                    30))
   (addr-range 8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))

(defun-nx destination-PML4E-and-destination-PDPTE-no-interfere-p (x86)
  (disjoint-p
   (addr-range 8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4t-base-addr x86)))
   (addr-range 8 (page-dir-ptr-table-entry-addr
                  (xr :rgf *rsi* x86)
                  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))

(defun-nx destination-xlation-governing-entries-paddrs-and-stack-no-interfere-p (x86)
  ;; The translation-governing addresses of the destination are disjoint
  ;; from the physical addresses corresponding to the stack.
  (disjoint-p
   (all-xlation-governing-entries-paddrs *2^30* (xr :rgf *rsi* x86) x86)
   (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))))

(defun-nx source-addresses-and-stack-no-interfere-p (x86)
  ;; The source addresses are disjoint from the physical addresses
  ;; corresponding to the stack.
  (disjoint-p
   (addr-range
    *2^30*
    (ash
     (loghead
      22
      (logtail
       30
       (rm-low-64 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rdi* x86)
                   (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                  x86)))
     30))
   (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w x86))))

(defun-nx more-non-interference-assumptions (x86)
  (and (source-physical-addresses-and-destination-PDPTE-no-interfere-p x86)
       (destination-PML4E-and-destination-PDPTE-no-interfere-p x86)
       (destination-xlation-governing-entries-paddrs-and-stack-no-interfere-p x86)
       (source-addresses-and-stack-no-interfere-p x86)))

;; ----------------------------------------------------------------------

(defthm rewire_dst_to_src-after-the-copy-source-p-addrs-open
  (implies (and (equal cpl (cpl x86))
                (rewire_dst_to_src-assumptions x86)
                (direct-mapped-paging-entries-p x86))

           (equal
            (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86))
            (addr-range *2^30*
                        (ash (loghead 22
                                      (logtail 30
                                               (rm-low-64
                                                (page-dir-ptr-table-entry-addr
                                                 (xr :rgf *rdi* x86)
                                                 (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                                x86)))
                             30))))
  :hints (("Goal"
           :use ((:instance las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
                            (pml4t-base-addr (pml4t-base-addr x86))
                            (pml4-table-entry-addr
                             (pml4-table-entry-addr (xr :rgf *rdi* x86)
                                                    (pml4t-base-addr x86)))
                            (pml4-table-entry
                             (mv-nth 1 (rb 8 (pml4-table-entry-addr (xr :rgf *rdi* x86)
                                                                    (pml4t-base-addr x86))
                                           :r x86)))
                            (pdpt-base-addr
                             (ash (loghead 40
                                           (logtail
                                            12
                                            (mv-nth 1 (rb
                                                       8 (pml4-table-entry-addr (xr :rgf *rdi* x86)
                                                                                (pml4t-base-addr x86))
                                                       :r x86))))
                                  12))
                            (page-dir-ptr-table-entry-addr
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rdi* x86)
                              (ash (loghead 40
                                            (logtail
                                             12
                                             (mv-nth 1 (rb
                                                        8 (pml4-table-entry-addr (xr :rgf *rdi* x86)
                                                                                 (pml4t-base-addr x86))
                                                        :r x86))))
                                   12)))
                            (page-dir-ptr-table-entry
                             (mv-nth 1
                                     (rb
                                      8
                                      (page-dir-ptr-table-entry-addr
                                       (xr :rgf *rdi* x86)
                                       (ash (loghead 40
                                                     (logtail
                                                      12
                                                      (mv-nth 1 (rb
                                                                 8 (pml4-table-entry-addr (xr :rgf *rdi* x86)
                                                                                          (pml4t-base-addr x86))
                                                                 :r x86))))
                                            12))
                                      :r x86)))
                            (lin-addr (xr :rgf *rdi* x86))
                            (r-w-x :r)))
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (pdpt-base-addr
                             pml4t-base-addr
                             pos
                             page-size
                             cr3bits->pdb
                             segment-selectorbits->rpl
                             ia32e-page-tablesbits->ps)
                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)
                             addr-range
                             (addr-range)
                             pml4-table-entry-addr
                             natp-pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                             acl2::consp-when-member-equal-of-atom-listp
                             ia32e-la-to-pa-xw-state
                             (:linear adding-7-to-pml4-table-entry-addr)
                             (:linear *physical-address-size*p-pml4-table-entry-addr)
                             ;; (:rewrite las-to-pas-xw-state)
                             (:rewrite acl2::equal-of-booleans-rewrite)
                             (:rewrite loghead-unequal)
                             (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                             (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             not
                             unsigned-byte-p-of-logtail
                             disjoint-p-subset-p
                             acl2::loghead-identity
                             acl2::ash-0
                             acl2::zip-open
                             acl2::logtail-identity
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

(defthm rewire_dst_to_src-after-the-copy-destination==source
  (implies (and (rewire_dst_to_src-assumptions x86)
                (direct-mapped-paging-entries-p x86)
                (more-non-interference-assumptions x86))
           (equal
            ;; Destination, after the copy:
            (mv-nth 1 (rb  *2^30* (xr :rgf *rsi* x86) :r
                           (x86-run (rewire_dst_to_src-clk) x86)))
            ;; Source, before the copy:
            (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r x86))))
  :hints (("Goal"
           :do-not '(preprocess generalize fertilize)
           :do-not-induct t
           :in-theory
           (e/d* (rb-wb-equal-in-non-marking-view
                  pos
                  pdpt-base-addr
                  page-size
                  cr3bits->pdb
                  ia32e-page-tablesbits->ps)
                 (rewire_dst_to_src-clk
                  (rewire_dst_to_src-clk)
                  addr-range
                  (addr-range)
                  size-of-rb
                  pml4-table-entry-addr
                  natp-pml4-table-entry-addr
                  page-dir-ptr-table-entry-addr
                  pml4-table-entry-addr-to-c-program-optimized-form
                  pml4-table-entry-addr-to-c-program-optimized-form-gl
                  page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                  page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                  disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                  acl2::consp-when-member-equal-of-atom-listp
                  ia32e-la-to-pa-xw-state
                  adding-7-to-pml4-table-entry-addr
                  *physical-address-size*p-pml4-table-entry-addr
                  (:r acl2::equal-of-booleans-rewrite)
                  (:r loghead-unequal)
                  (:r loghead-of-non-integerp)
                  (:r negative-logand-to-positive-logand-with-integerp-x)
                  (:r |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                  not
                  unsigned-byte-p-of-logtail
                  disjoint-p-subset-p
                  acl2::loghead-identity
                  acl2::ash-0
                  acl2::zip-open
                  acl2::logtail-identity
                  bitops::logand-with-negated-bitmask
                  unsigned-byte-p
                  force (force))))))

;; ======================================================================
