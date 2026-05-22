; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2026, Kestrel Technology, LLC
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
; Contributing Author:
; Alessandro Coglio   <www.alessandrocoglio.info>

(in-package "X86ISA")

(include-book "basic-structs")

(include-book "xdoc/constructors" :dir :system)

;; We do these once, here, to avoid each defbitstruct below doing them locally:
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ----------------------------------------------------------------------

(defsection paging-bitstructs
  :parents (structures)
  :short "Bitstructs related to the paging data structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "Source:
     Intel Manual, Mar 2026, Vol. 3A,
     Tables 5-15 through 5-20,
     Figure 5-11.")
   (xdoc::p
    "For now we only model structures for 4-level paging,
     and only ordinary paging (i.e. not HLAT paging).
     As mentioned in
     Intel Manual, Mar 2026, Vol. 3A, Section 5.1.1, footnote 1,
     this paging mode was previously called `IA-32e paging':
     this is why the names of the bitstructs below start with @('ia32e').
     We may want to update these names at some point,
     perhaps when we add structures for the other paging three modes.")))

(local (xdoc::set-default-parents paging-bitstructs))

;; ----------------------------------------------------------------------

(defbitstruct ia32e-page-tablesBits ; Tables 5-15 through 5-20

  ;; This constant defines the common bit fields for page table
  ;; structure entries.

  ;; The field reference-addr refers to the 40 bits in a paging
  ;; structure entry that contain the address of the inferior paging
  ;; structure. If this paging entry maps a page (PS=1) instead of
  ;; referencing an inferior structure (PS=0), do not use the
  ;; reference-addr field to access the address of the page. Use
  ;; dedicated operations (e.g., those defined from the bitstruct
  ;; ia32e-pdpte-1GB-page-layout) in that case, because unlike
  ;; reference-addr, the address of the mapped page is contained in
  ;; different-sized fields for each paging structure.

  ((p bitp)                 ;; Page present
   (r/w bitp)               ;; Read/Write
   (u/s bitp)               ;; User/supervisor
   (pwt bitp)               ;; Page-level Write-Through
   (pcd bitp)               ;; Page-level Cache-Disable
   (a bitp)                 ;; Accessed
   (d bitp)                 ;; Dirty
   (ps bitp)                ;; Page size
   (res1 4bits)             ;; Ignored
   (reference-addr 40bits)  ;; Address of inferior paging table
   (res2 11bits)            ;; Ignored and/or Reserved
   (xd bitp))               ;; Execute Disable
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-page-tables-layout-ok
   (iff (ia32e-page-tablesBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pml4eBits ; Table 5-15
  ((p bitp)      ;; Present
   (r/w bitp)    ;; Read/write
   (u/s bitp)    ;; User/supervisor
   (pwt bitp)    ;; Page-level Write-Through
   (pcd bitp)    ;; Page-level Cache-Disable
   (a bitp)      ;; Accessed (whether entry has been used for LA translation)
   (res1 bitp)   ;; Ignored
   (ps bitp)     ;; Page size (must be 0)
   (res2 4bits)  ;; Ignored (bits 11:8, including R bit 11)
   (pdpt 40bits) ;; Address of page-directory pointer table (bits 51:12, any M)
   (res3 11bits) ;; Ignored (bits 62:52)
   (xd bitp))    ;; If IA32_EFER.NXE = 1, execute disable;
                 ;; otherwise reserved (must be 0)
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pml4e-layout-ok
   (iff (ia32e-pml4eBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pdpte-1GB-pageBits ; Table 5-16
  ((p bitp)      ;; Present
   (r/w bitp)    ;; Read/write
   (u/s bitp)    ;; User/supervisor
   (pwt bitp)    ;; Page-level Write-Through
   (pcd bitp)    ;; Page-level Cache-Disable
   (a bitp)      ;; Accessed (whether entry has been used for LA translation)
   (d bitp)      ;; Dirty (whether referenced page was written)
   (ps bitp)     ;; Page size (Must be 1 for 1GB pages)
   (g bitp)      ;; Global translation
   (res1 3bits)  ;; Ignored (bits 11:9, including R bit 11)
   (pat bitp)    ;; PAT
   (res2 17bits) ;; Reserved (bits 29:13)
   (page 22bits) ;; Address of 1GB page (bits 51:30, any M)
   (res3 11bits) ;; Ignored (bits 62:52, including protection key)
   (xd bitp))    ;; If IA32_EFER.NXE = 1, execute disable;
                 ;; otherwise reserved (must be 0)
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pdpte-1GB-page-layout-ok
   (iff (ia32e-pdpte-1GB-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pdpte-pg-dirBits ; Table 5-17
  ((p bitp)      ;; Present
   (r/w bitp)    ;; Read/write
   (u/s bitp)    ;; User/supervisor
   (pwt bitp)    ;; Page-level Write-Through
   (pcd bitp)    ;; Page-level Cache-Disable
   (a bitp)      ;; Accessed (whether this entry has been used for LA translation)
   (res1 bitp)   ;; Ignored
   (ps bitp)     ;; Page size (must be 0)
   (res2 4bits)  ;; Ignored (bits 11:8, including R bit 11)
   (pd 40bits)   ;; Address of 4K-aligned page directory (bits 52:12, any M)
   (res3 11bits) ;; Ignored (bits 62:52)
   (xd bitp))    ;; If IA32_EFER.NXE = 1, execute disable;
                 ;; otherwise reserved (must be 0)

  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pdpte-pg-dir-layout-ok
   (iff (ia32e-pdpte-pg-dirBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pde-2MB-pageBits ; Table 5-18
  ((p bitp)      ;; Present
   (r/w bitp)    ;; Read/write
   (u/s bitp)    ;; User/supervisor
   (pwt bitp)    ;; Page-level Write-Through
   (pcd bitp)    ;; Page-level Cache-Disable
   (a bitp)      ;; Accessed
   (d bitp)      ;; Dirty (whether referenced page was written)
   (ps bitp)     ;; Page size (Must be 1 for 2MB pages)
   (g bitp)      ;; Global translation
   (res1 3bits)  ;; Ignored (bits 11:9, including R bit 11)
   (pat bitp)    ;; PAT
   (res2 8bits)  ;; Reserved (bits 20:13)
   (page 31bits) ;; Address of the 2MB page (bits 51-21, any M)
   (res3 11bits) ;; Ignored (bits 62:52, including protection key)
   (xd bitp)     ;; If IA32_EFER.NXE = 1, execute disable;
                 ;; otherwise reserved (must be 0)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pde-2MB-page-layout-ok
   (iff (ia32e-pde-2MB-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pde-pg-tableBits ; Table 5-19
  ((p bitp)      ;; Present
   (r/w bitp)    ;; Read/write
   (u/s bitp)    ;; User/supervisor
   (pwt bitp)    ;; Page-level Write-Through
   (pcd bitp)    ;; Page-level Cache-Disable
   (a bitp)      ;; Accessed
   (res1 bitp)   ;; Ignored
   (ps bitp)     ;; Page size (must be 0)
   (res2 4bits)  ;; Ignored (bits 11:8, including R bit 11)
   (pt 40bits)   ;; Address of the 4K-aligned page table (bits 51:12, any M)
   (res3 11bits) ;; Ignored (bits 62:52)
   (xd bitp)     ;; If IA32_EFER.NXE = 1, execute disable;
                 ;; otherwise reserved (must be 0)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pde-pg-table-layout-ok
   (iff (ia32e-pde-pg-tableBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pte-4K-pageBits ; Table 5-20
  ((p bitp)        ;; Present
   (r/w bitp)      ;; Read/write
   (u/s bitp)      ;; User/supervisor
   (pwt bitp)      ;; Page-level Write-Through
   (pcd bitp)      ;; Page-level Cache-Disable
   (a bitp)        ;; Accessed
   (d bitp)        ;; Dirty (whether referenced page was written)
   (pat bitp)      ;; PAT
   (g bitp)        ;; Global translation
   (res1 3bits)    ;; Ignored (bits 11:9, including R bit 11)
   (page 40bits)   ;; Address of the 4K page (bits 51:12, any M)
   (res2 11bits)   ;; Ignored (bits 62:52, including protection key)
   (xd bitp)       ;; If IA32_EFER.NXE = 1, execute disable;
                   ;; otherwise reserved (must be 0)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pte-4k-page-layout-ok
   (iff (ia32e-pte-4k-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------
