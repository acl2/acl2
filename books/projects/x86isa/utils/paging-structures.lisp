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

(include-book "basic-structs")

(defsection paging-bitstructs
  :parents (structures)
  :short "<b>Bitstructs related to the paging data structures</b>"

  :long "<p>Source: Intel Manual, Mar'17, Vol. 3A, Tables 4-14 through 4-19,
  Figure 4-11)</p>"
  )

(local (xdoc::set-default-parents paging-bitstructs))

;; ----------------------------------------------------------------------

(defbitstruct ia32e-page-tablesBits

  ;; This constant defines the common bit-fields for page table
  ;; structure entries.

  ;; The field reference-addr refers to the 40 bits in a paging
  ;; structure entry that contain the address of the inferior paging
  ;; structure. If this paging entry maps a page (PS=1) instead of
  ;; referencing an inferior structure (PS=0), do not use the
  ;; reference-addr field to access the address of the page. Use
  ;; dedicated macros (e.g., those defined in context of
  ;; *ia32e-pdpte-1GB-page-layout*) in that case, because unlike
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
   (res1 4bits)            ;; Ignored
   (reference-addr 40bits) ;; Address of inferior paging table
   (res2 11bits)           ;; Ignored and/or Reserved
   (xd bitp))               ;; Execute Disable
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-page-tables-layout-ok
   (iff (ia32e-page-tablesBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pml4eBits
  ((p bitp)   ;; Page present (must be 1)
   (r/w bitp) ;; Read/write
   (u/s bitp) ;; User/supervisor
   (pwt bitp) ;; Page-level Write-Through
   (pcd bitp) ;; Page-level Cache-Disable
   (a bitp)   ;; Accessed (whether this entry has been used for LA translation)
   (res1 bitp)    ;; Ignored
   (ps bitp)      ;; Page size (Must be zero)
   (res2 4bits)  ;; Ignored
   (pdpt 40bits) ;; Address of page-directory pointer table
   (res3 11bits) ;; Ignored and/or Reserved
   (xd bitp))     ;; If IA32_EFER.NXE = 1, Execute disable;
  ;; otherwise 0 (reserved)
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pml4e-layout-ok
   (iff (ia32e-pml4eBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pdpte-1GB-pageBits
  ((p bitp)   ;; Page present (must be 1)
   (r/w bitp) ;; Read/write
   (u/s bitp) ;; User/supervisor
   (pwt bitp) ;; Page-level Write-Through
   (pcd bitp) ;; Page-level Cache-Disable
   (a bitp)   ;; Accessed (whether this entry has been used for LA translation)
   (d bitp) ;; Dirty (whether s/w has written to the 1 GB page referenced by this entry)
   (ps bitp)      ;; Page size (Must be 1 for 1GB pages)
   (g bitp)       ;; Global translation
   (res1 3bits)  ;; Ignored
   (pat bitp)     ;; PAT
   (res2 17bits) ;; Reserved
   (page 22bits) ;; Address of 1 GB page
   (res3 11bits) ;; Ignored and/or Reserved
   (xd bitp))     ;; If IA32_EFER.NXE = 1, Execute disable;
  ;; otherwise 0 (reserved)
  :msb-first nil
  :inline t
  )

(local
 (defthm ia32e-pdpte-1GB-page-layout-ok
   (iff (ia32e-pdpte-1GB-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pdpte-pg-dirBits
  ((p bitp)   ;; Page present (must be 1)
   (r/w bitp) ;; Read/write
   (u/s bitp) ;; User/supervisor
   (pwt bitp) ;; Page-level Write-Through
   (pcd bitp) ;; Page-level Cache-Disable
   (a bitp)   ;; Accessed (whether this entry has been used for LA translation)
   (res1 bitp)    ;; Ignored
   (ps bitp)      ;; Page size (Must be 0)
   (res2 4bits)  ;; Ignored
   (pd 40bits)   ;; Physical addres of 4-K aligned PD referenced by this entry
   (res3 11bits) ;; Ignored and/or Reserved
   (xd bitp))     ;; If IA32_EFER.NXE = 1, Execute disable;
  ;; otherwise 0 (reserved)

  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pdpte-pg-dir-layout-ok
   (iff (ia32e-pdpte-pg-dirBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pde-2MB-pageBits
  ((p bitp)       ;; Page present (must be 1)
   (r/w bitp)     ;; Read/write
   (u/s bitp)     ;; User/supervisor
   (pwt bitp)     ;; Page-level Write-Through
   (pcd bitp)     ;; Page-level Cache-Disable
   (a bitp)       ;; Accessed
   (d bitp)       ;; Dirty
   (ps bitp)      ;; Page size (Must be 1 for 2MB pages)
   (g bitp)       ;; Global translation
   (res1 3bits)  ;; Ignored
   (pat bitp)     ;; PAT
   (res2 8bits)  ;; Reserved
   (page 31bits) ;; Physical addres of the 2MB page referenced by this entry
   (res3 11bits) ;; Ignored and/or Reserved
   (xd bitp) ;; If IA32_EFER.NXE = 1, Execute disable; otherwise 0 (reserved)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pde-2MB-page-layout-ok
   (iff (ia32e-pde-2MB-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pde-pg-tableBits
  ((p bitp)        ;; Page present (must be 1)
   (r/w bitp)      ;; Read/write
   (u/s bitp)      ;; User/supervisor
   (pwt bitp)      ;; Page-level Write-Through
   (pcd bitp)      ;; Page-level Cache-Disable
   (a bitp)        ;; Accessed
   (res1 bitp)    ;; Ignored
   (ps bitp)       ;; Page size (Must be 0)
   (res2 4bits)  ;; Ignored
   (pt 40bits)    ;; Physical addres of the 4K-aligned
   ;; page table referenced by this entry
   (res3 11bits) ;; Ignored and/or Reserved
   (xd bitp)       ;; If IA32_EFER.NXE = 1, Execute
   ;; disable; otherwise 0 (reserved)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pde-pg-table-layout-ok
   (iff (ia32e-pde-pg-tableBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct ia32e-pte-4K-pageBits
  ((p bitp)        ;; Page present (must be 1)
   (r/w bitp)      ;; Read/write
   (u/s bitp)      ;; User/supervisor
   (pwt bitp)      ;; Page-level Write-Through
   (pcd bitp)      ;; Page-level Cache-Disable
   (a bitp)        ;; Accessed
   (d bitp)        ;; Dirty
   (pat bitp)      ;; PAT
   (g bitp)        ;; Global translation
   (res1 3bits)  ;; Ignored
   (page 40bits)  ;; Physical address of the 4K page
   ;; referenced by this entry
   (res2 11bits) ;; Ignored
   (xd bitp)       ;; If IA32_EFER.NXE = 1, Execute
   ;; disable; otherwise 0 (reserved)
   )
  :msb-first nil
  :inline t)

(local
 (defthm ia32e-pte-4k-page-layout-ok
   (iff (ia32e-pte-4k-pageBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------
