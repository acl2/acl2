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

;; ----------------------------------------------------------------------

(defsection segmentation-bitstructs
  :parents (structures)
  :short "<b>Bitstructs related to segmentation, protection, etc.</b>"
  )

(local (xdoc::set-default-parents segmentation-bitstructs))

;; ----------------------------------------------------------------------

(defbitstruct hidden-segment-registerBits
  :short "Intel manual, Dec'23, Vol. 3A, Figure 3-7."
  ((base-addr 64bits) ;; Segment Base Address
   (limit 32bits)     ;; Segment Limit
   (attr  16bits)     ;; Attributes
   )
  :inline t
  :msb-first nil)
; These fields are "cached" from the segment descriptor (Figure 3-8):
; - The Segment Base is 32 bits in the segment descriptor,
;   so the 64 bits in BASE-ADDR above can hold it.
; - The Segment Limit is 20 bits in the segment descriptor,
;   and based on the G (granularity) flag it covers up to 4 GiB,
;   so the 32 bits in LIMIT above can hold it.
;   IMPORTANT: this means that the cached limit field must be
;   populated only after G flag is taken into account.
; - There are 12 remaining bits in the segment descriptor,
;   so the 16 bits in ATTR above can hold them.

(local
 (defthm hidden-segment-register-layout-ok
   (iff (hidden-segment-registerBits-p x)
        (unsigned-byte-p 112 x))
   :rule-classes nil))

(defbitstruct segment-selectorBits
  :short "Intel manual, Mar'23, Vol. 3A, Figure 3-6."
  ((rpl 2bits)     ;; Requestor Privilege Level (RPL)
   (ti bitp)       ;; Table Indicator (0 = GDT, 1 = LDT)
   (index 13bits)  ;; Index of descriptor in GDT or LDT
   )
  :inline t
  :msb-first nil)

(local
 (defthm segment-selector-layout-ok
   (iff (segment-selectorBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

(defbitstruct interrupt/trap-gate-descriptorBits
  :short "AMD manual, Jun'23, Vol. 2, Figures 4-24 and 4-18."
  ((offset15-0 16bits)
   (selector 16bits)
   (ist 3bits)
   (res1 5bits)
   (type 4bits)
   (s bitp) ;; S = 0 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (offset31-16 16bits)
   (offset63-32 32bits)
   (res2 8bits)
   (all-zeros? 5bits) ;; Check whether these are all zeroes or not.
   (res3 19bits)
   )
  :msb-first nil
  :inline t)

(local
 (defthm interrupt/trap-gate-descriptor-layout-ok
   (iff (interrupt/trap-gate-descriptorBits-p x)
        (unsigned-byte-p 128 x))
   :rule-classes nil))

(defbitstruct interrupt/trap-gate-descriptor-attributesBits
  :short "Subset of @(tsee interrupt/trap-gate-descriptorBits) above."
  ((ist 3bits)
   (type 4bits)
   (s bitp)
   (dpl 2bits)
   (p bitp)
   (unknownBits 5bits)) ;; TODO
  :msb-first nil
  :inline t)

(local
 (defthm interrupt/trap-gate-descriptor-attributes-layout-ok
   (iff (interrupt/trap-gate-descriptor-attributesBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

(defbitstruct gdtr/idtrBits
  :short "AMD manual, Jun'23, Vol. 2, Figure 4-8."
  ((base-addr 64bits) ;; Segment Base Address
   (limit 16bits))    ;; Segment Limit
  :msb-first nil
  :inline t)

(local
 (defthm gdtr/idtr-layout-ok
   (iff (gdtr/idtrBits-p x)
        (unsigned-byte-p 80 x))
   :rule-classes nil))

(defbitstruct code-segment-descriptorBits
  :short "AMD manual, Jun'23, Vol. 2, Figures 4-20 and 4-14."
  ((limit15-0 16bits)  ;; Ignored in 64-bit mode
   (base15-0 16bits)   ;; Ignored in 64-bit mode
   (base23-16 8bits)   ;; Ignored in 64-bit mode
   (a bitp)            ;; Ignored in 64-bit mode
   (r bitp)            ;; Ignored in 64-bit mode
   (c bitp)
   (msb-of-type bitp)  ;; must be 1
   (s bitp)            ;; S = 1 in 64-bit mode (code/data segment)
   (dpl 2bits)
   (p bitp)
   (limit19-16 4bits)  ;; Ignored in 64-bit mode
   (avl bitp)          ;; Ignored in 64-bit mode
                       ;; As per AMD manuals, this is ignored
                       ;; in 64-bit mode but the Intel manuals
                       ;; say it's not.  We're following the
                       ;; Intel manuals.
   (l bitp)
   (d bitp)
   (g bitp)            ;; Ignored in 64-bit mode
                       ;; As per AMD manuals, this is ignored
                       ;; in 64-bit mode but the Intel manuals
                       ;; say it's not.  We're following the
                       ;; Intel manuals.
   (base31-24 8bits))  ;; Ignored in 64-bit mode
  :msb-first nil
  :inline t)

(local
 (defthm code-segment-descriptor-layout-ok
   (iff (code-segment-descriptorBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct code-segment-descriptor-attributesBits
  :short "Subset of @(tsee code-segment-descriptorBits)."
  ((a bitp)
   (r bitp)
   (c bitp)
   (msb-of-type bitp) ;; must be 1
   (s bitp)           ;; S = 1 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (avl bitp)
   (l bitp)
   (d bitp)
   (g bitp)
   (unknownBits 4bits))
  :msb-first nil
  :inline t)

(local
 (defthm code-segment-descriptor-attributes-layout-ok
   (iff (code-segment-descriptor-attributesBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

(defbitstruct data-segment-descriptorBits
  :short "AMD manual, Jun'23, Vol. 2, Figures 4-21 and 4-15."
  ((limit15-0 16bits)  ;; Ignored in 64-bit mode
   (base15-0 16bits)   ;; Ignored in 64-bit mode
   (base23-16 8bits)   ;; Ignored in 64-bit mode
   (a bitp)            ;; Ignored in 64-bit mode
   (w bitp)            ;; Ignored in 64-bit mode
   (e bitp)            ;; Ignored in 64-bit mode
   (msb-of-type bitp)  ;; must be 0
   (s bitp)            ;; S = 1 in 64-bit mode (code/data segment)
   (dpl 2bits)         ;; Ignored in 64-bit mode
   (p bitp)            ;; !! NOT IGNORED: Segment present bit !!
   (limit19-16 4bits)  ;; Ignored in 64-bit mode
   (avl bitp)
   (l bitp)            ;; L = 1 in 64-bit mode
   (d/b bitp)          ;; Ignored in 64-bit mode
   (g bitp)            ;; Ignored in 64-bit mode
   (base31-24 8bits))  ;; Ignored in 64-bit mode
  :msb-first nil
  :inline t)

(local
 (defthm data-segment-descriptor-layout-ok
   (iff (data-segment-descriptorBits-p x)
        (unsigned-byte-p 64 x))
   :rule-classes nil))

(defbitstruct data-segment-descriptor-attributesBits
  :short "Subset of @(tsee data-segment-descriptorBits)."
  ((a bitp)
   (w bitp)
   (e bitp)
   (msb-of-type bitp) ;; must be 0
   (s bitp)           ;; S = 1 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (avl bitp)
   (l bitp)
   (d/b bitp)
   (g bitp)
   (unknownBits 4bits))
  :msb-first nil
  :inline t)

(local
 (defthm data-segment-descriptor-attributes-layout-ok
   (iff (data-segment-descriptor-attributesBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

;; System-Segment descriptors (64-bit mode): Note that the following
;; layouts are different in 32-bit mode, or even in compatibility mode.

(defbitstruct system-segment-descriptorBits
  :short "AMD manual, Jun'23, Vol. 2, Figure 4-22."
  ((limit15-0 16bits)
   (base15-0 16bits)
   (base23-16 8bits)
   (type 4bits)
   (s bitp) ;; S = 0 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (limit19-16 4bits)
   (avl bitp)
   (res1 2bits) ;; L and D/B bits are ignored.
   (g bitp)
   (base31-24 8bits)
   (base63-32 32bits)
   (res2 8bits)
   (all-zeroes? 5bits) ;; Check whether these are all zeroes or not.
   (res3 19bits))
  :msb-first nil
  :inline t)

(local
 (defthm system-segment-descriptor-layout-ok
   (iff (system-segment-descriptorBits-p x)
        (unsigned-byte-p 128 x))
   :rule-classes nil))

(defbitstruct system-segment-descriptor-attributesBits
  :short "Subset of @(tsee system-segment-descriptorBits)."
  ((type 4bits)
   (s bitp) ;; S = 0 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (avl bitp)
   (g bitp)
   (unknownBits 6bits))
  :msb-first nil
  :inline t)

(local
 (defthm system-segment-descriptor-attributes-layout-ok
   (iff (system-segment-descriptor-attributesBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

(defbitstruct call-gate-descriptorBits
  :short "AMD manual, Jun'23, Vol. 2, Figure 4-23."
  ((offset15-0 16bits)
   (selector 16bits)
   (res1 8bits)
   (type 4bits)
   (s bitp) ;; S = 0 in 64-bit mode
   (dpl 2bits)
   (p bitp)
   (offset31-16 16bits)
   (offset63-32 32bits)
   (res2 8bits)
   (all-zeroes? 5bits) ;; Check whether these are all zeroes or not.
   (res3 19bits))
  :msb-first nil
  :inline t)

(local
 (defthm call-gate-descriptor-layout-ok
   (iff (call-gate-descriptorBits-p x)
        (unsigned-byte-p 128 x))
   :rule-classes nil))

(defbitstruct call-gate-descriptor-attributesBits
  :short "Subset of @(tsee call-gate-descriptorBits)."
  ((type 4bits)
   (s bitp)
   (dpl 2bits)
   (p bitp)
   (unknownBits 8bits))
  :msb-first nil
  :inline t)

(local
 (defthm call-gate-descriptor-attributes-layout-ok
   (iff (call-gate-descriptor-attributesBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------
