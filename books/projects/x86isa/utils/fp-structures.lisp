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

(include-book "utilities")
(include-book "basic-structs")

(defsection fp-bitstructs
  :parents (structures)
  :short "<b>Bitstructs related to floating-point operations</b>"
  )

(local (xdoc::set-default-parents fp-bitstructs))

;; ----------------------------------------------------------------------

(defbitstruct fp-statusBits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 1, Section 8.1.3</p>"
  ((ie bitp)    ;; Invalid Operation Flag
   (de bitp)    ;; Denormalized Operand Flag
   (ze bitp)    ;; Zero Divide Flag
   (oe bitp)    ;; Overflow Flag
   (ue bitp)    ;; Underflow Flag
   (pe bitp)    ;; Precision Flag
   (sf bitp)    ;; Stack Fault
   (es bitp)    ;; Error Summary Status
   (c0 bitp)    ;; Condition Code
   (c1 bitp)    ;; Condition Code
   (c2 bitp)    ;; Condition Code
   (top 3bits) ;; Top of stack pointer
   (c3 bitp)    ;; Condition Code
   (b bitp)     ;; FPU Busy
   )
  :msb-first nil
  :inline t)

(local
 (defthm fp-status-layout-ok
   (iff (fp-statusBits-p x)
        (unsigned-byte-p 16 x))
   :rule-classes nil))

(defbitstruct mxcsrBits
  :long "<p>Source: Intel Manual, Feb-14, Vol. 1, Section 10.2.3</p>"

  ;; MXCSR (Intel Manual, Feb-14, Vol. 1, Section 10.2.3)

  ;;    Bits 16 through 31 of the MXCSR register are reserved and are
  ;;    cleared on a power-up or reset of the processor; attempting to
  ;;    write a non-zero value to these bits, using either the FXRSTOR
  ;;    or LDMXCSR instructions, will result in a general-protection
  ;;    exception (#GP) being generated.

  ((ie bitp)          ;; Invalid Operation Flag
   (de bitp)          ;; Denormal Flag
   (ze bitp)          ;; Divide-by-Zero Flag
   (oe bitp)          ;; Overflow Flag
   (ue bitp)          ;; Underflow Flag
   (pe bitp)          ;; Precision Flag
   (daz bitp)         ;; Denormals are Zeros
   (im bitp)          ;; Invalid Operation Mask
   (dm bitp)          ;; Denormal Mask
   (zm bitp)          ;; Divide-by-Zero Mask
   (om bitp)          ;; Overflow Mask
   (um bitp)          ;; Underflow Mask
   (pm bitp)          ;; Precision Mask
   (rc 2bits)        ;; Rounding Control
   (fz bitp)          ;; Flush to Zero
   (reserved 16bits) ;; Reserved bits
   )
  :msb-first nil
  :inline t)

(local
 (defthm mxcsr-layout-ok
   (iff (mxcsrBits-p x)
        (unsigned-byte-p 32 x))
   :rule-classes nil))

;; ----------------------------------------------------------------------
