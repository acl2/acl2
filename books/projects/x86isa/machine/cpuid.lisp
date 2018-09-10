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

(in-package "X86ISA")
(include-book "abstract-state") ;; Need x86p for get-cpuid-flag
(include-book "cpuid-constants")

;; Macros and functions used by utilities in dispatch.lisp to create opcode
;; dispatch functions

;; ----------------------------------------------------------------------

;; CPUID-related definitions:

(defsection cpuid
  :parents (machine opcode-maps)
  :short "Determining which CPUID features are supported in @('x86isa')"
  :long "<p>We introduce a constrained function @(tsee cpuid-flag-fn), which
  takes the following inputs:</p>

 <ol>
  <li>@('eax'): 32-bit leaf index </li>

  <li>@('ecx'): 32-bit sub-leaf index, where applicable </li>

  <li>@('reg'): index of the output general-purpose register (@('eax'),
  @('ebx'), @('ecx'), or @('edx')) </li>

  <li>@('bit'): relevant bit of @('reg') (0-63)</li>

  <li>@('x86'): the x86 state </li>
 </ol>

 <p>The only constraint about the return value of this function is that it must
 be a bit.  During proofs, you would need to add appropriate hypotheses to your
 theorems about the values returned by @('cpuid-flag-fn') for a given CPUID
 leaf, sub-leaf, and relevant output indexing information (i.e., @('reg') and
 @('bit')).  During execution, you can use @(tsee defattach) to execute this
 function.  By default, we use the function @(tsee cpuid-feature-bit-always-1)
 as an attachment --- this function always returns @('1'), i.e., all the
 features are enabled. Feel free, of course, to use your own attachment.</p>

 <p>We also provide macros --- @(tsee cpuid-flag) and @(tsee feature-flag) ---
 to access CPUID feature flags conveniently.</p>"

  (encapsulate

    (((cpuid-flag-fn * * * * x86) => *
      :formals (eax ecx reg bit x86)
      :guard (and (unsigned-byte-p 32 eax)
		  (unsigned-byte-p 32 ecx)
		  (or (equal reg #.*eax*)
		      (equal reg #.*ebx*)
		      (equal reg #.*ecx*)
		      (equal reg #.*edx*))
		  (unsigned-byte-p 6 bit)
		  (x86p x86))))

    (local
     (defun cpuid-flag-fn (eax ecx reg bit x86)
       (declare
	(ignorable eax ecx reg bit x86)
	(xargs :stobjs x86
	       :guard (x86p x86)))
       1))

    (defthm bitp-of-cpuid-flag-fn
      (bitp (cpuid-flag-fn eax ecx reg bit x86))
      :rule-classes :type-prescription))

  (define cpuid-feature-bit-always-1 ((eax :type (unsigned-byte 32))
				      (ecx :type (unsigned-byte 32))
				      (reg (or (equal reg #.*eax*)
					       (equal reg #.*ebx*)
					       (equal reg #.*ecx*)
					       (equal reg #.*edx*)))
				      (bit :type (integer 0 63))
				      x86)
    :ignore-ok t
    1)

  (defattach cpuid-flag-fn cpuid-feature-bit-always-1)

  (defmacro cpuid-flag (eax ;; CPUID leaf
			&key
			(ecx '0) ;; CPUID Sub-leaf (if any)
			(reg '0) ;; Index of the output register
			(bit '0) ;; Relevant bit of the output register
			(x86 'x86))
    ;; CPUID:

    ;; 64-bit input:
    ;; 32 bits each of eax (leaf) and possibly ecx (sub-leaf, where applicable)

    ;; 256-bit output:
    ;; 64 bits each of eax, ebx, ecx, edx

    (list 'cpuid-flag-fn eax ecx reg bit x86))

  (defmacro feature-flag (feature-flag)
    (declare (xargs :guard (member-equal feature-flag *supported-feature-flags*)))
    (case feature-flag
      (:vmx           `(cpuid-flag #ux_01             :reg #.*ecx* :bit 5))
      (:mmx           `(cpuid-flag #ux_01             :reg #.*edx* :bit 23))
      (:sse           `(cpuid-flag #ux_01             :reg #.*edx* :bit 25))
      (:sse2          `(cpuid-flag #ux_01             :reg #.*edx* :bit 26))
      (:sse3          `(cpuid-flag #ux_01             :reg #.*ecx* :bit 0))
      (:ssse3         `(cpuid-flag #ux_01             :reg #.*ecx* :bit 9))
      (:sse4.1        `(cpuid-flag #ux_01             :reg #.*ecx* :bit 19))
      (:sse4.2        `(cpuid-flag #ux_01             :reg #.*ecx* :bit 20))
      (:avx           `(cpuid-flag #ux_01             :reg #.*ecx* :bit 28))
      (:avx2          `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 5))
      (:avx512f       `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 16))
      (:avx512dq      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 17))
      (:avx512_ifma   `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 21))
      (:avx512pf      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 26))
      (:avx512er      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 27))
      (:avx512cd      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 28))
      (:avx512bw      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 30))
      (:avx512vl      `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ebx* :bit 31))
      (:avx512_vbmi   `(cpuid-flag #ux_01 :ecx #ux_00 :reg #.*ecx* :bit 1))
      (otherwise       0))))

;; ----------------------------------------------------------------------