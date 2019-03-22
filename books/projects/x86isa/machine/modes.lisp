; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Kestrel Technology, LLC
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
;   Alessandro Coglio <coglio@kestrel.edu>
; Contributing Author(s):
;  Shilpi Goel <shigoel@gmail.com>

(in-package "X86ISA")

(include-book "segmentation-structures" :dir :utils)
(include-book "paging-structures" :dir :utils)
(include-book "register-readers-and-writers" :ttags (:undef-flg))
(include-book "std/bitsets/bignum-extract" :dir :system) ;; For 64-bit-modep

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

;; ======================================================================

(defxdoc x86-modes
  :parents (machine)
  :short "Modes of operation of the processor."
  :long
  "<p>
   For now we do not model in detail all the processor modes and transitions
   (see Figure 2-3 in Intel Volume 3A).
   We implicitly assume that the processor
   is always in one of the following modes:
   </p>
   <ul>
     <li>Protected mode.</li>
     <li>Compatibility mode (sub-mode of IA-32e mode).</li>
     <li>64-bit mode (sub-mode of IA-32e mode).</li>
   </ul>
   <p>
   No real-address mode, virtual-8086 mode, or system management mode for now.
   </p>")

(local (xdoc::set-default-parents x86-modes))

;; ----------------------------------------------------------------------

(define 64-bit-modep (x86)
  :parents (x86-modes)
  :short "Check whether we are in 64-bit mode."
  :long
  "<p>
   Given the above modeling assumption stated in @(see x86-modes),
   this predicate discriminates between
   64-bit mode and the other two modes (collectively, 32-bit mode).
   Based on Intel manual, Mar'17, Vol. 3A, Sec. 2.2 (near Fig. 2-3),
   the discrimination is based on the IA32_EFER.LME and CS.L bits:
   if they are both 1, we are in 64-bit mode,
   otherwise we are in 32-bit mode
   (protected mode if IA32_EFER.LME is 0,
   compatibility mode if IA32_EFER.LME is 1 and CS.L is 0;
   note that when IA32_EFER.LME is 0, CS.L should be 0,
   according to Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5).
   </p>
   <p>
   This predicate does not include state invariants such as
   the constraints imposed by the 64-bit mode consistency checks
   described in Intel manual, Mar'17, Vol. 3A, Sec. 9.8.5.
   </p>
   <p>
   This predicate is useful as a hypothesis of theorems
   about either 64-bit or 32-bit mode.
   </p>
   <p>
   Since @('(xr :msr ... x86)') returns a 64-bit value
   but the IA32_EFER register consists of 12 bits.
   So we use @(tsee n12) to make @('ia32_eferBits') functions applicable.
   </p>"

  :no-function t
  :guard-hints (("Goal" :in-theory (e/d (bitsets::bignum-extract) ())))
  (mbe
   :logic
   (b* ((ia32_efer (n12 (xr :msr #.*ia32_efer-idx* x86)))
	(ia32_efer.lma (ia32_eferBits->lma ia32_efer))
	(cs-attr (xr :seg-hidden-attr #.*cs* x86))
	(cs.l (code-segment-descriptor-attributesBits->l cs-attr)))
     (and (equal ia32_efer.lma 1)
	  (equal cs.l 1)))
   :exec
   ;; [Shilpi] During execution, include the following book for efficiency (to
   ;; decrease the bytes allocated on the heap because of all the bignum
   ;; operations). This is likely most efficient on CCL.
   ;; (include-book "std/bitsets/bignum-extract-opt" :dir :system)
   ;; Note that this book requires a trust tag.
   (b* (((the (unsigned-byte 32) ia32_efer-low-32)
	 (bitsets::bignum-extract
	  (xr :msr #.*ia32_efer-idx* x86)
	  0))
	((the (unsigned-byte 12) ia32_efer)
	 (mbe :logic (n12 ia32_efer-low-32)
	      :exec (logand #xFFF (the (unsigned-byte 32) ia32_efer-low-32))))
	(ia32_efer.lma (ia32_eferBits->lma ia32_efer))
	((the (unsigned-byte 16) cs-attr)
	 (xr :seg-hidden-attr #.*cs* x86))
	(cs.l (code-segment-descriptor-attributesBits->l cs-attr)))
     (and (equal ia32_efer.lma 1)
	  (equal cs.l 1))))
  ///

  (local (in-theory (e/d () (force (force)))))

  (defrule 64-bit-modep-of-xw ; contributed by Eric Smith
    (implies (and (not (equal fld :msr))
		  (not (equal fld :seg-hidden-attr)))
	     (equal (64-bit-modep (xw fld index value x86))
		    (64-bit-modep x86))))

  ;; (defrule 64-bit-modep-of-!flgi ; contributed by Eric Smith
  ;;   (equal (64-bit-modep (!flgi flag val x86))
  ;;          (64-bit-modep x86)))

  ;; (defrule 64-bit-modep-of-!flgi-undefined
  ;;   (equal (64-bit-modep (!flgi-undefined flg x86))
  ;;          (64-bit-modep x86))
  ;;   :enable !flgi-undefined)

  (defrule 64-bit-modep-of-write-user-rflags
    (equal (64-bit-modep (write-user-rflags vector mask x86))
	   (64-bit-modep x86))))

;; ----------------------------------------------------------------------

(define x86-operation-mode (x86)
  :short "Returns the current mode of operation of the x86 machine"
  :long "<p>We only support 64-bit, Compatibility, and 32-bit Protected Modes
  for now.</p>"
  :parents (x86-modes)
  :returns (mode natp :rule-classes (:type-prescription :rewrite))
  (cond ((64-bit-modep x86) #.*64-bit-mode*)
	;; TODO: Other modes of operation
	(t #.*compatibility-mode*))

  ///

  (defret range-of-x86-operation-mode
    (and (<= 0 mode)
	 (< mode #.*num-proc-modes*))
    :rule-classes :linear)

  (defrule x86-operation-mode-of-xw
    (implies (and (not (equal fld :msr))
		  (not (equal fld :seg-hidden-attr)))
	     (equal (x86-operation-mode (xw fld index value x86))
		    (x86-operation-mode x86))))

  ;; (defrule x86-operation-mode-of-!flgi
  ;;   (equal (x86-operation-mode (!flgi flag val x86))
  ;;          (x86-operation-mode x86)))

  ;; (defrule x86-operation-mode-of-!flgi-undefined
  ;;   (equal (x86-operation-mode (!flgi-undefined flg x86))
  ;;          (x86-operation-mode x86))
  ;;   :enable !flgi-undefined)

  (defrule x86-operation-mode-of-write-user-rflags
    (equal (x86-operation-mode (write-user-rflags vector mask x86))
	   (x86-operation-mode x86))))

;; ----------------------------------------------------------------------
