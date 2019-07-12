; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :Dir :system))

;; ======================================================================
;; INSTRUCTION: BT
;; ======================================================================

(def-inst x86-bt-0F-A3
  ;; TO-DO: Speed this up!

  ;; 0F A3: BT r/m16/32/64, r16/32/64

  ;; If the bitBase is a register operand, the bitOffset can be in the
  ;; range 0 to [15, 31, 63] depending on the mode and register size.
  ;; If the bitBase is a memory address and bitOffset is a register
  ;; operand, the bitOffset can be:

  ;; Operand Size   Register bitOffset
  ;;      2          -2^15 to 2^15-1
  ;;      4          -2^31 to 2^31-1
  ;;      8          -2^63 to 2^63-1

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (e/d (segment-base-and-bounds)
					())))

  :prepwork
  ((local
    (defthm dumb-signed-byte-p-guard-lemma
      (implies (not (mv-nth 0
			    (x86-effective-addr
			     proc-mode p4 temp-rip rex-byte
			     r/m mod sib num-imm-bytes x86)))
	       (signed-byte-p 48
			      (mv-nth 2
				      (x86-effective-addr
				       proc-mode p4 temp-rip rex-byte
				       r/m mod sib num-imm-bytes x86))))))

   (local
    (in-theory (e/d ()
		    (acl2::mod-minus
		     signed-byte-p
		     unsigned-byte-p)))))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* ((p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       ((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (bitOffset (rgfi-size operand-size
			     (reg-index reg rex-byte #.*r*)
			     rex-byte
			     x86))

       ((mv flg0
	    (the (signed-byte 64) addr)
	    (the (unsigned-byte 3) increment-RIP-by)
	    x86)
	(if (equal mod #b11)
	    (mv nil 0 0 x86)
	  (let ((p4? (equal #.*addr-size-override*
			    (prefixes->adr prefixes))))
	    (x86-effective-addr proc-mode p4?
				temp-rip
				rex-byte
				r/m
				mod
				sib
				0 ;; No immediate operand
				x86))))
       ((when flg0) (!!ms-fresh :x86-effective-addr-error flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((mv flg2 bitOffset bitBase x86)
	(if (equal mod #b11)
	    ;; bitBase is a register operand.
	    (mv nil
		(mod bitOffset (ash operand-size 3))
		(rgfi-size operand-size
			   (reg-index r/m rex-byte #.*b*)
			   rex-byte
			   x86)
		x86)
	  ;; bitBase is a memory operand.
	  (b* ((bitOffset-int (case operand-size
				(1 (n08-to-i08 bitOffset))
				(2 (n16-to-i16 bitOffset))
				(4 (n32-to-i32 bitOffset))
				(t (n64-to-i64 bitOffset))))
	       (bitOffset-int-abs (abs bitOffset-int))
	       (bitNumber (mod bitOffset-int-abs 8))
	       (byte-addr (+ addr
			     (floor bitOffset-int 8)))
	       (inst-ac? (alignment-checking-enabled-p x86))
	       ((mv flg byte x86)
		(if (signed-byte-p 64 byte-addr)
		    (rme-size-opt proc-mode 1 byte-addr seg-reg :r inst-ac? x86
				  :check-canonicity t)
		  (mv (cons 'effective-address-error byte-addr) 0 x86))))
	    (mv flg bitNumber byte x86))))
       ((when flg2)
	(!!ms-fresh :rme-size-error flg2))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
	(let* ((x86 (!flgi :cf
			   (the (unsigned-byte 1) (acl2::logbit bitOffset bitBase))
			   x86))
	       (x86 (!flgi-undefined :pf x86))
	       (x86 (!flgi-undefined :af x86))
	       (x86 (!flgi-undefined :sf x86))
	       (x86 (!flgi-undefined :of x86)))
	  x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

(def-inst x86-bt-0F-BA

  ;; 0F BA/4: BT r/m16/32/64, imm8

  ;; If the bitBase is a register, the BitOffset can be in the range 0
  ;; to [15, 31, 63] depending on the mode and register size.  If the
  ;; bitBase is a memory address and bitOffset is an immediate operand,
  ;; then also the bitOffset can be in the range 0 to [15, 31, 63].

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86))

  :guard-hints (("Goal" :in-theory (enable rme-size-of-1-to-rme08)))

  :modr/m t

  :body

  ;; Note: opcode is the second byte of the two-byte opcode.

  (b* (((the (integer 1 8) operand-size)
	(select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override*
		   (prefixes->adr prefixes)))

       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))

       (inst-ac? t)
       ((mv flg0
	    bitBase
	    (the (unsigned-byte 3) increment-RIP-by)
	    (the (signed-byte 64) ?addr)
	    x86)
	(x86-operand-from-modr/m-and-sib-bytes
	 proc-mode #.*gpr-access* operand-size inst-ac?
	 nil ;; Not a memory pointer operand
	 seg-reg p4? temp-rip rex-byte r/m mod sib
	 1 ;; One-byte immediate data
	 x86))
       ((when flg0)
	(!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip increment-RIP-by x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       ((mv flg1 (the (unsigned-byte 8) bitOffset) x86)
	(rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
       ((when flg1) (!!ms-fresh :rme-size-error flg1))

       ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
	(add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
	(!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((the (integer 0 64) bitOffset)
	(mod bitOffset (the (integer 0 64) (ash operand-size 3))))

       ;; Update the x86 state:
       ;; CF affected. ZF unchanged. PF, AF, SF, and OF undefined.
       (x86
	(let* ((x86 (!flgi :cf
			   (the (unsigned-byte 1)
				(acl2::logbit bitOffset bitBase))
			   x86))
	       (x86 (!flgi-undefined :pf x86))
	       (x86 (!flgi-undefined :af x86))
	       (x86 (!flgi-undefined :sf x86))
	       (x86 (!flgi-undefined :of x86)))
	  x86))

       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
