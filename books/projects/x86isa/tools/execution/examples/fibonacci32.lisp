; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Shilpi Goel
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

(include-book "../top" :ttags :all)
(include-book "std/testing/assert" :dir :system)

(defsection fibonacci32-cosim
  :parents (concrete-simulation-examples)
  :short "Test to check if a 32-bit fibonacci program behaves as expected"
  )

(local (xdoc::set-default-parents fibonacci32-cosim))

;; (include-book "centaur/memoize/old/profile" :dir :system)

;; ======================================================================

#||

// Source program (in C):
// gcc -m32 -O2 -o fib32.o fib32.c

#include <stdio.h>
#include <stdlib.h>

long fib (int n) {
  if (n <= 0) {
    return 0;
  }
  else if (n == 1) {
    return 1;
  }
  else return (fib(n-1) + fib(n-2));
}

int main (int argc, char *argv[], char *env[]) {
  if (argc != 2) {
    printf("Error: Need one arg.\n");
    exit(1);
  }
  int n = atoi(argv[1]);
  printf("fib(%d) = %ld\n", n, fib(n));
}

||#

;; ----------------------------------------------------------------------

;; The following ACL2 representation of the fibonacci binary (with the
;; assembly instructions preserved as comments) was obtained from the
;; fibonacci machine-code program.

;; fib32.o:
;; (__TEXT,__text) section
;; _fib:
;; 00001e90	55              ; pushl	%ebp
;; 00001e91	89 e5           ; movl	%esp, %ebp
;; 00001e93	57              ; pushl	%edi
;; 00001e94	56              ; pushl	%esi
;; 00001e95	83 ec 10        ; subl	$0x10, %esp
;; 00001e98	8b 7d 08        ; movl	0x8(%ebp), %edi
;; 00001e9b	85 ff           ; testl	%edi, %edi
;; 00001e9d	7e 26           ; jle	0x1ec5
;; 00001e9f	b8 01 00 00 00  ; movl	$0x1, %eax
;; 00001ea4	83 ff 01        ; cmpl	$0x1, %edi
;; 00001ea7	74 1e   je	; 0x1ec7
;; 00001ea9	8d 47 ff        ; leal	-0x1(%edi), %eax
;; 00001eac	89 04 24        ; movl	%eax, (%esp)
;; 00001eaf	e8 dc ff ff ff  ; calll	_fib
;; 00001eb4	89 c6           ; movl	%eax, %esi
;; 00001eb6	83 c7 fe        ; addl	$-0x2, %edi
;; 00001eb9	89 3c 24        ; movl	%edi, (%esp)
;; 00001ebc	e8 cf ff ff ff  ; calll	_fib
;; 00001ec1	01 f0           ; addl	%esi, %eax
;; 00001ec3	eb 02           ; jmp	0x1ec7
;; 00001ec5	31 c0           ; xorl	%eax, %eax
;; 00001ec7	83 c4 10        ; addl	$0x10, %esp
;; 00001eca	5e              ; popl	%esi
;; 00001ecb	5f              ; popl	%edi
;; 00001ecc	5d              ; popl	%ebp
;; 00001ecd	c3              ; retl
;; 00001ece	66 90           ; nop

;; _main:
;; 00001ed0	55      pushl	%ebp
;; 00001ed1	89 e5   movl	%esp, %ebp
;; 00001ed3	57      pushl	%edi
;; 00001ed4	56      pushl	%esi
;; 00001ed5	83 ec 10        subl	$0x10, %esp
;; 00001ed8	e8 00 00 00 00  calll	0x1edd
;; 00001edd	5f      popl	%edi
;; 00001ede	83 7d 08 02     cmpl	$0x2, 0x8(%ebp)
;; 00001ee2	75 37   jne	0x1f1b
;; 00001ee4	8b 45 0c        movl	0xc(%ebp), %eax
;; 00001ee7	8b 40 04        movl	0x4(%eax), %eax
;; 00001eea	89 04 24        movl	%eax, (%esp)
;; 00001eed	e8 46 00 00 00  calll	0x1f38
;; 00001ef2	89 c6   movl	%eax, %esi
;; 00001ef4	89 34 24        movl	%esi, (%esp)
;; 00001ef7	e8 94 ff ff ff  calll	0x1e90
;; 00001efc	89 44 24 08     movl	%eax, 0x8(%esp)
;; 00001f00	89 74 24 04     movl	%esi, 0x4(%esp)
;; 00001f04	8d 87 b3 00 00 00       leal	0xb3(%edi), %eax
;; 00001f0a	89 04 24        movl	%eax, (%esp)
;; 00001f0d	e8 32 00 00 00  calll	0x1f44
;; 00001f12	31 c0   xorl	%eax, %eax
;; 00001f14	83 c4 10        addl	$0x10, %esp
;; 00001f17	5e      popl	%esi
;; 00001f18	5f      popl	%edi
;; 00001f19	5d      popl	%ebp
;; 00001f1a	c3      retl
;; 00001f1b	8d 87 c3 00 00 00       leal	0xc3(%edi), %eax
;; 00001f21	89 04 24        movl	%eax, (%esp)
;; 00001f24	e8 21 00 00 00  calll	0x1f4a
;; 00001f29	c7 04 24 01 00 00 00    movl	$0x1, (%esp)
;; 00001f30	e8 09 00 00 00  calll	0x1f3e
;; 00001f35	83 ec 04        subl	$0x4, %esp

(defconst *fibonacci-bytes*
  ;; (__TEXT,__text) section
  ;; _fib:
  (list
   #x55                     ; pushl	%ebp
   #x89 #xe5                ; movl	%esp, %ebp
   #x57                     ; pushl	%edi
   #x56                     ; pushl	%esi
   #x83 #xec #x10           ; subl	$0x10, %esp
   #x8b #x7d #x08           ; movl	0x8(%ebp), %edi
   #x85 #xff                ; testl	%edi, %edi
   #x7e #x26                ; jle	0x1ec5
   #xb8 #x01 #x00 #x00 #x00 ; movl	$0x1, %eax
   #x83 #xff #x01           ; cmpl	$0x1, %edi
   #x74 #x1e                ; je 0x1ec7
   #x8d #x47 #xff           ; leal	-0x1(%edi), %eax
   #x89 #x04 #x24           ; movl	%eax, (%esp)
   #xe8 #xdc #xff #xff #xff ; calll	_fib
   #x89 #xc6                ; movl	%eax, %esi
   #x83 #xc7 #xfe           ; addl	$-0x2, %edi
   #x89 #x3c #x24           ; movl	%edi, (%esp)
   #xe8 #xcf #xff #xff #xff ; calll	_fib
   #x01 #xf0                ; addl	%esi, %eax
   #xeb #x02                ; jmp	0x1ec7
   #x31 #xc0                ; xorl	%eax, %eax
   #x83 #xc4 #x10           ; addl	$0x10, %esp
   #x5e                     ; popl	%esi
   #x5f                     ; popl	%edi
   #x5d                     ; popl	%ebp
   #xc3                     ; retl
   #x66 #x90                ; nop
   ))

(defconst *some-main-bytes*
  (list
   ;; ...
   ;; _main:

   #x89 #xc6                 ;; movl	%eax, %esi        00001ef2
   #x89 #x34 #x24            ;; movl	%esi, (%esp)      00001ef4
   #xe8 #x94 #xff #xff #xff  ;; calll	0x1e90            00001ef7
   #x89 #x44 #x24 #x08       ;; movl	%eax, 0x8(%esp)   00001efc
   ))

(define make-fib32-addr-alst (start-addr halt-addr)
  :measure (nfix (- halt-addr start-addr))
  (if (or (not (integerp start-addr))
	  (not (integerp halt-addr))
	  (not (< start-addr halt-addr)))
      (list halt-addr)
    (cons start-addr
	  (make-fib32-addr-alst (1+ start-addr) halt-addr))))

(defconst *fibonacci32-binary*
  (append
   (pairlis$ (make-fib32-addr-alst #x00001e90  #x00001ecf)
	     *fibonacci-bytes*)
   (pairlis$ (make-fib32-addr-alst #x00001ef2  #x00001eff)
	     *some-main-bytes*)))

(define fib32 ((n natp))
  ;; Specification Function in ACL2
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
	((eql n 1) 1)
	(t (+ (fib32 (- n 1)) (fib32 (- n 2))))))

;; ======================================================================

(defconst *fib32-xrun-limit* #u_100_000_000_000)

(define check-fib32-output
  ((input        :type (unsigned-byte 8))
   (halt-address :type (signed-byte #.*max-linear-address-size*))
   (x86 "Output x86 State"))

  (cond ((or (fault x86)
	     (not (equal (ms x86)
			 `((x86-fetch-decode-execute-halt
			    :rip ,halt-address)))))

	 (cw "~|(ms x86) = ~x0 (fault x86) = ~x1~%"
	     (ms x86) (fault x86)))

	(t (let ((expected (fib32 input)))

	     (cond
	      ((equal (rgfi *eax* x86) expected)
	       (prog2$
		(cw
		 "~|(x86isa-fib ~x0) was correctly computed as ~x1.~%"
		 input
		 expected)
		t))
	      (t
	       (prog2$
		(cw
		 "~|(x86isa-fib ~x0) = ~x1, but eax is ~x2.~%"
		 input expected (rgfi *eax* x86))
		t)))))))

(define x86isa-one-fib32-cosim
  ((input         :type (unsigned-byte 8))
   (start-address :type (signed-byte #.*max-linear-address-size*))
   (halt-address  :type (signed-byte #.*max-linear-address-size*))
   (xrun-limit    :type (unsigned-byte 50))
   x86)

  (b* ((ctx __function__)
       ((mv flg x86)
	(init-x86-state
	 ;; Status (MS and fault field)
	 nil
	 start-address
	 ;; Initial values of General-Purpose Registers
	 `((#.*RAX* . ,input)
	   (#.*RBX* . #xbffff954)
	   (#.*RCX* . #xffffffff)
	   (#.*RDX* . ,input)
	   (#.*RDI* . #x00001edd)
	   (#.*RSI* . ,input)
	   (#.*RBP* . #xbffff898)
	   (#.*RSP* . #xbffff880))
	 ;; Initial values of Control Registers (already initialized in
	 ;; init-sys-view)
	 nil
	 ;; Initial values of Model-Specific Registers (already initialized
	 ;; in init-sys-view)
	 nil
	 ;; seg-visibles
	 `((#.*cs* . #x0000001b)
	   (#.*ss* . #x00000023)
	   (#.*ds* . #x00000023))

	 ;; For initial seg-hidden values:
	 ;; See segment-base-and-bounds.
	 ;; See add-to-*sp.

	 ;; seg-hidden base
	 (acons #.*cs* 0 (acons #.*ss* 0 (acons #.*ds* 0 nil)))
	 ;; seg-hidden limit
	 (acons #.*cs* #uxffff
		(acons #.*ss* #uxffff_ffff
		       (acons #.*ds* #uxffff_ffff nil)))
	 ;; seg-hidden attr
	 (acons
	  #.*cs*
	  (!code-segment-descriptor-attributesBits->d 1 0) ;; op size = 4
	  (acons
           #.*ss*
           (!data-segment-descriptor-attributesBits->w 1 0) ;; writable stack segment
           nil))
	 ;; Initial value of the Rflags Register
	 #x282
	 ;; Initial memory image
	 (acons
	  #xbffff880 ;; init value of esp (i.e., just before the call to _fib.)
	  input
	  *fibonacci32-binary*)
	 ;; x86 state
	 x86))
       ((when flg)
	(let ((x86 (!!ms-fresh :init-x86-state-error flg)))
	  (mv nil 0 x86)))
       ((mv steps x86) (time$ (x86-run-halt-count halt-address xrun-limit x86 xrun-limit)))
       (ok? (check-fib32-output input halt-address x86))
       ((unless ok?) (mv nil 0 x86)))
    (mv t steps x86)))

(define run-x86isa-fib32
  ((input         :type (unsigned-byte 8))
   (start-address :type (signed-byte #.*max-linear-address-size*))
   (halt-address  :type (signed-byte #.*max-linear-address-size*))
   (xrun-limit    :type (unsigned-byte 50))
   x86)

  (if (zp input)

      (mv t 0 x86)

    (b* (((mv flg steps x86)
	  (x86isa-one-fib32-cosim
	   (1- input) start-address halt-address xrun-limit x86))
	 ((unless flg)
	  (cw "~% Mismatch found!~%")
	  (mv flg 0 x86))
	 (- (cw "Input: ~p0 Steps: ~p1 ~%" input steps)))

      (run-x86isa-fib32
       (1- input) start-address halt-address xrun-limit x86))))

;; ----------------------------------------------------------------------

;; For efficient execution of 64-BIT-MODEP and SEGMENT-BASE-AND-BOUNDS:
(local (include-book "std/bitsets/bignum-extract-opt" :dir :system))

;; One run:
;; (b* ((start-address #x00001ef7) ;; address of call _fib (in main)
;;      (halt-address  #x00001efc) ;; address of instruction following call _fib (in main)
;;      (input         30)
;;      ((mv flg steps x86)
;;       (x86isa-one-fib32-cosim
;;        input start-address halt-address *fib32-xrun-limit* x86)))
;;   (mv flg steps x86))

;; Multiple runs:
(acl2::assert!-stobj
 (b* ((start-address #x00001ef7)
      (halt-address  #x00001efc)
      (input         20)
      ((mv flg & x86)
       (run-x86isa-fib32
	input start-address halt-address *fib32-xrun-limit* x86)))
   (mv flg x86))
 x86)

;; ----------------------------------------------------------------------
