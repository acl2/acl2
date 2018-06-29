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

;; This book contains the specification of the following instructions:
;; mul  imul

(in-package "X86ISA")

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(set-non-linearp t)

;; ======================================================================
;; Unsigned multiply: MUL
;; ======================================================================

(define mul-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((mask      (1- (expt 2 size)))
	 (neg-size  (- size))
	 (size*2    (* 2 size))
	 (fn-name   (mk-name "MUL-SPEC-" size))
	 (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
	(src    :type (unsigned-byte ,size)))

       :parents (mul-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
		      :exec dst))
	    (src (mbe :logic (n-size ,size src)
		      :exec src))

	    (product
	     (the (unsigned-byte ,size*2) (* dst src)))

	    (product-high
	     (mbe :logic (part-select product :low ,size :width ,size)
		  :exec (the (unsigned-byte ,size)
			  (ash (the (unsigned-byte ,size*2) product) ,neg-size))))
	    (product-low
	     (mbe :logic (part-select product :low 0 :width ,size)
		  :exec (the (unsigned-byte ,size) (logand ,mask product)))))

	   (mv product-high product-low product))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound ,size
	 :concl (mv-nth 1 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound ,size*2
	 :concl (mv-nth 2 (,fn-name dst src))
	 :hints (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
	 :gen-type t
	 :gen-linear t))
    ))

(make-event (mul-spec-gen  8))
(make-event (mul-spec-gen 16))
(make-event (mul-spec-gen 32))
(make-event (mul-spec-gen 64))

(define mul-spec
  ((size   :type (member 1 2 4 8))
   dst src)
  :guard (case size
	   (1 (and (n08p src) (n08p dst)))
	   (2 (and (n16p src) (n16p dst)))
	   (4 (and (n32p src) (n32p dst)))
	   (8 (and (n64p src) (n64p dst)))
	   (otherwise nil))

  :inline t

  :parents (instruction-semantic-functions)
  :short "Specification for the @('MUL') (unsigned multiply) instruction"

  (case size
    (1 (mul-spec-8  dst src))
    (2 (mul-spec-16 dst src))
    (4 (mul-spec-32 dst src))
    (8 (mul-spec-64 dst src))
    (otherwise (mv 0 0 0)))

  ///

  (defthm-usb mv-nth-0-mul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (ash size 3)
    :concl (mv-nth 0 (mul-spec size dst src))
    :gen-linear t
    :gen-type t)

  (defthm-usb mv-nth-1-mul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (ash size 3)
    :concl (mv-nth 1 (mul-spec size dst src))
    :gen-linear t
    :gen-type t)

  (defthm-usb mv-nth-2-mul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (* 2 (ash size 3))
    :concl (mv-nth 2 (mul-spec size dst src))
    :gen-linear t
    :gen-type t)

  )

;; ======================================================================
;; Signed multiply: IMUL
;; ======================================================================

(local
 (encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm size-of-signed-multiplication-product
    (implies (and (unsigned-byte-p size src)
		  (unsigned-byte-p size dst)
		  (natp size)
		  (< 0 size)
		  (equal size*2 (* 2 size)))
	     (signed-byte-p size*2 (* (logext size dst) (logext size src))))
    :hints (("Goal" :in-theory (e/d (logext loghead logapp logbitp)
				    ()))))))


(define imul-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((mask      (1- (expt 2 size)))
	 (neg-size  (- size))
	 (size*2    (* 2 size))
	 (fn-name   (mk-name "IMUL-SPEC-" size))
	 (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
	(src    :type (unsigned-byte ,size)))

       :parents (imul-spec)
       :guard-hints (("Goal" :in-theory
		      (e/d (n08-to-i08 n16-to-i16
				       n32-to-i32 n64-to-i64)
			   (unsigned-byte-p signed-byte-p))))

       (b* ((dst-int (the (signed-byte ,size) (ntoi ,size dst)))
	    (src-int (the (signed-byte ,size) (ntoi ,size src)))

	    (product-int (the (signed-byte ,size*2)
			   (* (the (signed-byte ,size) dst-int)
			      (the (signed-byte ,size) src-int))))
	    (product (the (unsigned-byte ,size*2) (n-size ,size*2 product-int)))

	    (product-high
	     (mbe :logic (part-select product :low ,size :width ,size)
		  :exec (the (unsigned-byte ,size)
			  (ash (the (unsigned-byte ,size*2) product) ,neg-size))))
	    (product-low
	     (mbe :logic (part-select product :low 0 :width ,size)
		  :exec (the (unsigned-byte ,size) (logand ,mask product))))

	    (product-low-int (the (signed-byte ,size)
			       (ntoi ,size product-low)))

	    (cf-and-of
	     ;; If product-low-int == product-int, then CF and OF
	     ;; should be cleared.  Otherwise, they should be set.
	     (the (unsigned-byte 1)
	       (bool->bit
		(not (equal
		      (the (signed-byte ,size) product-low-int)
		      (the (signed-byte ,size*2) product-int)))))))

	   (mv product-high product-low product cf-and-of))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound ,size
	 :concl (mv-nth 1 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound ,size*2
	 :concl (mv-nth 2 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-3-" fn-name)
	 :bound 1
	 :concl (mv-nth 3 (,fn-name dst src))
	 :gen-type t
	 :gen-linear t))
    ))


(make-event (imul-spec-gen  8))
(make-event (imul-spec-gen 16))
(make-event (imul-spec-gen 32))
(make-event (imul-spec-gen 64))


(define imul-spec
  ((size   :type (member 1 2 4 8))
   dst src)
  :guard (case size
	   (1 (and (n08p src) (n08p dst)))
	   (2 (and (n16p src) (n16p dst)))
	   (4 (and (n32p src) (n32p dst)))
	   (8 (and (n64p src) (n64p dst)))
	   (otherwise nil))

  :inline t

  :parents (instruction-semantic-functions)
  :short "Specification for the @('IMUL') (unsigned imultiply) instruction"

  (case size
    (1 (imul-spec-8  dst src))
    (2 (imul-spec-16 dst src))
    (4 (imul-spec-32 dst src))
    (8 (imul-spec-64 dst src))
    (otherwise (mv 0 0 0 0)))

  ///

  (defthm-usb mv-nth-0-imul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (ash size 3)
    :concl (mv-nth 0 (imul-spec size dst src))
    :gen-linear t
    :gen-type t)

  (defthm-usb mv-nth-1-imul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (ash size 3)
    :concl (mv-nth 1 (imul-spec size dst src))
    :gen-linear t
    :gen-type t)

  (defthm-usb mv-nth-2-imul-spec
    :hyp   (member size '(1 2 4 8))
    :bound (* 2 (ash size 3))
    :concl (mv-nth 2 (imul-spec size dst src))
    :gen-linear t
    :gen-type t)

  (defthm-usb mv-nth-3-imul-spec
    :hyp   (member size '(1 2 4 8))
    :bound 1
    :concl (mv-nth 3 (imul-spec size dst src))
    :gen-linear t
    :gen-type t)

  )

;; ======================================================================

(set-non-linearp nil)

;; ======================================================================
