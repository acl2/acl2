;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; This book contains the specification of the following instructions:
;; add  adc  sub  sbb  or  and  xor  cmp  test

(in-package "X86ISA")

(include-book "../x86-decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; SPECIFICATION: ADD
;; ======================================================================

(define gpr-add-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-add-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "add-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
	 ((dst            :type (unsigned-byte ,result-nbits))
	  (src            :type (unsigned-byte ,result-nbits))
	  (input-rflags   :type (unsigned-byte 32)))
	 :inline t

	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      (raw-result (the (unsigned-byte ,(1+ result-nbits))
			    (+ (the (unsigned-byte ,result-nbits) dst)
			       (the (unsigned-byte ,result-nbits) src))))
	      (signed-raw-result
	       (the (signed-byte ,(1+ result-nbits))
		 (+ (the (signed-byte ,result-nbits)
		      (,ntoi dst))
		    (the (signed-byte ,result-nbits)
		      (,ntoi src)))))

	      (result (the (unsigned-byte ,result-nbits)
			(n-size ,result-nbits raw-result)))

	      (cf (the (unsigned-byte 1) (,cf-spec-fn raw-result)))
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      (af (the (unsigned-byte 1) (,af-spec-fn dst src)))
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :af af
				  (!rflags-slice
				   :zf zf
				   (!rflags-slice
				    :sf sf
				    (!rflags-slice
				     :of of input-rflags))))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      ;; No undefined flags.
	      (undefined-flags 0))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))))

(make-event (gpr-add-spec-gen-fn 1))
(make-event (gpr-add-spec-gen-fn 2))
(make-event (gpr-add-spec-gen-fn 4))
(make-event (gpr-add-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: ADC
;; ======================================================================

(define gpr-adc-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-adc-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "adc-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
	 ((dst           :type (unsigned-byte ,result-nbits))
	  (src           :type (unsigned-byte ,result-nbits))
	  (input-rflags  :type (unsigned-byte 32)))

	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))
	      (input-cf (the (unsigned-byte 1)
			  (rflags-slice :cf input-rflags)))

	      (raw-result (the (unsigned-byte ,(1+ result-nbits))
			    (+
			     (the (unsigned-byte ,result-nbits) dst)
			     (the (unsigned-byte ,result-nbits) src)
			     (the (unsigned-byte 1) input-cf))))
	      (signed-raw-result
	       (the (signed-byte ,(1+ result-nbits))
		 (+ (the (signed-byte ,result-nbits)
		      (,ntoi dst))
		    (the (signed-byte ,result-nbits)
		      (,ntoi src))
		    (the (unsigned-byte 1)
		      input-cf))))

	      (result (the (unsigned-byte ,result-nbits)
			(n-size ,result-nbits raw-result)))

	      (cf (the (unsigned-byte 1) (,cf-spec-fn raw-result)))
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      (af (the (unsigned-byte 1) (,af-spec-fn dst src input-cf)))
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :af af
				  (!rflags-slice
				   :zf zf
				   (!rflags-slice
				    :sf sf
				    (!rflags-slice
				     :of of input-rflags))))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags 0))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))))

(make-event (gpr-adc-spec-gen-fn 1))
(make-event (gpr-adc-spec-gen-fn 2))
(make-event (gpr-adc-spec-gen-fn 4))
(make-event (gpr-adc-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: SUB
;; ======================================================================

;; The SUB instruction performs integer subtraction. It evaluates the
;; result for both signed and unsigned integer operands and sets the
;; OF and CF flags to indicate an overflow in the signed or unsigned
;; result, respectively. The SF flag indicates the sign of the signed
;; result.

;; (include-book "centaur/gl/gl" :dir :system)

;; (def-gl-thm sub-signed-and-unsigned-check
;;   :hyp (and (n32p x)
;;             (n32p y))
;;   :concl (equal (n32 (- (n32-to-i32 x) (n32-to-i32 y)))
;;                 (n32 (- x y)))
;;   :g-bindings `((x (:g-number ,(gl-int 0 2 33)))
;;                 (y (:g-number ,(gl-int 1 2 33)))))


(define gpr-sub-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-sub-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (?cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "sub-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
	 ((dst          :type (unsigned-byte ,result-nbits))
	  (src          :type (unsigned-byte ,result-nbits))
	  (input-rflags :type (unsigned-byte 32)))

	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      (signed-raw-result
	       (the (signed-byte ,(1+ result-nbits))
		 (- (the (signed-byte ,result-nbits)
		      (,ntoi dst))
		    (the (signed-byte ,result-nbits)
		      (,ntoi src)))))

	      (result (the (unsigned-byte ,result-nbits)
			(n-size ,result-nbits signed-raw-result)))

	      (cf (the (unsigned-byte 1) (acl2::bool->bit (< dst src))))
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      (af (the (unsigned-byte 1) (,af-spec-fn dst src)))
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :af af
				  (!rflags-slice
				   :zf zf
				   (!rflags-slice
				    :sf sf
				    (!rflags-slice
				     :of of input-rflags))))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags 0))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (gpr-sub-spec-gen-fn 1))
(make-event (gpr-sub-spec-gen-fn 2))
(make-event (gpr-sub-spec-gen-fn 4))
(make-event (gpr-sub-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: SBB
;; ======================================================================

(define gpr-sbb-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-sbb-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (ntoi (mk-name "N" str-nbits "-TO-I" str-nbits))
       (?cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (af-spec-fn (mk-name "sbb-af-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits))
       (of-spec-fn (mk-name "of-spec" result-nbits)))


      `(define ,fn-name
	 ((dst          :type (unsigned-byte ,result-nbits))
	  (src          :type (unsigned-byte ,result-nbits))
	  (input-rflags :type (unsigned-byte 32)))
	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))
	      (input-cf (the (unsigned-byte 1)
			  (rflags-slice :cf input-rflags)))

	      (signed-raw-result
	       (the (signed-byte ,(+ 2 result-nbits))
		 (- (the (signed-byte ,result-nbits)
		      (,ntoi dst))
		    (the (signed-byte ,(1+ result-nbits))
		      (+ (the (signed-byte ,result-nbits)
			   (,ntoi src))
			 input-cf)))))

	      (result (the (unsigned-byte ,result-nbits)
			(n-size ,result-nbits signed-raw-result)))

	      (cf (the (unsigned-byte 1)
		    (acl2::bool->bit
		     (< dst
			(the (unsigned-byte ,(1+ result-nbits))
			  (+ input-cf src))))))
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      (af (the (unsigned-byte 1) (,af-spec-fn dst src input-cf)))
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of (the (unsigned-byte 1) (,of-spec-fn signed-raw-result)))

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :af af
				  (!rflags-slice
				   :zf zf
				   (!rflags-slice
				    :sf sf
				    (!rflags-slice
				     :of of input-rflags))))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags 0))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src cf))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (gpr-sbb-spec-gen-fn 1))
(make-event (gpr-sbb-spec-gen-fn 2))
(make-event (gpr-sbb-spec-gen-fn 4))
(make-event (gpr-sbb-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: OR
;; ======================================================================

(define gpr-or-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-or-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits)))


      `(define ,fn-name
	 ((dst           :type (unsigned-byte ,result-nbits))
	  (src           :type (unsigned-byte ,result-nbits))
	  (input-rflags  :type (unsigned-byte 32)))
	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      ((the (unsigned-byte ,result-nbits) result)
	       (mbe :logic (part-select (logior dst src)
					:low 0 :width ,result-nbits)
		    :exec (logior dst src)))

	      (cf 0)
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      ;; AF is undefined.
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of 0)

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :zf zf
				  (!rflags-slice
				   :sf sf
				   (!rflags-slice
				    :of of input-rflags)))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      ;; AF is undefined.
	      (undefined-flags (!rflags-slice :af 1 0)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (gpr-or-spec-gen-fn 1))
(make-event (gpr-or-spec-gen-fn 2))
(make-event (gpr-or-spec-gen-fn 4))
(make-event (gpr-or-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: AND
;; ======================================================================

(define gpr-and-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-and-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (?cf-spec-fn (mk-name "cf-spec" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits)))


      `(define ,fn-name
	 ((dst          :type (unsigned-byte ,result-nbits))
	  (src          :type (unsigned-byte ,result-nbits))
	  (input-rflags :type (unsigned-byte 32)))
	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      ((the (unsigned-byte ,result-nbits) result)
	       (mbe :logic (part-select (logand dst src)
					:low 0 :width ,result-nbits)
		    :exec (logand dst src)))

	      (cf 0)
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      ;; AF is undefined
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of 0)

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :zf zf
				  (!rflags-slice
				   :sf sf
				   (!rflags-slice
				    :of of input-rflags)))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      ;; AF is undefined.
	      (undefined-flags (!rflags-slice :af 1 0)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (gpr-and-spec-gen-fn 1))
(make-event (gpr-and-spec-gen-fn 2))
(make-event (gpr-and-spec-gen-fn 4))
(make-event (gpr-and-spec-gen-fn 8))

;; ======================================================================
;; SPECIFICATION: XOR
;; ======================================================================

(define gpr-xor-spec-gen-fn ((operand-size :type (member 1 2 4 8)))
  :verify-guards nil

  (b* ((fn-name (mk-name "gpr-xor-spec-" operand-size))
       (result-nbits (ash operand-size 3))
       (str-nbits (if (eql result-nbits 8) "08" result-nbits))
       (pf-spec-fn (mk-name "pf-spec" result-nbits))
       (sf-spec-fn (mk-name "sf-spec" result-nbits)))


      `(define ,fn-name
	 ((dst          :type (unsigned-byte ,result-nbits))
	  (src          :type (unsigned-byte ,result-nbits))
	  (input-rflags :type (unsigned-byte 32)))
	 :parents (,(mk-name "gpr-arith/logic-spec-" operand-size))
	 :inline t

	 (b* ((dst (mbe :logic (n-size ,result-nbits dst)
			:exec dst))
	      (src (mbe :logic (n-size ,result-nbits src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      ((the (unsigned-byte ,result-nbits) result)
	       (mbe :logic (part-select (logxor dst src)
					:low 0 :width ,result-nbits)
		    :exec (logxor dst src)))

	      (cf 0)
	      (pf (the (unsigned-byte 1) (,pf-spec-fn result)))
	      ;; AF is undefined.
	      (zf (the (unsigned-byte 1) (zf-spec result)))
	      (sf (the (unsigned-byte 1) (,sf-spec-fn result)))
	      (of 0)

	      (output-rflags (the (unsigned-byte 32)
			       (!rflags-slice
				:cf cf
				(!rflags-slice
				 :pf pf
				 (!rflags-slice
				  :zf zf
				  (!rflags-slice
				   :sf sf
				   (!rflags-slice
				    :of of input-rflags)))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      ;; AF is undefined.
	      (undefined-flags (!rflags-slice :af 1 0)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,result-nbits
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
	   :gen-type t
	   :gen-linear t
	   :hints-l (("Goal"
		      :in-theory
		      (e/d (unsigned-byte-p)
			   (acl2::unsigned-byte-p-of-logxor)))))

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (gpr-xor-spec-gen-fn 1))
(make-event (gpr-xor-spec-gen-fn 2))
(make-event (gpr-xor-spec-gen-fn 4))
(make-event (gpr-xor-spec-gen-fn 8))

;; ======================================================================

(defun gpr-arith/logic-spec-gen-fn (operand-size)

  (declare (type (member 1 2 4 8) operand-size)
	   (xargs :verify-guards nil))

  (b* ((fn-name          (mk-name "gpr-arith/logic-spec-" operand-size))
       (gpr-add-spec-fn  (mk-name "gpr-add-spec-"   operand-size))
       (gpr-adc-spec-fn  (mk-name "gpr-adc-spec-"   operand-size))
       (?gpr-sub-spec-fn  (mk-name "gpr-sub-spec-"   operand-size))
       (?gpr-sbb-spec-fn  (mk-name "gpr-sbb-spec-"   operand-size))
       (?gpr-cmp-spec-fn  (mk-name "gpr-cmp-spec-"   operand-size))
       (?gpr-or-spec-fn   (mk-name "gpr-or-spec-"    operand-size))
       (?gpr-and-spec-fn  (mk-name "gpr-and-spec-"   operand-size))
       (?gpr-xor-spec-fn  (mk-name "gpr-xor-spec-"   operand-size))
       (?gpr-test-spec-fn (mk-name "gpr-test-spec-"  operand-size)))

      `(define ,fn-name
	 ((operation :type (member #.*OP-ADD* #.*OP-ADC* #.*OP-SUB*
				   #.*OP-SBB* #.*OP-CMP* #.*OP-OR*
				   #.*OP-AND* #.*OP-XOR* #.*OP-TEST*))
	  (dst          :type (unsigned-byte ,(ash operand-size 3)))
	  (src          :type (unsigned-byte ,(ash operand-size 3)))
	  (input-rflags :type (unsigned-byte 32)))

	 :parents (gpr-arith/logic-spec)
	 :enabled t
	 (case operation
	   (#.*OP-ADD* ;; 0
	    (,gpr-add-spec-fn dst src input-rflags))
	   (#.*OP-OR* ;; 1
	    (,gpr-or-spec-fn dst src input-rflags))
	   (#.*OP-ADC* ;; 2
	    (,gpr-adc-spec-fn dst src input-rflags))
	   (#.*OP-AND* ;; 3
	    (,gpr-and-spec-fn dst src input-rflags))
	   (#.*OP-SUB* ;; 4
	    (,gpr-sub-spec-fn dst src input-rflags))
	   (#.*OP-XOR* ;; 5
	    (,gpr-xor-spec-fn dst src input-rflags))
	   (#.*OP-SBB* ;; 6
	    (,gpr-sbb-spec-fn dst src input-rflags))
	   (#.*OP-TEST* ;; 7
	    ;; We will re-use the AND specification here.
	    (,gpr-and-spec-fn dst src input-rflags))
	   (#.*OP-CMP* ;; 8
	    ;; We will re-use the SUB specification here.
	    (,gpr-sub-spec-fn dst src input-rflags))
	   (otherwise
	    ;; The guard will prevent us from reaching here.
	    (mv 0 0 0))))))

(make-event (gpr-arith/logic-spec-gen-fn  1))
(make-event (gpr-arith/logic-spec-gen-fn  2))
(make-event (gpr-arith/logic-spec-gen-fn  4))
(make-event (gpr-arith/logic-spec-gen-fn  8))

(defsection gpr-arith/logic-spec

  :parents (x86-instruction-semantics)
  :short "Semantics of general-purpose arithmetic and logical instructions"
  :long "<p>These instructions are:</p>
<ul>
<li>@('ADD')</li>
<li>@('ADC')</li>
<li>@('SUB')</li>
<li>@('SBB')</li>
<li>@('CMP')</li>
<li>@('OR')</li>
<li>@('AND')</li>
<li>@('XOR')</li>
<li>@('TEST')</li>
</ul>

@(def gpr-arith/logic-spec)"

  (defmacro gpr-arith/logic-spec
    (operand-size operation dst src input-rflags)
    `(case ,operand-size
       (1 (gpr-arith/logic-spec-1 ,operation ,dst ,src ,input-rflags))
       (2 (gpr-arith/logic-spec-2 ,operation ,dst ,src ,input-rflags))
       (4 (gpr-arith/logic-spec-4 ,operation ,dst ,src ,input-rflags))
       (otherwise
	(gpr-arith/logic-spec-8 ,operation ,dst ,src ,input-rflags)))))

;; ======================================================================
