#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "hacks")

   
;Should more of less of this "C stuff" be in this library?

;;
;; C_CONDITIONAL
;;

(defund c_conditional (a b c)
  (declare (type (signed-byte 32) a)
	   (type (signed-byte 32) b)
	   (type (signed-byte 32) c))
  (if (= a 0) 
      c 
    b))

;; We want to open c_conditional when the test value is a constant, since in
;; that case we can always resolve the test.
;;
(defthm c_conditional-constant-opener
  (implies (syntaxp (quotep a))
           (equal (c_conditional a b c)
                  (if (equal a 0) c b)))
  :hints (("Goal" :in-theory (enable c_conditional))))

(defthm +_c_conditional_c_conditional_constants-2
  (implies (and (syntaxp (quotep b1))
		(syntaxp (quotep c1))
		(syntaxp (quotep b2))
		(syntaxp (quotep c2)))
	   (equal (+ (c_conditional a1 b1 c1)
		     (c_conditional a2 b2 c2)
		     z)
		  (+ (if (equal a1 0) c1 b1)
		     (if (equal a2 0) c2 b2)
		     z)))
  :hints (("Goal" :in-theory (enable c_conditional))))

;try just enabling c_conditional throughout?
(defthm sbp-c_conditional
  (implies (and (signed-byte-p n a)
		(signed-byte-p n b))
	   (signed-byte-p n (c_conditional c a b)))
  :hints (("goal" :in-theory (enable c_conditional))))

;try just enabling c_conditional throughout?
(defthm usbp-c_conditional
  (implies (and (unsigned-byte-p n a)
		(unsigned-byte-p n b))
	   (unsigned-byte-p n (c_conditional c a b)))
  :hints (("goal" :in-theory (enable c_conditional))))

(defthm loghead-c_conditional
  (equal (loghead n (c_conditional a b c))
	 (c_conditional a (loghead n b) (loghead n c)))
  :hints (("Goal" :in-theory (enable c_conditional))))

(defthmd c_conditional-to-logext-16
  (implies (unsigned-byte-p 16 y)
           (equal (c_conditional (logand 32768 y) (logior -65536 y) y)
                  (logext 16 y)))
  :hints (("goal" :in-theory (enable c_conditional))))

;;
;; C_BIT
;;

;do we ever use c_bit

;; This function is defined elsewhere.  By adding it here, we
;; make this book independent of that code.
(defund c_bit (x) (if x 1 0))

(defthm logand-c_bit
  (and (equal (logand (c_bit x) y) (b-and (c_bit x) (logcar y)))
       (equal (logand y (c_bit x)) (b-and (c_bit x) (logcar y)))
       (equal (logand (c_bit b1) (c_bit b2)) (c_bit (and b1 b2))))
  :hints (("Goal" :in-theory (enable c_bit))))


;;
;; ADD32
;;

(defund add32 (a b) 
  (declare
    (xargs :guard
	 (and (signed-byte-p 32 a)
	      (signed-byte-p 32 b))))
  (logext 32 (+ a b)))

(defthm signed-byte-p-of-add32
  (signed-byte-p 32 (add32 a b))
  :hints (("Goal" :in-theory (enable add32))))

;;
;; ADDU32
;;

;is this ever used?
;I'm somewhat surprised that this doesn't chop its result down to 32 bits or something. -ews
(defun addu32 (a b) 
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))))
  (+ a b))

;;
;; ADDU16
;;

;I'm somewhat surprised that this doesn't chop its result down to 16 bits or something. -ews
(defun addu16 (a b) 
  (declare (xargs :guard (and (unsigned-byte-p 16 a)
                              (unsigned-byte-p 16 b))))
  (+ a b))

;could make a fw-chaining rule about unsigned-byte-p of this?
(defthm integerp-of-addu16
  (implies (and (integerp a)
                (integerp b))
           (integerp (acl2::addu16 a b)))
  :hints (("Goal" :in-theory (enable acl2::addu16))))


;; ;; Due to GCL compiler limitations, logxor does not seem to get
;; ;; optimized for integers.  Thus we define xor32 and do compiler
;; ;; replacments on it.
;; ;does this ever get used?
;; (defun xor32 (a b) 
;;   (declare
;;     (xargs :guard
;; 	 (and (signed-byte-p 32 a)
;; 	      (signed-byte-p 32 b))))
;;   (logxor a b))
