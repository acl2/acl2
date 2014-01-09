; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; logand-helper.lisp
;;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "more-floor-mod"))

(local
 (include-book "floor-mod"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "truncate-rem"))

(local
 (set-default-hints '((nonlinearp-default-hint
		       stable-under-simplificationp hist pspv))))



(local (in-theory (disable not-integerp-type-set-rules
                           integerp-mod-1
                           integerp-mod-2
                           integerp-mod-3
                           mod-bounds-1
                           |(floor (+ x y) z) where (< 0 z)|
                           REDUCE-ADDITIVE-CONSTANT-<
                           default-times-1
                           default-times-2
                           MOD-X-Y-=-X-Y
                           MOD-X-Y-=-X+Y
                           cancel-mod-+
                           default-plus-1
                           default-plus-2
                           default-floor-1
                           default-floor-2
                           linear-floor-bounds-1
                           linear-floor-bounds-2
                           linear-floor-bounds-3
                           EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                           EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                           )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (encapsulate
  ((op (x y) t))

  (local
   (defun op (x y)
     (+ x y)))

  (defthm op-comm
    (equal (op y x)
	   (op x y)))

  (defthm op-assoc
    (equal (op (op x y) z)
	   (op x (op y z))))
  ))

(local
 (defthm op-comm-2
   (equal (op y (op x z))
	  (op x (op y z)))
   :hints (("Goal" :in-theory (disable op-comm
				       op-assoc)
	    :use ((:instance op-assoc
			     (x y)
			     (y x)
			     (z z))
		  (:instance op-comm)
		  (:instance op-assoc))))))

(defthm |(equal (logand x y) -1)|
  (equal (equal (logand x y) -1)
	 (and (equal x -1)
	      (equal y -1))))

(local
 (defthm logand-=-0-crock-a
   (implies (equal (logand y z) 0)
	    (equal (logand (logand x y) z) 0))))

(defthm logand-assoc
  (equal (logand (logand x y) z)
	 (logand x (logand y z)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm logand-y-x
  (equal (logand y x)
	 (logand x y)))

(defthm logand-y-x-z
  (equal (logand y x z)
	 (logand x y z))
  :hints (("Goal" :use (:functional-instance
			op-comm-2
			(op binary-logand)))))


