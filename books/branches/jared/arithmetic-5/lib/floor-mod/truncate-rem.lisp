; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; truncate-rem.lisp
;;;
;;; We rewrite expressions involving truncate and rem to floor and mod
;;; respectively.  We also handle ceiling and round.
;;;
;;; The rules in this book can be rather expensive.  Perhaps they
;;; should only be enabled when things have stabilized?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod"))

(local
 (include-book "floor-mod-basic"))

(include-book "../basic-ops/building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rewrite-truncate-to-floor
  (implies (syntaxp (rewriting-goal-literal x mfc state))
	   (equal (truncate x y)
		  (cond ((not (real/rationalp (/ x y)))
			 0)
			((<= 0 (/ x y))
			 (floor x y))
			((integerp (/ x y))
			 (/ x y))
			(t
			 (+ 1 (floor x y))))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(defthm rewrite-rem-to-mod
  (implies (syntaxp (rewriting-goal-literal x mfc state))
	   (equal (rem x y)
		  (cond ((not (real/rationalp (/ x y)))
			 (if (acl2-numberp x)
			     x
			   0))
			((<= 0 (/ x y))
			 (mod x y))
			((integerp (/ x y))
			 0)
			(t
			 (- (mod x y) y)))))
  :hints (("Goal" :in-theory (e/d (mod) (truncate)))))

(defthm rewrite-ceiling-to-floor
  (implies (syntaxp (rewriting-goal-literal x mfc state))
	   (equal (ceiling x y)
		  (cond ((not (real/rationalp (/ x y)))
			 0)
			((integerp (/ x y))
			 (/ x y))
			(t
			 (+ 1 (floor x y))))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

;;; This is messy, can we do any better?

(defthm rewrite-round-to-floor
  (implies (syntaxp (rewriting-goal-literal x mfc state))
	   (equal (round x y)
		  (cond ((not (real/rationalp (/ x y)))
			 (cond ((< 1/2 (/ x y))
				1)
			       ((< (/ x y) -1/2)
				-1)
			       (t
				0)))
			((< (mod (/ x y) 1) 1/2)
			 (floor x y))
			((< 1/2 (mod (/ x y) 1))
			 (+ 1 (floor x y)))
			(t
			 (if (evenp (floor x y))
			     (floor x y)
			   (+ 1 (floor x y)))))))
  :hints (("Goal" :in-theory (e/d (floor mod) (nonnegative-integer-quotient)))))

(defthm ash-to-floor
  (implies (syntaxp (rewriting-goal-literal i mfc state))
	   (equal (ash i n)
		  (cond ((and (integerp i)
			      (integerp n))
			 (floor i (expt 2 (- n))))
			((integerp i)
			 i)
			(t
			 0))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(in-theory (disable truncate rem ceiling round ash))
