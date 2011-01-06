; Arithmetic-5 Library
; Copyright (C) 2009 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod.lisp
;;;
;;; This is a start at a book for reasoning about floor and mod.
;;; Much of what is here is from the IHS books and modified.
;;;
;;; Rules based on:
;;;
;;; (thm
;;;  (implies (and (rationalp x)
;;; 	       (rationalp y)
;;; 	       (rationalp z)
;;; 	       (not (equal 0 x)))
;;; 	  (equal (floor (* x y) (* x z))
;;; 		 (floor y z))))
;;;
;;; (thm
;;;  (implies (and (rationalp x)
;;; 	       (rationalp y)
;;; 	       (rationalp z)
;;; 	       (not (equal 0 x)))
;;; 	  (equal (mod (* x y) (* x z))
;;; 		 (* x (mod y z))))
;;;  :hints (("Goal" :in-theory (enable mod))))
;;;
;;; are analogous to rules in simple-equalities-and-inequalities.lisp
;;; and simplify.lisp.  It would be good to take advantage of this by
;;; reusing definitions and making theories such as scatter-exponents
;;; or prefer-positive-exponents have similar affects on floor and
;;; mod.  Presently, this is rather a mess.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(include-book "../basic-ops/building-blocks")

(include-book "../basic-ops/common")

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "forcing-types"))

(local
 (include-book "floor-mod-helper"))

(local
 (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp 
					       hist pspv))))


;; Jared added this to speed up the proofs

(local (defthm acl2-count-of-cdr-weak
         (<= (acl2-count (cdr x))
             (acl2-count x))
         :rule-classes ((:rewrite) (:linear))))

(local (defthm acl2-count-of-cdr-strong
         (implies (consp x)
                  (< (acl2-count (cdr x))
                     (acl2-count x)))
         :rule-classes ((:rewrite) (:linear))))

(local (defthm acl2-count-of-car-weak
         (<= (acl2-count (car x))
             (acl2-count x))
         :rule-classes ((:rewrite) (:linear))))

(local (defthm acl2-count-of-car-strong
         (implies (consp x)
                  (< (acl2-count (car x))
                     (acl2-count x)))
         :rule-classes ((:rewrite) (:linear))))

(local (defthm acl2-count-positive-when-consp
         (implies (consp x)
                  (< 0 (acl2-count x)))
         :rule-classes :type-prescription))

(local (defthm equal-of-acl2-count-of-cdr
         (implies (equal (acl2-count x) (acl2-count (cdr x)))
                  (not (consp x)))
         :rule-classes :forward-chaining))

(local (in-theory (disable not-integerp-type-set-rules
                           mod-x-y-=-x+y
                           simplify-terms-such-as-ax+bx-=-0
                           reduce-additive-constant-equal
                           floor-zero
                           floor-=-x/y
                           simplify-products-gather-exponents-<

                           integerp-mod-1
                           integerp-mod-2
                           integerp-mod-3
                           expt-type-prescription-nonpositive-base-odd-exponent
                           expt-type-prescription-nonpositive-base-even-exponent
                           expt-type-prescription-negative-base-odd-exponent
                           expt-type-prescription-negative-base-even-exponent
                           expt-type-prescription-integerp-base
                           expt-type-prescription-positive-base
                           expt-type-prescription-integerp-base-b
                           expt-type-prescription-integerp-base-a
                           default-plus-1
                           default-plus-2
                           default-times-1
                           default-times-2
                           default-divide
                           default-minus
                           default-expt-1
                           default-expt-2
                           default-mod-2
                           mod-positive
                           mod-negative
                           mod-nonpositive
                           mod-x-y-=-x-y
                           floor-zero
                           mod-zero
                           rationalp-x
                           integerp-/-expt-2
                           floor-positive
                           floor-negative

                           acl2-numberp-x
                           integer-abs
                           acl2-count
                           numeric-constant-p
                           meta-rationalp-correct
                           floor-=-x/y
                           )))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of alternative recursive definitions of floor and mod.
;;; Are these actually useful?

(defun floor-rec (x y)
  (declare (xargs :measure (abs (floor x y))
		  :hints (("Goal" :in-theory (disable |(denominator (+ x r))|)))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (1- (floor-rec (+ x y) y)))
		 ((< y x)
		  t)
		 (t
		  (1+ (floor-rec (- x y) y)))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (1- (floor-rec (+ x y) y)))
		 ((< x y)
		  t)
		 (t
		  (1+ (floor-rec (- x y) y)))))))

(defun mod-rec (x y)
  (declare (xargs :measure (abs (floor x y))
		  :hints (("Goal" :in-theory (disable |(denominator (+ x r))|)))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (mod-rec (+ x y) y))
		 ((< y x)
		  t)
		 (t
		  (mod-rec (- x y) y))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (mod-rec (+ x y) y))
		 ((< x y)
		  t)
		 (t
		  (mod-rec (- x y) y))))))

(defthm floor-ind
  t
  :rule-classes ((:induction :pattern (floor x y)
			     :scheme (floor-rec x y))))

(defthm mod-ind
  t
  :rule-classes ((:induction :pattern (mod x y)
			     :scheme (mod-rec x y))))

(in-theory (disable floor-ind mod-ind))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Justifying recursion by floor

(defthm justify-floor-recursion
  (and (implies (and ;(rationalp x)
		     (< 0 x)
		     (rationalp y)
		     (< 1 y))
		(< (floor x y) x))
       (implies (and ;(rationalp x)
		     (< x -1)
		     (rationalp y)
		     (<= 2 y))
		(< x (floor x y))))
  :hints (("Subgoal 1.2.2" :cases ((< i -1))))
  :otf-flg t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Pulling + outside floor and mod.

;;; The floor-sum-cases and mod-sum-cases rules are very powerful, but
;;; cause too much case splitting for normal use, even if we limited
;;; them to when we were rewriting the goal rather than backchaining.
;;; So, we leave them disabled.

(defthm |(floor (+ x y) z)|
  (implies (and (rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (floor (+ x y) z)
		  (cond ((not (acl2-numberp z))
			 0)
			((equal z 0)
			 0)
			((< 0 z)
			 (if (< (+ (mod x z) (mod y z)) z)
			     (+ (floor x z) (floor y z))
			   (+ 1 (floor x z) (floor y z))))
			(t
			 (if (< z (+ (mod x z) (mod y z)))
			     (+ (floor x z) (floor y z))
			   (+ 1 (floor x z) (floor y z))))))))

(defthm |(floor (+ x y) z) rewriting goal literal|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (floor (+ x y) z)
		  (cond ((not (acl2-numberp z))
			 0)
			((equal z 0)
			 0)
			((< 0 z)
			 (if (< (+ (mod x z) (mod y z)) z)
			     (+ (floor x z) (floor y z))
			   (+ 1 (floor x z) (floor y z))))
			(t
			 (if (< z (+ (mod x z) (mod y z)))
			     (+ (floor x z) (floor y z))
			   (+ 1 (floor x z) (floor y z))))))))

;;; But we do include a couple of rules with less case-splitting.
;;; We use the corollaries, because we do not want to introduce
;;; unnecessary IF tests when trying to relieve hypotheses.  Linear
;;; arithmetic will be used when relieving a hypothesis, but 
;;; not when rewriting the test of an IF exprression.

(defun not-too-many-addends-1 (x n)
  (cond ((< 3 n) ; magic number
	 nil)
	((eq (fn-symb x) 'BINARY-+)
	 (not-too-many-addends-1 (arg2 x) (+ 1 n)))
	(t
	 t)))

(defun not-too-many-addends (x)
  (not-too-many-addends-1 x 0))

(defthm |(floor (+ x y) z) where (< z 0)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (not-too-many-addends y))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(< z 0))
           (equal (floor (+ x y) z)
		  (if (< z (+ (mod x z) (mod y z)))
		      (+ (floor x z) (floor y z))
		    (+ 1 (floor x z) (floor y z)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< z 0)
				(< z (+ (mod x z) (mod y z))))
			   (equal (floor (+ x y) z)
				  (+ (floor x z) (floor y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< z 0)
				(<= (+ (mod x z) (mod y z)) z))
			   (equal (floor (+ x y) z)
				  (+ 1 (floor x z) (floor y z)))))))

(defthm |(floor (+ x y) z) where (< 0 z)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (not-too-many-addends y))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(< 0 z))
           (equal (floor (+ x y) z)
		  (if (< (+ (mod x z) (mod y z)) z)
		      (+ (floor x z) (floor y z))
		    (+ 1 (floor x z) (floor y z)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< 0 z)
				(< (+ (mod x z) (mod y z)) z))
			   (equal (floor (+ x y) z)
				  (+ (floor x z) (floor y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< 0 z)
				(<= z (+ (mod x z) (mod y z))))
			   (equal (floor (+ x y) z)
				  (+ 1 (floor x z) (floor y z)))))))

(in-theory (disable  |(floor (+ x y) z)|
		     |(floor (+ x y) z) rewriting goal literal|))

;;; A special case of the above:

(defthm |(floor (+ 1 x) y)|
  (implies (and (rationalp x)
		(rationalp y)
		(< 1 y))
           (equal (floor (+ 1 x) y)
		  (if (< (+ 1 (mod x y)) y)
		      (floor x y)
		    (+ 1 (floor x y)))))
  :hints (("Goal" :in-theory (enable |(floor (+ x y) z)|))))

(defthm |(mod (+ x y) z)|
  (implies (and (rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (mod (+ x y) z)
		  (if (<= 0 z)
		      (if (< (+ (mod x z) (mod y z)) z)
			  (+ (mod x z) (mod y z))
			(+ (mod x z) (mod y z) (- z)))
		    (if (< z (+ (mod x z) (mod y z)))
			(+ (mod x z) (mod y z))
		      (+ (mod x z) (mod y z) (- z)))))))

(defthm |(mod (+ x y) z) rewriting goal literal|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (mod (+ x y) z)
		  (if (<= 0 z)
		      (if (< (+ (mod x z) (mod y z)) z)
			  (+ (mod x z) (mod y z))
			(+ (mod x z) (mod y z) (- z)))
		    (if (< z (+ (mod x z) (mod y z)))
			(+ (mod x z) (mod y z))
		      (+ (mod x z) (mod y z) (- z)))))))

(defthm |(mod (+ x y) z) where (<= z 0)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (not-too-many-addends y))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(<= z 0))
           (equal (mod (+ x y) z)
		  (if (< z (+ (mod x z) (mod y z)))
		      (+ (mod x z) (mod y z))
		    (+ (mod x z) (mod y z) (- z)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= z 0)
				(< z (+ (mod x z) (mod y z))))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= z 0)
				(<= (+ (mod x z) (mod y z)) z))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z) (- z)))))))

(defthm |(mod (+ x y) z) where (<= 0 z)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (not-too-many-addends y))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(<= 0 z))
           (equal (mod (+ x y) z)
		  (if (< (+ (mod x z) (mod y z)) z)
		      (+ (mod x z) (mod y z))
		    (+ (mod x z) (mod y z) (- z)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= 0 z)
				(< (+ (mod x z) (mod y z)) z))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (not-too-many-addends y))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= 0 z)
				(<= z (+ (mod x z) (mod y z))))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z) (- z)))))))

(in-theory (disable |(mod (+ x y) z)|
		    |(mod (+ x y) z) rewriting goal literal|))

;;; A special case of the above:
(defthm |(mod (+ 1 x) y)|
  (implies (and (rationalp x)
		(rationalp y)
		(< 1 y))
           (equal (mod (+ 1 x) y)
		  (if (< (+ 1 (mod x y)) y)
		      (+ 1 (mod x y))
		    (+ 1 (mod x y) (- y)))))
  :hints (("Goal" :in-theory (enable |(mod (+ x y) z)|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; I normalize floor and mod expressions so that the args
;;; do not contain any ``divisive'' factors.  This is similar
;;; in spirit to the reverse of the previous:
#|
(defthm rewrite-floor-x*y-z-right
  (implies (and (rationalp (/ x z))
		(rationalp (/ y z))
		(rationalp (/ (* x y) z)))
	   (equal (floor (* x y) z)
		  (floor x (/ z y)))))
|#
;;; The other possibility would be to do something similar to 
;;; the rtl books, and use fl := (floor x 1) as the primitive.

(defun find-divisive-factor (x simplep mfc state)
  (declare (xargs :guard t))
  (cond ((variablep x)
	 nil)
	((fquotep x)
	 (if (consp (cdr x))		; for the guard
	     (let ((c (unquote x)))
	       (if (and (rationalp c)
			(not (equal 0 c)) ; I don't think this will happen
			(< (abs c) 1))

;;; Note: factor is somewhat misnamed.  It should probably in
;;; inverted-factor, or some such.

		   (list (cons 'factor (invert-match x)))
		 nil))
	   nil))
	((eq (ffn-symb x) 'EXPT)
         (cond ((eq (fn-symb (arg1 x)) 'UNARY-/)
		(let ((inv (invert-match x)))
		  (if (and (if simplep
			       t
			     (proveably-non-zero 'x `((x . ,inv)) mfc state))
			   ;; prevent various odd loops
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               ((quotep (arg1 x))
		(if (consp (cdr (arg1 x)))	; for the guard
		    (let ((c (unquote (arg1 x))))
		      (if (and (rationalp c)
			       (not (equal 0 c)) ; I don't think this will happen
			       (or (< (abs c) 1)
				   (eq (fn-symb (arg2 x)) 'UNARY--)
				   (and (eq (fn-symb (arg2 x)) 'BINARY-*)
					(rational-constant-p (arg1 (arg2 x)))
					(< (unquote (arg1 (arg2 x))) 0)))
			       (stable-under-rewriting-products (invert-match x)
								mfc state))
			  (list (cons 'factor (invert-match x)))
			nil))
		  nil))
               ((eq (fn-symb (arg2 x)) 'UNARY--)
		(let ((inv (invert-match x)))
		  (if (and (if simplep
			       t
			     (proveably-non-zero 'x `((x . ,inv)) mfc state))
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                (let ((inv (invert-match x)))
		  (if (and (if simplep
			       t
			     (proveably-non-zero 'x `((x . ,inv)) mfc state))
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               (t
                nil)))
	((eq (ffn-symb x) 'UNARY-/)
	 (let ((inv (invert-match x)))
	   (if (and (if simplep
			t
		      (proveably-non-zero 'x `((x . ,inv)) mfc state))
		    (stable-under-rewriting-products inv mfc state))
	       (list (cons 'factor inv))
	     nil)))
	((eq (ffn-symb x) 'BINARY-*)
	 (let ((temp (find-divisive-factor (arg1 x) simplep mfc state)))
	   (if temp
	       temp
	     (find-divisive-factor (arg2 x) simplep mfc state))))
	(t
	 nil)))

(defthm |(floor (* x (/ y)) z) not rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep x)))  ; What should we do here?
		(syntaxp (not (rewriting-goal-literal x mfc state)))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor x nil mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(floor (* x (/ y)) z) rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep x)))
		(syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor x t mfc state)
			   (factor))
		(acl2-numberp factor)
		(case-split (not (equal 0 factor))))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(floor x (* y (/ z))) not rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep y)))
		(syntaxp (not (rewriting-goal-literal x mfc state)))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor y nil mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(floor x (* y (/ z))) rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep y)))
		(syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor y t mfc state)
			   (factor))
		(acl2-numberp factor)
		(case-split (not (equal 0 factor))))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(mod (* x (/ y)) z) not rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep x)))
		(syntaxp (not (rewriting-goal-literal x mfc state)))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor x nil mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm |(mod (* x (/ y)) z) rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep x)))
		(syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor x t mfc state)
			   (factor))
		(acl2-numberp factor)
		(case-split (not (equal 0 factor))))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm |(mod x (* y (/ z))) not rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep y)))
		(syntaxp (not (rewriting-goal-literal x mfc state)))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor y nil mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm |(mod x (* y (/ z))) rewriting-goal-literal|
  (implies (and (syntaxp (not (quotep y)))
		(syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (in-term-order-* x mfc state))
		(syntaxp (in-term-order-* y mfc state))
		(rationalp (/ x y))
		(bind-free (find-divisive-factor y t mfc state)
			   (factor))
		(acl2-numberp factor)
		(case-split (not (equal 0 factor))))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Un-negating the args of floor and mod

(defthm |(floor (- x) y)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (mostly-negative-addends-p x mfc state))
                (rationalp (/ x y)))
           (equal (floor x y)
                  (if (integerp (* x (/ y)))
                      (* x (/ y))
                    (+ -1 (- (floor (- x) y))))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p x mfc state))
				(rationalp (/ x y))
				(not (integerp (* x (/ y)))))
			   (equal (floor x y)
				  (+ -1 (- (floor (- x) y))))))))

(defthm |(floor x (- y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (mostly-negative-addends-p y mfc state))
                (rationalp (/ x y)))
	    (equal (floor x y)
		   (if (integerp (* x (/ y)))
		       (* x (/ y))
		     (+ -1 (- (floor x (- y)))))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p x mfc state))
				(rationalp (/ x y))
				(not (integerp (* x (/ y)))))
			   (equal (floor x y)
				  (+ -1 (- (floor x (- y)))))))))

(defthm |(mod (- x) y)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (mostly-negative-addends-p x mfc state))
		;(acl2-numberp y)
                (rationalp (/ x y)))
	   (equal (mod x y)
		  (if (integerp (/ x y))
		      (- (mod (- x) y))
		    (+ y (- (mod (- x) y))))))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p x mfc state))
				(integerp (* x (/ y))))
			   (equal (mod x y)
				  (- (mod (- x) y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p x mfc state))
				(rationalp (/ x y))
				(not (integerp (* x (/ y)))))
			   (equal (mod x y)
				  (+ y (- (mod (- x) y))))))))

(defthm |(mod x (- y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (mostly-negative-addends-p y mfc state))
		;(acl2-numberp y)
                (rationalp (/ x y)))
	   (equal (mod x y)
		  (if (integerp (/ x y))
		      (mod x (- y))
		    (+ y (mod x (- y))))))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p y mfc state))
				(integerp (* x (/ y))))
			   (equal (mod x y)
				  (mod x (- y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(syntaxp (mostly-negative-addends-p y mfc state))
				(rationalp (/ x y))
				(not (integerp (* x (/ y)))))
			   (equal (mod x y)
				  (+ y (mod x (- y))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Could these four rules be generalized like |(mod (mod x y) z)| and
;;; |(mod (+ x (mod a b)) y)|?

;;; Eliminating nesting of floor and mod, when possible

(defthm |(floor (mod x y) z)|
  (implies (and ;(acl2-numberp x)
		;(acl2-numberp y)
		(rationalp x)
		(rationalp y)
		(rationalp z)
		(equal i (/ y z))
		(integerp (* i (floor x y))))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

#|
I think the above rule is as good as we can do.  Although we could
derive a more general rule from the immediately below it is too messy, 
and involves  (FLOOR (* Y (FLOOR X Y)) Z) which doesn't seem to have 
an easy reduction unless the above applies anyway.

(thm
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z))
	   (equal (floor (mod x y) z)
		  xxx))
 :hints (("Goal" :in-theory (enable mod |(floor (+ x y) z)|)
                 :do-not '(generalize eliminate-destructors)))
 :otf-flg t)
|#

;;; Is this subsumed by |(mod (+ x (mod a b)) y)|?  I get so confused
;;; sometimes.

;;; Now that I have weakened it a little, can I weaken 
;;; |(mod (+ x (mod a b)) y)|?

;;; Can I weaken any of the others?



(encapsulate
 ()
 (local (in-theory (enable floor-=-x/y)))

 (defthm |(mod (mod x y) z)|
   (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                 ;;(rationalp x)
                 (rationalp y)
                 (rationalp z)
                 (equal i (/ y z))
                 (integerp (* i (floor x y))))
            (equal (mod (mod x y) z)
                   (if (equal z 0)
                       (mod x y)
                     (mod x z))))
   :hints (("Goal" :cases ((rationalp x))
            :in-theory (enable mod)))
   :rule-classes ((:rewrite)
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 ;;(rationalp x)
                                 (rationalp y)
                                 (equal z 0))
                            (equal (mod (mod x y) z)
                                   (mod x y))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 ;;(rationalp x)
                                 (rationalp y)
                                 (rationalp z)
                                 (not (equal z 0))
                                 (equal i (/ y z))
                                 (integerp (* i (floor x y))))
                            (equal (mod (mod x y) z)
                                   (mod x z)))))))

(encapsulate
 ()
 (local (in-theory (enable floor-zero
                           floor-=-x/y
                           mod-x-y-=-x+y
                           not-integerp-1a
                           not-integerp-1b
                           not-integerp-2a
                           not-integerp-2b)))

 (local (in-theory (disable mod-zero 
                            default-plus-1
                            default-plus-2
                            default-times-1
                            default-times-2
                            linear-floor-bounds-1
                            linear-floor-bounds-2)))

 (defthm |(mod (floor x y) z)|
   (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                 (rationalp x)
                 (integerp y)
                 (integerp z))
            (equal (mod (floor x y) z)
                   (cond ((integerp (* x (/ y)))
                          (* (/ y) (mod x (* y z))))
                         ((and (< z 0)
                               (integerp (* (/ z) (floor x y))))
                          (+ (- z)
                             (floor x y)
                             (- (* z (floor x (* y z))))))
                         (t
                          (+ (floor x y)
                             (- (* z (floor x (* y z)))))))))
   :rule-classes ((:rewrite)
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (< z 0)
                                 (not (integerp (* x (/ y))))
                                 (integerp (* (/ z) (floor x y))))
                            (equal (mod (floor x y) z)
                                   (+ (- z)
                                      (floor x y)
                                      (- (* z (floor x (* y z))))))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (<= 0 z))
                            (equal (mod (floor x y) z)
                                   (+ (floor x y)
                                      (- (* z (floor x (* y z))))))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (integerp (* x (/ y))))
                            (equal (mod (floor x y) z)
                                   (* (/ y) (mod x (* y z))))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (not (integerp (* (/ z) (floor x y)))))
                            (equal (mod (floor x y) z)
                                   (+ (floor x y)
                                      (- (* z (floor x (* y z)))))))))))


;;; Note how much easier this proof is than the one in
;;; ihs/quotient-remainder-lemmas.lisp

(encapsulate
 ()
 (local (in-theory (enable floor-zero floor-=-x/y
                           ;; why?
                           mod-x-y-=-x+y)))

 (defthm |(floor (floor x y) z)|
   ;; Jared 8.55 seconds
   (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                 (rationalp x)
                 (integerp y)
                 (integerp z))
            (equal (floor (floor x y) z)
                   (cond ((and (< z 0)
                               (not (integerp (/ x y)))
                               (integerp (/ (floor x y) z)))
                          (+ 1 (floor x (* y z))))
                         (t
                          (floor x (* y z))))))
   :rule-classes ((:rewrite)
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (< z 0)
                                 (not (integerp (/ x y)))
                                 (integerp (/ (floor x y) z)))
                            (equal (floor (floor x y) z)
                                   (+ 1 (floor x (* y z))))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (<= 0 z))
                            (equal (floor (floor x y) z)
                                   (floor x (* y z)))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (integerp (/ x y)))
                            (equal (floor (floor x y) z)
                                   (floor x (* y z)))))
                  (:rewrite
                   :corollary
                   (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                                 (rationalp x)
                                 (integerp y)
                                 (integerp z)
                                 (not (integerp (/ (floor x y) z))))
                            (equal (floor (floor x y) z)
                                   (floor x (* y z))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This rule provides a very nice simplification.  We do not want to
;;; have rules like |(mod (+ x y) z)| interfere with it, so it comes
;;; later in this book.

;;; Note: My thinking in the above paragraph is faulty.  ACL2 rewrites
;;; from the inside-out.  Here is an application for outside-in
;;; rewriting that is not related to constructor/destructor reasoning,
;;; which are the commonly cited applications.  I do not think this
;;; will ever get used.

;;; It is analogous to:
#|
(thm
 (implies (and (rationalp (/ x z))
	       (rationalp (/ y z)))
	  (equal (equal (mod (+ x y) z) x)
		 (and (equal (mod y z) 0)
		      (equal (mod x z) x)))))
|#

;;; Note that we don't even have to use bind-free, but can get away
;;; with syntaxp.

(defun mod-+-cancel-0-fn-1 (x z)
  (declare (xargs :guard (and (pseudo-termp x)
                              (eq (fn-symb x) 'BINARY-+))))
  (cond ((equal (fargn x 1) z)
         t)
        ((eq (fn-symb (fargn x 2)) 'BINARY-+)
         (mod-+-cancel-0-fn-1 (fargn x 2) z))
        ((equal (fargn x 2) z)
         t)
        (t
         nil)))

(defun mod-+-cancel-0-fn (x z)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (eq (fn-symb x) 'BINARY-+)
           (not (eq (fn-symb z) 'BINARY-+)))
      (mod-+-cancel-0-fn-1 x z)
    nil))

(encapsulate
 ()
 (local (in-theory (enable not-integerp-1b
                           not-integerp-2b
                           not-integerp-2a
                           not-integerp-1a)))

 (defthm |(equal (mod (+ x y) z) x)|
    (implies (and (rationalp x)
		  (rationalp y)
                  (syntaxp (mod-+-cancel-0-fn x z)))
             (equal (equal (mod x y) z)
                    (and (equal (mod (- x z) y) 0)
                         (equal (mod z y) z))))
    :hints (("Goal" :cases ((rationalp z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This rule provides a very nice simplification.  We do not want to
;;; have rules like |(floor (+ x y) z)| interfere with it, so it comes
;;; later in this book.

;;; Note: My thinking in the above paragraph is faulty.  ACL2 rewrites
;;; from the inside-out.  Here is an application for outside-in
;;; rewriting that is not related to constructor/destructor reasoning,
;;; which are the commonly cited applications.  I do not think this
;;; will ever get used.

;;; It is analogous to:
#|
(thm
 (implies (and (rationalp (/ x z))
	       (rationalp (/ y z)))
	  (equal (equal (floor (+ x y) z) (/ x z))
		 (and (integerp (/ x z))
		      (equal (floor y z) 0)))))
|#

(defun floor-+-cancel-0-fn-2 (x y z mfc state)
  (declare (xargs :guard t))
  (let ((neg-x (negate-match x)))
    (and (equal (mfc-rw+ '(EQUAL (UNARY-- (BINARY-* neg-x (UNARY-/ y)))
				 z)
			 `((neg-x . ,neg-x) (y . ,y) (z . ,z))
			 t t mfc state)
		*t*)
	 (stable-under-rewriting-sums neg-x mfc state))))

(defun floor-+-cancel-0-fn-1 (x y z mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (eq (fn-symb x) 'BINARY-+))))
  (cond ((floor-+-cancel-0-fn-2 (fargn x 1) y z mfc state)
         (list (cons 'addend (negate-match (fargn x 1)))))
        ((eq (fn-symb (fargn x 2)) 'BINARY-+)
         (floor-+-cancel-0-fn-1 (fargn x 2) y z mfc state))
        ((floor-+-cancel-0-fn-2 (fargn x 2) y z mfc state)
         (list (cons 'addend (negate-match (fargn x 2)))))
        (t
         nil)))

(defun floor-+-cancel-0-fn (x y z mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (eq (fn-symb x) 'BINARY-+)
           (not (eq (fn-symb z) 'BINARY-+)))
      (floor-+-cancel-0-fn-1 x y z mfc state)
    nil))


(local
 (defthm crock-529
   (implies (and (rationalp (/ x z))
		 (rationalp (/ y z)))
	    (equal (equal (floor (+ x y) z) (/ x z))
		   (and (integerp (/ x z))
			(equal (floor y z) 0))))
   :hints (("Goal" :cases ((< 0 z)
			   (< z 0))))
   :rule-classes nil))

(defthm |(equal (floor (+ x y) z) x)|
    (implies (and (rationalp (/ x y))
                  (syntaxp (in-term-order-+ x mfc state))
		(bind-free (floor-+-cancel-0-fn x y z mfc state)
			     (addend))
		  (equal (- (/ addend y)) z))
             (equal (equal (floor x y) z)
                    (and (integerp (/ addend y))
                         (equal (floor (+ addend x) y) 0))))
    :hints (("Goal" :in-theory (disable FLOOR-ZERO)
	            :use (:instance crock-529
				    (x addend)
				    (y (+ addend x))
				    (z y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
(thm
 (implies (and (rationalp x)
	       (rationalp y)
	       (rationalp z)
	       (not (equal 0 x)))
	  (equal (floor (* x y) (* x z))
		 (floor y z))))

(thm
 (implies (and (rationalp x)
	       (rationalp y)
	       (rationalp z)
	       (not (equal 0 x)))
	  (equal (mod (* x y) (* x z))
		 (* x (mod y z))))
 :hints (("Goal" :in-theory (enable mod))))
|#

;;; Below is from an earlier, inadequate try.  But the present regime
;;; is not much better.  Rationalize me.

#|
(defun factors-ccc (product)
  (declare (xargs :guard (pseudo-termp product)))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (fargn product 1)
            (factors-ccc (fargn product 2)))
    (list product)))

(defun find-common-factors-1 (x-factors y-factors simplep mfc state)
  (declare (xargs :guard (and (pseudo-term-listp x-factors)
                              (pseudo-term-listp y-factors))))
  (cond ((endp x-factors)
	 nil)
	((and (member-equal (car x-factors) y-factors)
	      (if simplep
		  (proveably-rational 'X `((x . ,(car x-factors)))
				      mfc state)
		(proveably-non-zero-rational 'X `((x . ,(car x-factors)))
					     mfc state))
	      (stable-under-rewriting-products (invert-match (car x-factors))
					       mfc state))
	 (list (cons 'factor (invert-match (car x-factors)))))
	(t
	 (find-common-factors-1 (cdr x-factors) y-factors simplep mfc state))))

(defun find-common-factors (x y simplep mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (let* ((x-factors (factors-ccc x))
         (y-factors (factors-ccc y)))
    (find-common-factors-1 x-factors y-factors simplep mfc state)))
|#

;;; get-the-ens-dangerously will fail if mfc is redefined.
;;; should be in axioms.lisp

(defun get-the-ens-dangerously (mfc)
  (cadr (cadddr (cddddr (cddr mfc)))))

(defun gather-or-scatter-dangerously (mfc state)
  (declare (xargs :mode :program))
  (let ((ens (get-the-ens-dangerously mfc))
	(nume (caar (getprop 'simplify-products-gather-exponents-equal 
			     'runic-mapping-pairs
			     nil
			     'current-acl2-world
			     (w state)))))
    (enabled-numep nume ens)))

(defun ugly-hack-one (lhs rhs mfc state)
  (declare (xargs :mode :program))
  (if (gather-or-scatter-dangerously mfc state)
      (find-rational-matching-factors-gather-exponents lhs rhs mfc state)
    (find-rational-matching-factors-scatter-exponents lhs rhs mfc state)))

(defun ugly-hack-two (lhs rhs mfc state)
  (declare (xargs :mode :program))
  (if (gather-or-scatter-dangerously mfc state)
      (find-non-zero-rational-matching-factors-gather-exponents lhs rhs mfc state)
    (find-non-zero-rational-matching-factors-scatter-exponents lhs rhs mfc state)))

(defthm floor-cancel-*-not-rewriting-goal-literal
    (implies (and (syntaxp (not (rewriting-goal-literal lhs mfc state)))
		  (rationalp (/ lhs rhs))
		(syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
		   (ugly-hack-two lhs rhs mfc state)
                   (x))
                  (rationalp x)
                  (not (equal x 0)))
             (equal (floor lhs rhs)
                    (floor (* x lhs) (* x rhs)))))

(defthm floor-cancel-*-rewriting-goal-literal
    (implies (and (syntaxp (rewriting-goal-literal lhs mfc state))
		  (rationalp (/ lhs rhs))
                  (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
                   (ugly-hack-one lhs rhs mfc state)
                   (x))
                  (rationalp x)
                  (case-split (not (equal x 0))))
             (equal (floor lhs rhs)
                    (floor (* x lhs) (* x rhs)))))

(defthm mod-cancel-*-not-rewriting-goal-literal
    (implies (and (syntaxp (not (rewriting-goal-literal lhs mfc state)))
		  (rationalp (/ lhs rhs))
                  (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
                   (ugly-hack-two lhs rhs mfc state)
                   (x))
		  (rationalp x)
                  (not (equal x 0)))
             (equal (mod lhs rhs)
                    (* (/ x)
                       (mod (* x lhs) (* x rhs)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-cancel-*-rewriting-goal-literal
    (implies (and (syntaxp (rewriting-goal-literal lhs mfc state))
		  (rationalp (/ lhs rhs))
                  (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
                   (ugly-hack-one lhs rhs mfc state)
                   (x))
		  (rationalp x)
                  (case-split (not (equal x 0))))
             (equal (mod lhs rhs)
                    (* (/ x)
                       (mod (* x lhs) (* x rhs)))))
  :hints (("Goal" :in-theory (enable mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; same as find-constant-factor-<

(defun find-constant-factor-floor-mod (lhs rhs)
  
  ;;

  (cond ((and (eq (fn-symb lhs) 'BINARY-*)
	      (eq (fn-symb rhs) 'BINARY-*)
	      (numeric-constant-p (arg1 lhs))
	      (numeric-constant-p (arg1 rhs)))
	 ;; (rel (* c x) (* d y))
	 (let ((c (unquote (arg1 lhs)))
	       (d (unquote (arg1 rhs))))
	   (cond ((or (eql c 0)
		      (eql (abs c) 1))
		  `((c . ,(kwote (/ d)))))
		 ((or (eql d 0)
		      (eql (abs d) 1))
		  `((c . ,(kwote (/ c)))))
		 ((< c d)
		  `((c . ,(kwote (/ c)))))
		 (t
		  `((c . ,(kwote (/ d))))))))
	((and (eq (fn-symb rhs) 'BINARY-*)
	      (numeric-constant-p lhs)
	      (numeric-constant-p (arg1 rhs)))
	 ;; (rel c (* d y))
	 (let ((c (unquote lhs))
	       (d (unquote (arg1 rhs))))
	   (cond ((or (eql c 0)
		      (eql (abs c) 1))
		  `((c . ,(kwote (/ d)))))
		 ((or (eql d 0)
		      (eql (abs d) 1))
		  `((c . ,(kwote (/ c)))))
		 ((< c d)
		  `((c . ,(kwote (/ c)))))
		 (t
		  `((c . ,(kwote (/ d))))))))
	((and (eq (fn-symb lhs) 'BINARY-*)
	      (numeric-constant-p (arg1 lhs))
	      (numeric-constant-p rhs))
	 ;; (rel (* c x) d)
	 (let ((c (unquote (arg1 lhs)))
	       (d (unquote rhs)))
	   (cond ((or (eql c 0)
		      (eql (abs c) 1))
		  `((c . ,(kwote (/ d)))))
		 ((or (eql d 0)
		      (eql (abs d) 1))
		  `((c . ,(kwote (/ c)))))
		 ((< c d)
		  `((c . ,(kwote (/ c)))))
		 (t
		  `((c . ,(kwote (/ d))))))))
	((and (eq (fn-symb rhs) 'BINARY-*)
	      (numeric-constant-p (arg1 rhs))
	      (not (eq (fn-symb (arg2 rhs)) 'BINARY-*))
	      (eq (fn-symb lhs) 'BINARY-+))
	 ;; (rel x (* d y))
	 ;; I don't think we want to do anything here, but
	 ;; I leave this as a reminder to think about it.
	 nil)
	((and (eq (fn-symb lhs) 'BINARY-*)
	      (numeric-constant-p (arg1 lhs))
	      (not (eq (fn-symb (arg2 lhs)) 'BINARY-*))
	      (eq (fn-symb rhs) 'BINARY-+))
	 ;; (rel (* d y) x)
	 ;; I don't think we want to do anything here, but
	 ;; I leave this as a reminder to think about it.
	 nil)
	((and (eq (fn-symb rhs) 'BINARY-+)
	      (eq (fn-symb lhs) 'BINARY-+))
	 ;; We could probably do something clever here, but I am not
	 ;; sure just what.
	 nil)
	(t
	 nil)))

(defthm floor-cancel-*-const
    (implies (and (rationalp (/ lhs rhs))
                  (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
                   (find-constant-factor-floor-mod lhs rhs)
                   (c))
                  (rationalp c)
                  (not (equal c 0)))
             (equal (floor lhs rhs)
                    (floor (* c lhs) (* c rhs)))))

(defthm mod-cancel-*-const
    (implies (and (rationalp (/ lhs rhs))
                  (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
                  (bind-free 
                   (find-constant-factor-floor-mod lhs rhs)
		   (c))
		  (rationalp c)
                  (not (equal c 0)))
             (equal (mod lhs rhs)
                    (* (/ c)
                       (mod (* c lhs) (* c rhs)))))
  :hints (("Goal" 
           :in-theory (e/d (mod)
                           (floor-cancel-*-const)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Cancellation

#|
(thm
 (implies (and (rationalp x)
	       (rationalp y)
	       (rationalp z)
	       (integerp (/ y z)))
	  (equal (floor (+ x y) z)
		 (+ (/ y z) (floor x z)))))

(thm
 (implies (and (rationalp x)
	       (rationalp y)
	       (rationalp z)
	       (not (equal z 0))
	       (integerp (/ y z)))
	  (equal (mod (+ x y) z)
		 (mod x z))))
|#

(defun find-cancelling-addends (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (cond ((and (proveably-integer 
		      '(BINARY-* X (UNARY-/ Y))
		      `((x . ,(negate-match (fargn x 1))) (y . ,y))
		      mfc state)
		     (stable-under-rewriting-sums (negate-match (fargn x 1))
						  mfc state))
                (list (cons 'addend (negate-match (fargn x 1)))))
               ((eq (fn-symb (fargn x 2)) 'BINARY-+)
                (find-cancelling-addends (fargn x 2) y mfc state))
               ((and (proveably-integer 
		      '(BINARY-* X (UNARY-/ Y))
		      `((x . ,(negate-match (fargn x 2))) (y . ,y))
		      mfc state)
		     (stable-under-rewriting-sums (negate-match (fargn x 2))
						  mfc state))
                (list (cons 'addend (negate-match (fargn x 2)))))
               (t
                nil)))
        ((and (proveably-integer 
	       '(BINARY-* X (UNARY-/ Y))
	       `((x . ,(negate-match x)) (y . ,y))
	       mfc state)
	      (stable-under-rewriting-sums (negate-match x) mfc state))
         (list (cons 'addend (negate-match x))))
        (t
         nil)))

(defthm cancel-floor-+
    (implies (and (rationalp (/ x y))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free 
                   (find-cancelling-addends x y mfc state)
                   (addend))
                  (equal i (/ addend y))
                  (integerp i))
             (equal (floor x y)
                    (+ (- i) (floor (+ addend x) y)))))

(defthm cancel-mod-+
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (not (equal y 0))
		  (syntaxp (not (equal x ''0)))
                  (rationalp (/ x y))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free 
                   (find-cancelling-addends x y mfc state)
                   (addend))
                  (equal i (/ addend y))
                  (integerp i))
             (equal (mod x y)
                    (mod (+ addend x) y)))
    :hints (("Goal" :in-theory (enable mod)))
    :otf-flg t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We should probably generalize these to handle cases where the
;;; inner mod is being multiplied by an integer. (constant only?)

#|
(thm
 (implies (and (rationalp x)
	       (rationalp a)
	       (rationalp b)
	       (rationalp y)
	       (not (equal y 0))
	       (integerp (/ b y)))
	  (equal (mod (+ x (mod a b)) y)
		 (mod (+ x a) y)))
 :hints (("Goal" :in-theory (enable |(mod (+ x y) z)|))))

;;; This latter one will prove after verifying 
;;; |(mod (+ x (- (mod a b))) y)|.  I should investigate why this
;;; fails if tried here.

(thm
 (implies (and (rationalp x)
	       (rationalp a)
	       (rationalp b)
	       (rationalp y)
	       (not (equal y 0))
	       (integerp (/ b y)))
	  (equal (mod (+ x (- (mod a b))) y)
		 (mod (+ x (- a)) y))))
|#

;;; Is this a simple generalization of |(mod (mod x y) z)|?  Does it 
;;; replace |(mod (mod x y) z)|?  Can we do the same for, say, 
;;; |(mod (floor x y) z)|?

(defun simplify-mod-+-mod-fn (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((arg1 (fargn x 1))
               (arg2 (fargn x 2)))
           (cond ((and (eq (fn-symb arg1) 'MOD)
                       (proveably-integer '(BINARY-* X (UNARY-/ Y))
					  `((x . ,(fargn arg1 2)) (y . ,y))
					  mfc state)
		       (stable-under-rewriting-sums (negate-match arg1)
						    mfc state))
                  (list (cons 'w (fargn arg1 1))
                        (cons 'z (fargn arg1 2))
			(cons 'term (negate-match arg1))))
                 ((eq (fn-symb arg2) 'BINARY-+)
                  (simplify-mod-+-mod-fn arg2 y mfc state))
                 ((and (eq (fn-symb arg2) 'MOD)
                       (proveably-integer '(BINARY-* X (UNARY-/ Y))
					  `((x . ,(fargn arg2 2)) (y . ,y))
					  mfc state)
		       
		       (stable-under-rewriting-sums (negate-match arg2)
						    mfc state))
                  (list (cons 'w (fargn arg2 1))
                        (cons 'z (fargn arg2 2))
			(cons 'term (negate-match arg2))))
                 (t
                  nil))))
        ((and (eq (fn-symb x) 'MOD)
              (proveably-integer '(BINARY-* X (UNARY-/ Y))
				 `((x . ,(fargn x 2)) (y . ,y))
				 mfc state)
	      (stable-under-rewriting-sums (negate-match x)
					   mfc state))
         (list (cons 'w (fargn x 1))
               (cons 'z (fargn x 2))
	       (cons 'term (negate-match x))))
        (t
         nil)))

(defthm |(mod (+ x (mod a b)) y)|
;; Jared 13.42 seconds (some gc)
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
                  (rationalp (/ x y))
		  (not (equal y 0))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free 
                   (simplify-mod-+-mod-fn x y mfc state)
                   (w z term))
		  ;; Prevent various odd loops.
		  (syntaxp (stable-under-rewriting-sums term mfc state))
		  (equal term (- (mod w z)))
                  (integerp (/ z y)))
             (equal (mod x y)
                    (mod (+ term w x) y))))

(defun simplify-mod-+-minus-mod-fn (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((arg1 (fargn x 1))
               (arg2 (fargn x 2)))
           (cond ((and (eq (fn-symb arg1) 'UNARY--)
                       (eq (fn-symb (fargn arg1 1)) 'MOD)
                       (proveably-integer '(BINARY-* X (UNARY-/ Y))
					  `((x . ,(fargn (fargn arg1 1) 2)) (y . ,y))
					  mfc state)
		       (stable-under-rewriting-sums (negate-match (fargn arg1 1))
						    mfc state))
                  (list (cons 'w (fargn (fargn arg1 1) 1))
                        (cons 'z (fargn (fargn arg1 1) 2))
			(cons 'term (negate-match arg1))))
                 ((eq (fn-symb arg2) 'BINARY-+)
                  (simplify-mod-+-minus-mod-fn arg2 y mfc state))
                 ((and (eq (fn-symb arg2) 'UNARY--)
                       (eq (fn-symb (fargn arg2 1)) 'MOD)
                       (proveably-integer '(BINARY-* X (UNARY-/ Y))
					  `((x . ,(fargn (fargn arg2 1) 2)) (y . ,y))
					  mfc state)
		       (stable-under-rewriting-sums (negate-match (fargn arg2 1))
						    mfc state))
                  (list (cons 'w (fargn (fargn arg2 1) 1))
                        (cons 'z (fargn (fargn arg2 1) 2))
			(cons 'term (negate-match arg2))))
                 (t
                  nil))))
         ((and (eq (fn-symb x) 'UNARY--)
               (eq (fn-symb (fargn x 1)) 'MOD)
	       (proveably-integer '(BINARY-* X (UNARY-/ Y))
				  `((x . ,(fargn (fargn x 1) 2)) (y . ,y))
				  mfc state)
	       (stable-under-rewriting-sums (negate-match (fargn x 1))
					    mfc state))
         (list (cons 'w (fargn (fargn x 1) 1))
               (cons 'z (fargn (fargn x 1) 2))
	       (cons 'term (negate-match (fargn x 1)))))
        (t
         nil)))

(defthm |(mod (+ x (- (mod a b))) y)|
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
                  (rationalp (/ x y))
		  (not (equal y 0))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free 
                   (simplify-mod-+-minus-mod-fn x y mfc state)
                   (w z term))
		  ;; Prevent various odd loops.
		  (syntaxp (stable-under-rewriting-sums term mfc state))
		  (equal term (mod w z))
                  (integerp (/ z y)))
             (equal (mod x y)
                    (mod (+ x (- w) term) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(thm
 (implies (and (integerp a)
               (integerp b)
               (integerp y)
               (not (equal 0 y))
               (integerp z)
               (not (equal 0 z))
               (integerp (/ y z)))
          (equal (mod (* a (mod b y)) z)
                 (mod (* a b) z))))
|#
