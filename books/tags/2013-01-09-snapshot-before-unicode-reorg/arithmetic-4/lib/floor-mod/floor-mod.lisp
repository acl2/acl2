; Arithmetic-4 Library
; Copyright (C) 2008 Robert Krug <rkrug@cs.utexas.edu>
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod.lisp
;;;
;;; This is a start at a book for reasoning about floor and mod.
;;; Much of what is here is from the IHS books and modified.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(include-book "../basic-ops/building-blocks")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of alternative recursive definitions of floor and mod.
;;; Are these actually useful?

(defun floor* (x y)
  (declare (xargs :measure (abs (floor x y))
		  :hints (("Goal" :in-theory (disable denominator-plus)))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (1- (floor* (+ x y) y)))
		 ((< y x)
		  t)
		 (t
		  (1+ (floor* (- x y) y)))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (1- (floor* (+ x y) y)))
		 ((< x y)
		  t)
		 (t
		  (1+ (floor* (- x y) y)))))))

(defun mod* (x y)
  (declare (xargs :measure (abs (floor x y))
		  :hints (("Goal" :in-theory (disable denominator-plus)))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (mod* (+ x y) y))
		 ((< y x)
		  t)
		 (t
		  (mod* (- x y) y))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (mod* (+ x y) y))
		 ((< x y)
		  t)
		 (t
		  (mod* (- x y) y))))))

(defthm floor-ind
  t
  :rule-classes ((:induction :pattern (floor x y)
			     :scheme (floor* x y))))

(defthm mod-ind
  t
  :rule-classes ((:induction :pattern (mod x y)
			     :scheme (mod* x y))))

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

(defthm |(floor (+ x y) z) where (< z 0)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
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
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< z 0)
				(< z (+ (mod x z) (mod y z))))
			   (equal (floor (+ x y) z)
				  (+ (floor x z) (floor y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(< z 0)
				(<= (+ (mod x z) (mod y z)) z))
			   (equal (floor (+ x y) z)
				  (+ 1 (floor x z) (floor y z)))))))

(defthm |(floor (+ x y) z) where (< 0 z)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(< 0 z))
           (equal (floor (+ x y) z)
		  (if (< (+ (mod x z) (mod y z)) z)
		      (+ (floor x z) (floor y z))
		    (+ 1 (floor x z) (floor y z))))))

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
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= z 0)
				(< z (+ (mod x z) (mod y z))))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(rationalp (/ x z))
				(rationalp (/ y z))
				(<= z 0)
				(<= (+ (mod x z) (mod y z)) z))
			   (equal (mod (+ x y) z)
				  (+ (mod x z) (mod y z) (- z)))))))

(defthm |(mod (+ x y) z) where (<= 0 z)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(rationalp (/ x z))
                (rationalp (/ y z))
		(<= 0 z))
           (equal (mod (+ x y) z)
		  (if (< (+ (mod x z) (mod y z)) z)
		      (+ (mod x z) (mod y z))
		    (+ (mod x z) (mod y z) (- z))))))

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

(defun find-divisive-factor (x mfc state)
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
		  (if (and (proveably-non-zero 'x `((x . ,inv)) mfc state)
			   ;; prevent various odd loops
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               ((quotep (arg1 x))
		(let ((c (unquote x)))
		  (if (and (acl2-numberp c)
			   (not (equal 0 c)) ; I don't think this will happen
			   (< (abs c) 1)
			   (stable-under-rewriting-products (invert-match x)
							    mfc state))
		      (list (cons 'factor (invert-match x)))
		    nil)))
               ((eq (fn-symb (arg2 x)) 'UNARY--)
		(let ((inv (invert-match x)))
		  (if (and (proveably-non-zero 'x `((x . ,inv)) mfc state)
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                (let ((inv (invert-match x)))
		  (if (and (proveably-non-zero 'x `((x . ,inv)) mfc state)
			   (stable-under-rewriting-products inv mfc state))
		      (list (cons 'factor inv))
		    nil)))
               (t
                nil)))
	((eq (ffn-symb x) 'UNARY-/)
	 (let ((inv (invert-match x)))
	   (if (and (proveably-non-zero 'x `((x . ,inv)) mfc state)
		    (stable-under-rewriting-products inv mfc state))
	       (list (cons 'factor inv))
	     nil)))
	((eq (ffn-symb x) 'BINARY-*)
	 (let ((temp (find-divisive-factor (arg1 x) mfc state)))
	   (if temp
	       temp
	     (find-divisive-factor (arg2 x) mfc state))))
	(t
	 nil)))

(defthm |(floor (* x (/ y)) z)|
  (implies (and (rationalp (/ x y))
		(bind-free (find-divisive-factor x mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(floor x (* y (/ z)))|
  (implies (and (rationalp (/ x y))
		(bind-free (find-divisive-factor y mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (floor x y)
		  (floor (* factor x) (* factor y)))))

(defthm |(mod (* x (/ y)) z)|
  (implies (and (rationalp (/ x y))
		(bind-free (find-divisive-factor x mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm |(mod x (* y (/ z)))|
  (implies (and (rationalp (/ x y))
		(bind-free (find-divisive-factor y mfc state)
			   (factor))
		(acl2-numberp factor)
		(not (equal 0 factor)))
	   (equal (mod x y)
		  (* (/ factor) (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Un-negating the args of floor and mod

(defthm |(floor (- x) y)|
  (implies (and (rationalp (/ x y))
                (syntaxp (mostly-negative-addends-p x mfc state)))
           (equal (floor x y)
                  (if (integerp (* x (/ y)))
                      (* x (/ y))
                    (+ -1 (- (floor (- x) y)))))))

(defthm |(floor x (- y))|
  (implies (and (rationalp (/ x y))
                (syntaxp (mostly-negative-addends-p y mfc state)))
	    (equal (floor x y)
		   (if (integerp (* x (/ y)))
		       (* x (/ y))
		     (+ -1 (- (floor x (- y))))))))

(defthm |(mod (- x) y)|
  (implies (and ;(acl2-numberp y)
		(rationalp (/ x y))
                (syntaxp (mostly-negative-addends-p x mfc state)))
	   (equal (mod x y)
		  (if (integerp (/ x y))
		      (- (mod (- x) y))
		    (+ y (- (mod (- x) y))))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm |(mod x (- y))|
  (implies (and ;(acl2-numberp y)
		(rationalp (/ x y))
                (syntaxp (mostly-negative-addends-p y mfc state)))
	   (equal (mod x y)
		  (if (integerp (/ x y))
		      (mod x (- y))
		    (+ y (mod x (- y))))))
  :hints (("Goal" :in-theory (enable mod))))

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

(defthm |(mod (mod x y) z)|
  (implies (and ;(rationalp x)
		(rationalp y)
		(rationalp z)
		(equal i (/ y z))
		(integerp (* i (floor x y))))
	   (equal (mod (mod x y) z)
		  (if (equal z 0)
		      (mod x y)
		  (mod x z))))
  :hints (("Goal" :cases ((rationalp x))
	          :in-theory (enable mod))))

(defthm |(mod (floor x y) z)|
  (implies (and (rationalp x)
		(integerp y)
		(integerp z))
	   (equal (mod (floor x y) z)
		  (if (and (< z 0)
			   (not (integerp (* x (/ y))))
			   (integerp (* (/ z) (floor x y))))
		      (+ (- z)
			 (floor x y)
			 (- (* z (floor x (* y z)))))
		    (+ (floor x y)
		       (- (* z (floor x (* y z)))))))))

;;; Note how much easier this proof is than the one in
;;; ihs/quotient-remainder-lemmas.lisp

(defthm |(floor (floor x y) z)|
  (implies (and (rationalp x)
		(integerp y)
		(integerp z))
	   (equal (floor (floor x y) z)
		  (cond ((and (< z 0)
			      (not (integerp (/ x y)))
			      (integerp (/ (floor x y) z)))
			 (+ 1 (floor x (* y z))))
			(t
			 (floor x (* y z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This rule provides a very nice simplification.  We do not want to
;;; have rules like |(mod (+ x y) z)| interfere with it, so it comes
;;; later in this book.

;;; Note: My thinking in the above paragraph is faulty.  ACL2 rewrites
;;; from the inside-out.  Here is an application for outside-in
;;; rewriting that is not related to constructor/destructor
;;; reasoning, which are the commonly cited applications.

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

(defthm |(equal (mod (+ x y) z) x)|
    (implies (and (rationalp x)
		  (rationalp y)
                  (syntaxp (mod-+-cancel-0-fn x z)))
             (equal (equal (mod x y) z)
                    (and (equal (mod (- x z) y) 0)
                         (equal (mod z y) z))))
    :hints (("Goal" :cases ((rationalp z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This rule provides a very nice simplification.  We do not want to
;;; have rules like |(floor (+ x y) z)| interfere with it, so it comes
;;; later in this book.

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
                  (bind-free (floor-+-cancel-0-fn x y z mfc state)
			     (addend))
		  (equal (- (/ addend y)) z))
             (equal (equal (floor x y) z)
                    (and (integerp (/ addend y))
                         (equal (floor (+ addend x) y) 0))))
    :hints (("Goal" :use (:instance crock-529
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

(defun factors-ccc (product)
  (declare (xargs :guard (pseudo-termp product)))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (fargn product 1)
            (factors-ccc (fargn product 2)))
    (list product)))

(defun find-common-factors-1 (x-factors y-factors mfc state)
  (declare (xargs :guard (and (pseudo-term-listp x-factors)
                              (pseudo-term-listp y-factors))))
  (cond ((endp x-factors)
	 nil)
	((and (member-equal (car x-factors) y-factors)
	      (proveably-non-zero-rational 'X `((x . ,(car x-factors)))
					   mfc state)
	      (stable-under-rewriting-products (invert-match (car x-factors))
					       mfc state))
	 (list (cons 'factor (invert-match (car x-factors)))))
	(t
	 (find-common-factors-1 (cdr x-factors) y-factors mfc state))))

(defun find-common-factors (x y mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (let* ((x-factors (factors-ccc x))
         (y-factors (factors-ccc y)))
    (find-common-factors-1 x-factors y-factors mfc state)))

(defthm floor-cancel-*
    (implies (and (rationalp (/ x y))
                  (bind-free 
                   (find-common-factors x y mfc state)
                   (factor))
                  (rationalp factor)
                  (not (equal factor 0)))
             (equal (floor x y)
                    (floor (* factor x) (* factor y)))))

(defthm mod-cancel-*
    (implies (and (rationalp (/ x y))
                  (bind-free 
                   (find-common-factors x y mfc state)
                   (factor))
		  (rationalp factor)
                  (not (equal factor 0)))
             (equal (mod x y)
                    (* (/ factor)
                       (mod (* factor x) (* factor y)))))
  :hints (("Goal" :in-theory (enable mod))))

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
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
                  (rationalp (/ x y))
		  (not (equal y 0))
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
