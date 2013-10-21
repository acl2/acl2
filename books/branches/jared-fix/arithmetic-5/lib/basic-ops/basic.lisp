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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; basic.lisp
;;;
;;; This book contains the basic rules used to enforce a functional
;;; nesting order for +, -, *, and /, as well as a few other simple
;;; rules.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local 
 (include-book "../../support/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. Functional nesting order.

;;; These rules enforce the functional nesting order + - * / as well
;;; as commutative and associative rules for + and *.

;;; 1.a. + and -

;;; This rule is somewhat out of place, but I don't know where else to
;;; put it.

(defthm |(+ c (+ d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (+ c (+ d x))
		  (+ (+ c d) x))))

(defthm |(+ y x)|
    (equal (+ y x)
           (+ x y)))

(defthm |(+ y (+ x z))|
  (equal (+ y (+ x z))
         (+ x (+ y z))))

(defthm |(+ (+ x y) z)|
    (equal (+ (+ x y) z)
           (+ x (+ y z))))

;;; A ``base case'' rule.

(defthm |(+ 0 x)|
  (implies (acl2-numberp x)
           (equal (+ 0 x)
                  x)))

;;; Unary-- is idempotent.

(defthm |(- (- x))|
  (implies (acl2-numberp x)
           (equal (- (- x))
                  x)))

;;; We regard - as a unary operation (unary-- is the internal
;;; representation), and hence push it inside the binary operation +
;;; (or binary-+).

(defthm |(- (+ x y))|
  (equal (- (+ x y))
         (+ (- x) (- y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1.b. * and /

;;; This rule is somewhat out of place, but I don't know where else to
;;; put it.

(defthm |(* c (* d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c (* d x))
		  (* (* c d) x))))

(defthm |(* y x)|
    (equal (* y x)
           (* x y)))

(defthm |(* y (* x z))|
   (equal (* y (* x z))
          (* x (* y z))))

(defthm |(* (* x y) z)|
    (equal (* (* x y) z)
           (* x (* y z))))

(defthm |(* 1 x)|
  (implies (acl2-numberp x)
           (equal (* 1 x)
                  x)))

(defthm |(* 0 x)|
  (equal (* 0 x)
         0))

(defthm |(* -1 x)|
  (equal (* -1 x)
         (- x)))

;;; Unary-/ is idempotent.

(defthm |(/ (/ x))|
  (implies (acl2-numberp x)
           (equal (/ (/ x))
                  x)))

;;; We regard / as a unary operation (unary-/ is the internal
;;; representation), and hence push it inside the binary operation *
;;; (or binary-*).

(defthm |(/ (* x y))|
  (equal (/ (* x y))
	 (* (/ x) (/ y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1.c. mixed

;;; Moved to distributivity.lisp.

#|
;;; Two distributivity rules.  Note that we disable the ``built-in''
;;; rule Distributivity in top.lisp.

(defthm |(* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))

(local
 (in-theory (disable Distributivity)))

(defthm |(* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))
|#

;;; These rules might seem out of place in that they deal with
;;; cancelling like terms --- something otherwise handled elsewhere.
;;; However, by coming after (in this file) the two distributivity
;;; rules above they will help catch such forms as 
;;; (* (+ a b) (/ (+ a b))) here, rather than letting it get
;;; distributed out and then having to deal with it afterwards.  We
;;; place this comment here as a reminder of how the occasional
;;; ''extra'' rule can be a good thing.

;;; I believe that these two rules are sufficient to handle the
;;; general case, since x and (/ x) will be placed next to each other
;;; in term-order.

;;; Note that these rules does not catch such terms as
;;; (* (expt x y) (expt x (- y))) or
;;; (* (expt x y) (expt (/ x) y)).
;;; Should we try to handle these also?  Or is it reasonable to assume
;;; that |(expt x (- n))| and |(expt (/ x) n)| will obviate the need?

(defthm |(* a (/ a))|
    (implies (acl2-numberp x)
             (equal (* x (/ x))
                    (if (equal x 0)
                        0
                      1))))

(defthm |(* a (/ a) b)|
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (* x (/ x) y)
                    (if (equal x 0)
                        0
                      y))))

;;; We pull - outside of *.  These two rules are sufficient to handle
;;; the general case since ACL2 rewrites from the inside out.  Note
;;; that we specificly exclude negative constants from these rules.

(defthm |(* x (- y))|
  (implies (syntaxp (not (quotep y)))
	   (equal (* x (- y))
		  (- (* x y)))))

(defthm |(* (- x) y)|
  (implies (syntaxp (not (quotep x)))
	   (equal (* (- x) y)
		  (- (* x y)))))

;;; In the case of a product involving a constant, we prefer the
;;; constant to be negative.

(defthm |(- (* c x))|
  (implies (syntaxp (quotep c))
	   (equal (- (* c x))
		  (* (- c) x))))

;;; We pull - outside of / also.  Note that we do not need a rule
;;; analogous to |(- (* c x))| since ``execution'' will ensure that
;;; this is done automatically in that case.

(defthm |(/ (- x))|
  (implies (syntaxp (not (quotep x)))
  (equal (/ (- x))
         (- (/ x)))))
