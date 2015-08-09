; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; simple-equalities-and-inequalities.lisp
;;;
;;; We take care of a few of the simple cases involving constants and
;;; other simple patterns here, rather than worry about them
;;; elsewhere.  This makes the rules in collect.lisp and
;;; normalize.lisp much simpler.  (Does it really?)
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "../../support/top"))

(local
 (include-book "simplify-helper"))

(local
 (include-book "simple-equalities-and-inequalities-helper"))

(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that for many of the rules in this library, such as the
;;; following, one cannot tell what the rule matches by examining
;;; the left-hand-side of the conclusion.  The rule |(equal (- x) c)|
;;; would appear to match on all equalities since the lhs is
;;; (equal x c).  However, the syntaxp hypotheses limit the
;;; applicability of the rule to those cases where:
;;; 1. c is a constant.  (The variables c and d will always denote
;;;    constants.)
;;; 2. The x is ``like'' (- ...) in the sense of
;;;    negative-addends-p.  The (- x) in the rhs of the
;;;    conclusion will undo this negation, not introduce it.
;;; In general, the rule's names are a good guide to what they
;;; match on.

(defthm |(equal (- x) c)|
    (implies (and (syntaxp (numeric-constant-p c))
		  (syntaxp (mostly-negative-addends-p x mfc state))
		  (acl2-numberp c)
                  (acl2-numberp x))
             (equal (equal x c)
                    (equal (- x) (- c)))))

(defthm |(equal c (- x))|
    (implies (and (syntaxp (numeric-constant-p c))
		  (syntaxp (mostly-negative-addends-p x mfc state))
		  (acl2-numberp c)
                  (acl2-numberp x))
             (equal (equal c x)
                    (equal (- x) (- c)))))

(defthm |(equal (/ x) c)|
  (implies (and (syntaxp (numeric-constant-p c))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp
		 (simplify-ok-p `(EQUAL ,x ,c)
				'(EQUAL (UNARY-/ x) (UNARY-/ c))
				`((x . ,x) (c . ,c))
				mfc state))
		(acl2-numberp c)
		(acl2-numberp x))
           (equal (equal x c)
                  (equal (/ x) (/ c)))))

(defthm |(equal c (/ x))|
  (implies (and (syntaxp (numeric-constant-p c))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp
		 (simplify-ok-p `(EQUAL ,x ,c)
				'(EQUAL (UNARY-/ x) (UNARY-/ c))
				`((x . ,x) (c . ,c))
				mfc state))
		(acl2-numberp c)
		(acl2-numberp x))
           (equal (equal c x)
                  (equal (/ x) (/ c)))))

(defthm |(equal (- x) (- y))|
    (implies (and (syntaxp (mostly-negative-addends-p x mfc state))
                  (syntaxp (mostly-negative-addends-p y mfc state))
                  (acl2-numberp x)
                  (acl2-numberp y))
             (equal (equal x y)
                    (equal (- x) (- y)))))

(defthm |(equal (/ x) (/ y))|
  (implies (and (syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp (mostly-divisive-factors-p y mfc state))
		(syntaxp
		 (simplify-ok-p `(EQUAL ,x ,y)
				'(EQUAL (UNARY-/ x) (UNARY-/ y))
				`((x . ,x) (y . ,y))
				mfc state))
		(acl2-numberp x)
                (acl2-numberp y))
           (equal (equal x y)
                  (equal (/ x) (/ y)))))

(local
 (in-theory (disable floor)))

(defthm integerp-<-constant
  (implies (and (syntaxp (rational-constant-p c))
		(real/rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< x c)
                  (<= x (floor c 1))))
  :otf-flg t)

(defthm constant-<-integerp
  (implies (and (syntaxp (rational-constant-p c))
                (real/rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< c x)
                  (<= (+ 1 (floor c 1)) x)))
  :otf-flg t)

(defthm |(< (- x) c)|
  (implies (and (syntaxp (numeric-constant-p c))
		(syntaxp (mostly-negative-addends-p x mfc state)))
             (equal (< x c)
                    (< (- c) (- x)))))

(defthm |(< c (- x))|
  (implies (and (syntaxp (numeric-constant-p c))
		(syntaxp (mostly-negative-addends-p x mfc state)))
             (equal (< c x)
                    (< (- x) (- c)))))

(defthm |(< (/ x) 0)|
  (implies (and (syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp
		 (simplify-ok-p `(< ,x '0)
				'(< (UNARY-/ x) '0)
				`((x . ,x))
				mfc state))
		(real/rationalp x))
	   (equal (< x 0)
		  (< (/ x) 0))))

(defthm |(< 0 (/ x))|
  (implies (and (syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp
		 (simplify-ok-p `(< '0 ,x)
				'(< '0 (UNARY-/ x))
				`((x . ,x))
				mfc state))
		(real/rationalp x))
	   (equal (< 0 x)
		  (< 0 (/ x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The next four rules have a rather complicated syntaxp test.
;;; We are doing two things at once.
;;; 1. We are using a simplified version of simplify-ok-p.
;;; 2. We are restricting the rules applicablity to when it is most
;;; likely to do some good.  This latter, again, falls into two
;;; subcases:
;;; 2.a. Either we are rewriting a term which appears explicitly in
;;; the current goal, or
;;; 2.b. We have an objective of T or NIL (note here that the linear
;;; arithmetic procedures ore only used when we have such an
;;; objective).
;;; That is, if we don't know what our objective is and we are not
;;; rewriting something which appears explicitly in the goal, it
;;; is likely to be more trouble than it is worth to introduce such
;;; a conjunction or disjunction.

;;; OK, the above is what I wanted to do, but the following
;;; syntaxp test is illegal:
#|
(syntaxp (or (and (rewriting-goal-literal x mfc state)  ; for efficiency
		  (let ((parity (present-in-goal `(< ,x ,c) mfc state)))
		    (cond ((eq parity 'positive)
			   t)
			  ((eq parity 'negative)
			   (not (proveably-integer 'x `((x . ,x)) mfc state)))
			  (t
			   nil))))
	     (let ((obj (mfc-obj x mfc state)))
	       (or (eq obj 'T)
		   (and (eq obj 'NIL)
			(not (proveably-integer 'x `((x . ,x)) mfc state)))))))

ACL2 Error in ( DEFTHM |(< (/ x) c) negative c| ...):  A rewrite rule
generated from |(< (/ x) c) negative c| is illegal because if either
state or mfc is a member of the vars of the term to be evaluated, we
require that both mfc and state be present and that they be the last
two args of the term, in that order.  We also require that the remaining
vars be already bound.  This does not appear to be the case in
(SYNTAXP (OR (AND (REWRITING-GOAL-LITERAL X MFC STATE)
                  (LET (#) (COND # # #)))
             (LET ((OBJ #))
                  (OR (EQ OBJ #) (AND # #))))).
The vars already bound are (C X).
||#
;;; So I split it up into two seperate rules.

(local
 (in-theory (enable prefer-*-to-/)))

(defthm |(< (/ x) c) negative c --- present in goal|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< c 0)
		(syntaxp (rewriting-goal-literal x mfc state))   ; for efficiency
		(syntaxp (let ((parity (present-in-goal `(< ,x ,c) mfc state)))
			   (cond ((eq parity 'positive)
				  t)
				 ((eq parity 'negative)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))
				 (t
				  nil))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< x c)
		  (and (< (/ x) 0)
		       (< (/ c) (/ x))))))

(defthm |(< (/ x) c) negative c --- obj t or nil|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< c 0)
		(syntaxp (let ((obj (mfc-obj x mfc state)))
			   (or (eq obj 'T)
			       (and (eq obj 'NIL)
				    (not (proveably-integer 'x `((x . ,x)) mfc state))))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< x c)
		  (and (< (/ x) 0)
		       (< (/ c) (/ x))))))

(defthm |(< (/ x) c) positive c --- present in goal|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< 0 c)
		(syntaxp (rewriting-goal-literal x mfc state)) ; for efficiency
		(syntaxp (let ((parity (present-in-goal `(< ,x ,c) mfc state)))
			   (cond ((eq parity 'positive)
				  t)
				 ((eq parity 'negative)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))
				 (t
				  nil))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< x c)
		  (or (<= (/ x) 0)
		      (< (/ c) (/ x))))))

(defthm |(< (/ x) c) positive c --- obj t or nil|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< 0 c)
		(syntaxp (or (eq (mfc-obj x mfc state) 'T)
			     (and (eq (mfc-obj x mfc state) 'NIL)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< x c)
		  (or (<= (/ x) 0)
		      (< (/ c) (/ x))))))

(defthm |(< c (/ x)) positive c --- present in goal|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< 0 c)
		(syntaxp (rewriting-goal-literal x mfc state)) ; for efficiency
		(syntaxp (let ((parity (present-in-goal `(< ,c ,x) mfc state)))
			   (cond ((eq parity 'positive)
				  t)
				 ((eq parity 'negative)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))
				 (t
				  nil))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< c x)
		  (and (< 0 (/ x))
		       (< (/ x) (/ c))))))

(defthm |(< c (/ x)) positive c --- obj t or nil|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< 0 c)
		(syntaxp (or (eq (mfc-obj x mfc state) 'T)
			     (and (eq (mfc-obj x mfc state) 'NIL)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< c x)
		  (and (< 0 (/ x))
		       (< (/ x) (/ c))))))

(defthm |(< c (/ x)) negative c --- present in goal|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< c 0)
		(syntaxp (rewriting-goal-literal x mfc state)) ; for efficiency
		(syntaxp (let ((parity (present-in-goal `(< ,c ,x) mfc state)))
			   (cond ((eq parity 'positive)
				  t)
				 ((eq parity 'negative)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))
				 (t
				  nil))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< c x)
		  (or (<= 0 (/ x))
		      (< (/ x) (/ c))))))

(defthm |(< c (/ x)) negative c --- obj t or nil|
  (implies (and (syntaxp (numeric-constant-p c))
		(real/rationalp c)
		(< c 0)
		(syntaxp (or (eq (mfc-obj x mfc state) 'T)
			     (and (eq (mfc-obj x mfc state) 'NIL)
				  (not (proveably-integer 'x `((x . ,x)) mfc state)))))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(real/rationalp x))
	   (equal (< c x)
		  (or (<= 0 (/ x))
		      (< (/ x) (/ c))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(< (- x) (- y))|
    (implies (and (syntaxp (mostly-negative-addends-p x mfc state))
                  (syntaxp (mostly-negative-addends-p y mfc state)))
             (equal (< x y)
                    (< (- y) (- x)))))

;;; We introduce the case-split only when we are rewriting a goal
;;; literal.  Not when we are back-chaining.

(defthm |(< (/ x) (/ y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (mostly-divisive-factors-p x mfc state))
		(syntaxp (mostly-divisive-factors-p y mfc state))
		(syntaxp (let ((parity (present-in-goal `(< ,x ,y) mfc state)))
			   (cond ((eq parity 'positive)
				  t)
				 ((eq parity 'negative)
				  (and (not (proveably-integer 'x `((x . ,x)) mfc state))
				       (not (proveably-integer 'y `((y . ,y)) mfc state))))
				  (t
				   nil))))
		(real/rationalp x)
		(real/rationalp y))
	   (equal (< x y)
		  (cond ((and (< 0 x)
			      (< 0 y))
			 (< (/ y) (/ x)))
			((and (< x 0)
			      (< y 0))
			 (< (/ y) (/ x)))
			(t
			 (< (/ x) (/ y))))))
  :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-1 NORMALIZE-<-/-TO-*-2
				     NORMALIZE-<-/-TO-*-3-2 NORMALIZE-<-/-TO-*-3-4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next few rules catch a few of the simplest cases otherwise
;;; missed when not using prefer-positive-exponents.  Where should we
;;; draw the line as to what to put here?

;;; What should probably be done is to generalize all of the below
;;; with a small set of bind-free rules similar to the
;;; prefer-positive-exponents rules for equal and <.  Note that we
;;; would be limiting their use to when we win at little cost by doing
;;; so (prefering positive exponents).

(defthm |(equal x (/ y))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(equal (* x y) 1))
	   (equal (equal x (/ y))
		  t))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(not (equal x (/ y)))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(not (equal y 0))
		(not (equal (* x y) 1)))
	   (equal (equal x (/ y))
		  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1 1))))

(defthm |(equal x (- (/ y)))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(equal (* x y) -1))
	   (equal (equal x (- (/ y)))
		  t))
  :hints (("Goal" :use (:instance |(equal c (/ x))|
				  (c x)
				  (x (- (/ y))))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(not (equal x (- (/ y))))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(not (equal y 0))
		(not (equal (* x y) -1)))
	   (equal (equal x (- (/ y)))
		  nil))
  :hints (("Goal" :use (:instance |(equal c (/ x))|
				  (c x)
				  (x (- (/ y))))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1 1))))

(defthm |(equal (* x (/ y)) 1)|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(equal x y))
	   (equal (equal (* x (/ y)) 1)
		  t))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(not (equal (* x (/ y)) 1))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x y)))
	   (equal (equal (* x (/ y)) 1)
		  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(equal (* (/ x) y) 1)|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(equal x y))
	   (equal (equal (* (/ x) y) 1)
		  t))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(not (equal (* (/ x) y) 1))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x y)))
	   (equal (equal (* (/ x) y) 1)
		  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(equal (* x (/ y)) -1)|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(equal x (- y)))
	   (equal (equal (* x (/ y)) -1)
		  t))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(not (equal (* x (/ y)) -1))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x (- y))))
	   (equal (equal (* x (/ y)) -1)
		  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(equal (* (/ x) y) -1)|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x 0))
		(equal x (- y)))
	   (equal (equal (* (/ x) y) -1)
		  t))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(not (equal (* (/ x) y) -1))|
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(not (equal x (- y))))
	   (equal (equal (* (/ x) y) -1)
		  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1))))

(defthm |(< x (/ y)) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(< (* x y) 1))
	   (< x (/ y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= x (/ y)) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(<= (* x y) 1))
	   (<= x (/ y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< x (/ y)) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(< 1 (* x y)))
	   (< x (/ y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= x (/ y)) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(<= 1 (* x y)))
	   (<= x (/ y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (/ x) y) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< 1 (* x y)))
	   (< (/ x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (/ x) y) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(<= 1 (* x y)))
	   (<= (/ x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (/ x) y) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< (* x y) 1))
	   (< (/ x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (/ x) y) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(<= (* x y) 1))
	   (<= (/ x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< 1 (* x (/ y))) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(< y x))
	   (< 1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= 1 (* x (/ y))) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(<= y x))
	   (<= 1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< 1 (* x (/ y))) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(< x y))
	   (< 1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= 1 (* x (/ y))) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(<= x y))
	   (<= 1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< 1 (* (/ x) y)) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< x y))
	   (< 1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= 1 (* (/ x) y)) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(<= x y))
	   (<= 1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< 1 (* (/ x) y)) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< y x))
	   (< 1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= 1 (* (/ x) y)) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(<= y x))
	   (<= 1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* x (/ y)) 1) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(< x y))
	   (< (* x (/ y)) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* x (/ y)) 1) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(<= x y))
	   (<= (* x (/ y)) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* x (/ y)) 1) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(< y x))
	   (< (* x (/ y)) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* x (/ y)) 1) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(<= y x))
	   (<= (* x (/ y)) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* (/ x) y) 1) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< y x))
	   (< (* (/ x) y) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* (/ x) y) 1) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(<= y x))
	   (<= (* (/ x) y) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* (/ x) y) 1) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< x y))
	   (< (* (/ x) y) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* (/ x) y) 1) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(<= x y))
	   (<= (* (/ x) y) 1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< -1 (* x (/ y))) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(< (- y) x))
	   (< -1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= -1 (* x (/ y))) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(<= (- y) x))
	   (<= -1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< -1 (* x (/ y))) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(< x (- y)))
	   (< -1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= -1 (* x (/ y))) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(<= x (- y)))
	   (<= -1 (* x (/ y))))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< -1 (* (/ x) y)) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< (- x) y))
	   (< -1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= -1 (* (/ x) y)) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(<= (- x) y))
	   (<= -1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< -1 (* (/ x) y)) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< y (- x)))
	   (< -1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= -1 (* (/ x) y)) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(<= y (- x)))
	   (<= -1 (* (/ x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* x (/ y)) -1) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(< x (- y)))
	   (< (* x (/ y)) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* x (/ y)) -1) with (< 0 y)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 y)
		(<= x (- y)))
	   (<= (* x (/ y)) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* x (/ y)) -1) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(< (- y) x))
	   (< (* x (/ y)) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* x (/ y)) -1) with (< y 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< y 0)
		(<= (- y) x))
	   (<= (* x (/ y)) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* (/ x) y) -1) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< y (- x)))
	   (< (* (/ x) y) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* (/ x) y) -1) with (< 0 x)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(<= y (- x)))
	   (<= (* (/ x) y) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(< (* (/ x) y) -1) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< (- x) y))
	   (< (* (/ x) y) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))

(defthm |(<= (* (/ x) y) -1) with (< x 0)|
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(<= (- x) y))
	   (<= (* (/ x) y) -1))
  :rule-classes ((:rewrite :backchain-limit-lst (2 2 1 1))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm equal-to-iff
   (equal (equal (< a b)
                 (< x y))
          (iff (< a b)
               (< x y)))))

(defthm |(equal (+ (- c) x) y)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
		(< c 0)
		(syntaxp (simplify-ok-p `(EQUAL (BINARY-+ ,c ,x) ,y)
					'(EQUAL x (BINARY-+ (UNARY-- c) y))
					`((x . ,x)
					  (y . ,y)
					  (c . ,c))
					mfc state))
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal (+ c x) y)
                  (equal x (+ (- c) y)))))

(defthm |(< (+ (- c) x) y)|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
		(< c 0)
		(syntaxp (simplify-ok-p `(< (BINARY-+ ,c ,x) ,y)
					'(< x (BINARY-+ (UNARY-- c) y))
					`((x . ,x)
					  (y . ,y)
					  (c . ,c))
					mfc state))
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (< (+ c x) y)
                  (< x (+ (- c) y)))))

(defthm |(< y (+ (- c) x))|
  (implies (and (syntaxp (quotep c))
                (acl2-numberp c)
		(< c 0)
		(syntaxp (simplify-ok-p `(< ,y (BINARY-+ ,c ,x))
					'(< (BINARY-+ (UNARY-- c) y) x)
					`((x . ,x)
					  (y . ,y)
					  (c . ,c))
					mfc state))
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (< y (+ c x))
                  (< (+ (- c) y) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The use of find-constant-addend and find-constant-factor allows us to reduce
;;; the number of very similar rules.

(defun find-constant-addend (lhs rhs)

  ;; We look for a leading additive constant on both lhs and rhs, and
  ;; pick the smaller and negate it.  You must check that c is not
  ;; 0, to prevent loops.

  (cond ((and (eq (fn-symb lhs) 'BINARY-+)
	      (eq (fn-symb rhs) 'BINARY-+)
	      (numeric-constant-p (arg1 lhs))
	      (numeric-constant-p (arg1 rhs)))
	 ;; (rel (+ c x) (+ d y))
	 (let ((c (unquote (arg1 lhs)))
	       (d (unquote (arg1 rhs))))
	   (cond ((eql c 0)
		  `((c . ,(kwote (- d)))))
		 ((eql d 0)
		  `((c . ,(kwote (- c)))))
		 ((< c d)
		  `((c . ,(kwote (- c)))))
		 (t
		  `((c . ,(kwote (- d))))))))
	((and (eq (fn-symb rhs) 'BINARY-+)
	      (numeric-constant-p lhs)
	      (numeric-constant-p (arg1 rhs)))
	 ;; (rel c (+ d y))
	 (let ((c (unquote lhs))
	       (d (unquote (arg1 rhs))))
	   (cond ((eql c 0)
		  `((c . ,(kwote (- d)))))
		 ((eql d 0)
		  `((c . ,(kwote (- c)))))
		 ((< c d)
		  `((c . ,(kwote (- c)))))
		 (t
		  `((c . ,(kwote (- d))))))))
	((and (eq (fn-symb lhs) 'BINARY-+)
	      (numeric-constant-p (arg1 lhs))
	      (numeric-constant-p rhs))
	 ;; (rel (+ c x) d)
	 (let ((c (unquote (arg1 lhs)))
	       (d (unquote rhs)))
	   (cond ((eql c 0)
		  `((c . ,(kwote (- d)))))
		 ((eql d 0)
		  `((c . ,(kwote (- c)))))
		 ((< c d)
		  `((c . ,(kwote (- c)))))
		 (t
		  `((c . ,(kwote (- d))))))))
	(t
	 nil)))

(defthm reduce-additive-constant-equal
  (implies (and (syntaxp (in-term-order-+ lhs mfc state))
		(syntaxp (in-term-order-+ rhs mfc state))
		(bind-free (find-constant-addend lhs rhs)
			   (c))
		(not (equal c 0))
		(syntaxp (simplify-ok-p `(EQUAL ,lhs ,rhs)
					'(EQUAL (BINARY-+ c lhs) (BINARY-+ c rhs))
					`((lhs . ,lhs)
					  (rhs . ,rhs)
					  (c . ,c))
					mfc state))
		(acl2-numberp lhs)
		(acl2-numberp rhs)
		(acl2-numberp c))
	   (equal (equal lhs rhs)
		  (equal (+ c lhs) (+ c rhs)))))

(defthm reduce-additive-constant-<
  (implies (and (syntaxp (in-term-order-+ lhs mfc state))
		(syntaxp (in-term-order-+ rhs mfc state))
		(bind-free (find-constant-addend lhs rhs)
			   (c))
		(not (equal c 0))
		(syntaxp (simplify-ok-p `(< ,lhs ,rhs)
					'(< (BINARY-+ c lhs) (BINARY-+ c rhs))
					`((lhs . ,lhs)
					  (rhs . ,rhs)
					  (c . ,c))
					mfc state))
		(acl2-numberp lhs)
		(acl2-numberp rhs)
		(acl2-numberp c))
	   (equal (< lhs rhs)
		  (< (+ c lhs) (+ c rhs)))))

(defun find-constant-factor-equal (lhs rhs)

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
	 `((c . ,(kwote (/ (unquote (arg1 lhs)))))))
	((and (eq (fn-symb lhs) 'BINARY-*)
	      (numeric-constant-p (arg1 lhs))
	      (not (eq (fn-symb (arg2 lhs)) 'BINARY-*))
	      (eq (fn-symb rhs) 'BINARY-+))
	 ;; (rel (* d y) x)
	 `((c . ,(kwote (/ (unquote (arg1 rhs)))))))
	((and (eq (fn-symb rhs) 'BINARY-+)
	      (eq (fn-symb lhs) 'BINARY-+))
	 ;; We could probably do something clever here, but I am not
	 ;; sure just what.
	 nil)
	(t
	 nil)))

(defun find-rational-constant-factor-< (lhs rhs)

  ;;

  (cond ((and (eq (fn-symb lhs) 'BINARY-*)
	      (eq (fn-symb rhs) 'BINARY-*)
	      (rational-constant-p (arg1 lhs))
	      (rational-constant-p (arg1 rhs)))
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
	      (rational-constant-p lhs)
	      (rational-constant-p (arg1 rhs)))
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
	      (rational-constant-p (arg1 lhs))
	      (rational-constant-p rhs))
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
	      (rational-constant-p (arg1 rhs))
	      (not (eq (fn-symb (arg2 rhs)) 'BINARY-*))
	      (eq (fn-symb lhs) 'BINARY-+))
	 ;; (rel x (* d y))
	 ;; I don't think we want to do anything here, but
	 ;; I leave this as a reminder to think about it.
	 nil)
	((and (eq (fn-symb lhs) 'BINARY-*)
	      (rational-constant-p (arg1 lhs))
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

(defun find-constant-factor-< (lhs rhs)

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

(defthm reduce-multiplicative-constant-equal
  (implies (and (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
		(bind-free (find-constant-factor-equal lhs rhs)
			   (c))
		(not (equal c 0))
		(not (equal (abs c) 1))
		(syntaxp (simplify-ok-p `(EQUAL ,lhs ,rhs)
					'(EQUAL (BINARY-* c lhs) (BINARY-* c rhs))
					`((lhs . ,lhs)
					  (rhs . ,rhs)
					  (c . ,c))
					mfc state))
		(acl2-numberp lhs)
		(acl2-numberp rhs)
		(acl2-numberp c))
	   (equal (equal lhs rhs)
		  (equal (* c lhs) (* c rhs)))))

(defthm reduce-rational-multiplicative-constant-<
  (implies (and (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
		(bind-free (find-rational-constant-factor-< lhs rhs)
			   (c))
		(not (equal c 0))
		(not (equal (abs c) 1))
		(syntaxp (simplify-ok-p `(< ,lhs ,rhs)
					'(< (BINARY-* c lhs) (BINARY-* c rhs))
					`((lhs . ,lhs)
					  (rhs . ,rhs)
					  (c . ,c))
					mfc state))
		(acl2-numberp lhs)
		(acl2-numberp rhs)
		(real/rationalp c))
	   (equal (< lhs rhs)
		  (if (< 0 c)
		      (< (* c lhs) (* c rhs))
		    (< (* c rhs) (* c lhs))))))

(defthm reduce-multiplicative-constant-<
  (implies (and (syntaxp (in-term-order-* lhs mfc state))
		(syntaxp (in-term-order-* rhs mfc state))
		(bind-free (find-constant-factor-< lhs rhs)
			   (c))
		(not (equal c 0))
		(not (equal (abs c) 1))
		(syntaxp (simplify-ok-p `(< ,lhs ,rhs)
					'(< (BINARY-* c lhs) (BINARY-* c rhs))
					`((lhs . ,lhs)
					  (rhs . ,rhs)
					  (c . ,c))
					mfc state))
		(real/rationalp lhs)
		(real/rationalp rhs)
		(acl2-numberp c))
	   (equal (< lhs rhs)
		  (if (< 0 c)
		      (< (* c lhs) (* c rhs))
		    (< (* c rhs) (* c lhs)))))
  :hints (("Goal" :use (:instance big-helper-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next two rules help with things like:
#|
(thm
 (IMPLIES (AND (INTEGERP X)
	       (INTEGERP Z)
	       (<= (+ 1/2 X) Z))
	  (<= (+ 3/4 X) Z)))
|#

(defthm |(< (+ c/d x) y)|
  (implies (and (syntaxp (rational-constant-p c))
		(syntaxp (not (integer-constant-p c)))
		(syntaxp (simplify-ok-p `(< (BINARY-+ ,c ,x) ,y)
					'(< (BINARY-* (DENOMINATOR c) (BINARY-+ c x))
					    (BINARY-* (DENOMINATOR c) y))
					`((x . ,x)
					  (y . ,y)
					  (c . ,c))
					mfc state))
		(real/rationalp c)
		(not (equal c 0))
		(acl2-numberp y))
	   (equal (< (+ c x) y)
		  (< (* (denominator c) (+ c x))
		     (* (denominator c) y))))
  :hints (("Goal" :in-theory (disable *-R-DENOMINATOR-R-PASS1))))

(defthm |(< x (+ c/d y))|
  (implies (and (syntaxp (rational-constant-p c))
		(syntaxp (not (integer-constant-p c)))
		(syntaxp (simplify-ok-p `(< ,x (BINARY-+ ,c ,y))
					'(< (BINARY-* (DENOMINATOR c) x)
					    (BINARY-* (DENOMINATOR c) (BINARY-+ c y)))
					`((x . ,x)
					  (y . ,y)
					  (c . ,c))
					mfc state))
		(real/rationalp c)
		(not (equal c 0))
		(acl2-numberp x))
	   (equal (< x (+ c y))
		  (< (* (denominator c) x)
		     (* (denominator c) (+ c y)))))
  :hints (("Goal" :in-theory (disable *-R-DENOMINATOR-R-PASS1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We introduce the case-split only when we are rewriting a goal
;;; literal.  Not when we are back-chaining.

(defthm |(equal (* x y) 0)|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (present-in-goal `(EQUAL (BINARY-* ,x ,y) '0) mfc state))
		(acl2-numberp x)
		(acl2-numberp y))
           (equal (equal (* x y) 0)
                  (or (equal x 0)
                      (equal y 0)))))

(defun product (factors)
  (declare (xargs :guard t))
  (cond ((atom factors)
	 nil)  ; For the guard
	((atom (cdr factors))
	 (car factors))
	(t
	 `(BINARY-* ,(car factors)
		    ,(product (cdr factors))))))

(defun find-rational-factor-and-remainder-1 (x rem mfc state)
  (declare (xargs :guard (true-listp rem)))
  (cond ((not (eq (fn-symb x) 'BINARY-*))
	 nil)
	((proveably-real/rational 'x `((x . ,(arg1 x))) mfc state)
	 `((y . ,(arg1 x))
	   (z . ,(product (reverse (cons (arg2 x) rem))))))
	((eq (fn-symb (arg2 x)) 'BINARY-*)
	 (find-rational-factor-and-remainder-1 (arg2 x)
					       (cons (arg1 x) rem)
					       mfc state))
	((proveably-real/rational 'x `((x . ,(arg2 x))) mfc state)
	 `((y . ,(arg2 x))
	   (z . ,(product (reverse (cons (arg1 x) rem))))))
	(t
	 nil)))

(defun find-rational-factor-and-remainder (x mfc state)
  (declare (xargs :guard t))
  (find-rational-factor-and-remainder-1 x nil mfc state))

(defthm |(< (* x y) 0)|
    (implies (and (syntaxp (eq (fn-symb x) 'BINARY-*))
		  (syntaxp (in-term-order-* x mfc state))
		  (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< ,x '0) mfc state))
		  (bind-free (find-rational-factor-and-remainder x mfc state)
			     (y z))
		  (equal x (* y z))
                  (real/rationalp y)
                  (acl2-numberp z))
             (equal (< x 0)
                    (cond ((equal y 0)
                           nil)
                          ((equal z 0)
                           nil)
                          ((< 0 y)
                           (< z 0))
                          ((< y 0)
                           (< 0 z)))))
    :hints (("Goal" :use ((:instance big-helper-1
				     (y z)
				     (z y)))
	            :in-theory (disable big-helper-1))))

(defthm |(< 0 (* x y))|
    (implies (and (syntaxp (eq (fn-symb x) 'BINARY-*))
		  (syntaxp (in-term-order-* x mfc state))
		  (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< '0 ,x) mfc state))
		  (bind-free (find-rational-factor-and-remainder x mfc state)
			     (y z))
		  (equal x (* y z))
                  (real/rationalp y)
                  (acl2-numberp z))
             (equal (< 0 x)
                    (cond ((equal y 0)
                           nil)
                          ((equal z 0)
                           nil)
                          ((< 0 y)
                           (< 0 z))
                          ((< y 0)
                           (< z 0)))))
    :hints (("Goal" :use ((:instance big-helper-1
				     (y z)
				     (z y)))
	            :in-theory (disable big-helper-1))))

(defthm |(< (* x y) 0) rationalp (* x y)|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< (BINARY-* ,x ,y) '0) mfc state))
		  (acl2-numberp x)
                  (real/rationalp (* x y)))
             (equal (< (* x y) 0)
                    (cond ((equal y 0)
                           nil)
                          ((equal x 0)
                           nil)
                          ((< 0 y)
                           (< (/ x) 0))
                          ((< y 0)
                           (< 0 (/ x))))))
    :hints (("Goal" :use (:instance big-helper-2
				    (lhs (* x y))
				    (rhs 0)
				    (c (/ x))))))

(defthm |(< 0 (* x y)) rationalp (* x y)|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< '0 (BINARY-* ,x ,y)) mfc state))
		  (acl2-numberp x)
                  (real/rationalp (* x y)))
             (equal (< 0 (* x y))
                    (cond ((equal y 0)
                           nil)
                          ((equal x 0)
                           nil)
                          ((< 0 y)
                           (< 0 (/ x)))
                          ((< y 0)
                           (< (/ x) 0)))))
    :hints (("Goal" :use (:instance big-helper-2
				    (lhs 0)
				    (rhs (* x y))
				    (c (/ x))))))

(defthm |(< (* x (/ y)) 0) rationalp (* x (/ y))|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< (BINARY-* ,x (UNARY-/ ,y)) '0) mfc state))
		  (acl2-numberp y)
                  (real/rationalp (* x (/ y))))
             (equal (< (* x (/ y)) 0)
                    (cond ((equal y 0)
                           nil)
                          ((equal x 0)
                           nil)
                          ((< 0 y)
                           (< x 0))
                          ((< y 0)
                           (< 0 x)))))
    :hints (("Goal" :use (:instance big-helper-2
				    (lhs (* x (/ y)))
				    (rhs 0)
				    (c y)))))

(defthm |(< 0 (* x (/ y))) rationalp (* x (/ y))|
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (present-in-goal `(< '0 (BINARY-* ,x (UNARY-/ ,y))) mfc state))
		  (acl2-numberp y)
                  (real/rationalp (* x (/ y))))
             (equal (< 0 (* x (/ y)))
                    (cond ((equal y 0)
                           nil)
                          ((equal x 0)
                           nil)
                          ((< 0 y)
                           (< 0 x))
                          ((< y 0)
                           (< x 0)))))
    :hints (("Goal" :use (:instance big-helper-2
				    (lhs 0)
				    (rhs (* x (/ y)))
				    (c y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Controlling equality substitution can be tricky and annoying.
;;; The next theorem should be simple!

(encapsulate
 ()

 (local
  (defthm even-is-not-odd-helper
    (implies (and (integerp x)
		  (integerp y))
	     (hide (not (equal (* 2 x)
			       (+ 1 (* 2 y))))))
    :hints (("Goal" :use ((:instance
			   (:theorem
			    (implies (and (evenp x)
					  (not (evenp y)))
				     (not (equal x y))))
			   (x (* 2 x))
			   (y (+ 1 (* 2 y))))))
	    ("Subgoal 2'" :expand ((HIDE (NOT (EQUAL (* 2 X) (+ 1 (* 2 Y))))))))))

 (defthm even-is-not-odd
   (implies (and (integerp x)
		 (integerp y))
	    (not (equal (* 2 x)
			(+ 1 (* 2 y)))))
   :hints (("Goal" :use even-is-not-odd-helper
	    :expand ((HIDE (NOT (EQUAL (* 2 X) (+ 1 (* 2 Y)))))))))

 )