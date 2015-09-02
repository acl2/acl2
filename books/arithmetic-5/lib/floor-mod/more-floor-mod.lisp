; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; more-floor-mod.lisp
;;;
;;; Here are some more theorems about floor and mod.
;;; This book needs cleaning up and organizing.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/top")

(include-book "floor-mod")

(include-book "floor-mod-basic")

;;; We want these to be the first rules seen:

(include-book "if-normalization")

(include-book "forcing-types")

(table acl2-defaults-table :state-ok t)

(SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID STABLE-UNDER-SIMPLIFICATIONP
                                  HIST NIL)))

;; Jared adding this to speed up proofs

(local (in-theory (disable not-integerp-type-set-rules
                           ;mod-x-y-=-x+y
                           ;simplify-terms-such-as-ax+bx-=-0
                           ;reduce-additive-constant-equal
                           ;floor-zero
                           ;floor-=-x/y
                           ;simplify-products-gather-exponents-<
                           integerp-mod-1
                           integerp-mod-2
                           integerp-mod-3

                           )))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of handy theorems.  How should these be generalized?
;;; Only constants?  Only powers of 2?

(defthm |(* 2 (floor x y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(real/rationalp (/ x y)))
	   (equal (* 2 (floor x y))
		  (if (integerp (* 1/2 (floor (* 2 x) y)))
		      (floor (* 2 x) y)
		    (+ -1 (floor (* 2 x) y)))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(integerp (* 1/2 (floor (* 2 x) y))))
			   (equal (* 2 (floor x y))
				  (floor (* 2 x) y))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(not (integerp (* 1/2 (floor (* 2 x) y)))))
			   (equal (* 2 (floor x y))
				  (+ -1 (floor (* 2 x) y)))))))

;;; Ugly little hack to preven looping:

;;; Original idea for this hack is due to Matt, who graciously
;;; listened to my whining and provided a solution.
;;; (See the evil stuffing of LAMBDAs inside HIDE, in rewrite in
;;; rewrite.lisp for the source of the difficulty.)

(defun ugly-unhide-hack (x)
  x)

(in-theory (disable ugly-unhide-hack))

(defun ugly-unhide-hack-fn (x)
  (case-match x
    ((('LAMBDA ('X 'Y)
	      ('BINARY-* ''1/2 ('FLOOR 'X 'Y)))
      u
      v)
     (list (cons 'y `(BINARY-* '1/2 (FLOOR ,u ,v)))))
    ;; I don't think there are any guaruntees about the order of args
    ;; in a lambda
    ((('LAMBDA ('Y 'X)
	      ('BINARY-* ''1/2 ('FLOOR 'X 'Y)))
      u
      v)
     (list (cons 'y `(BINARY-* '1/2 (FLOOR ,v ,u)))))
    (&
     nil)))

(defthm ugly-unhide-hack-thm-1
  (implies (and (bind-free (ugly-unhide-hack-fn x)
			   (y))
		(force (equal x y)))
	   (equal (ugly-unhide-hack (hide x))
		  y))
  :hints (("Goal" :in-theory (enable ugly-unhide-hack)
	          :expand ((hide x)))))

;;; I don't think I will ever need this, but I include it just in
;;; case.
(defthm ugly-unhide-hack-thm-2
  (implies (syntaxp (not (consp (car x))))
	   (equal (ugly-unhide-hack (hide x))
		  x))
  :hints (("Goal" :in-theory (enable ugly-unhide-hack)
	   :expand ((hide x)))))

(defun ugly-unhide-hack-loop-stopper-1 (bad-term clause n)
  (declare (xargs :guard (true-listp clause)))
  (cond ((or (not (integerp n)) ; for easy termination proof
	     (<= n 0))
	 (or (and (eq (fn-symb (car clause)) 'NOT)
		  (equal bad-term (arg1 (car clause))))
	     (equal bad-term (car clause))))
        (t
         (ugly-unhide-hack-loop-stopper-1 bad-term (cdr clause) (+ -1 n)))))

(defun ugly-unhide-hack-loop-stopper (x y mfc state)
  (declare (ignore state))
  (ugly-unhide-hack-loop-stopper-1 `(INTEGERP (BINARY-* '1/2 (FLOOR ,x ,y)))
				   (mfc-clause mfc)
				   (car (caaddr (cadr (cddddr (cddddr mfc)))))))

(defthm |(* 1/2 (floor x y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(syntaxp (not (ugly-unhide-hack-loop-stopper x y mfc state)))
		(real/rationalp (/ x y)))
	   (equal (* 1/2 (floor x y))
		  (if (integerp (ugly-unhide-hack (hide (* 1/2 (floor x y)))))
		      (floor (* 1/2 x) y)
		    (+ 1/2 (floor (* 1/2 x) y)))))
  :hints (("Goal" :in-theory (enable ugly-unhide-hack)
	          :expand ((HIDE (* 1/2 (FLOOR X Y))))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(integerp (ugly-unhide-hack (hide (* 1/2 (floor x y))))))
			   (equal (* 1/2 (floor x y))
				  (floor (* 1/2 x) y))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(real/rationalp (/ x y))
				(not (integerp (ugly-unhide-hack (hide (* 1/2 (floor x y)))))))
			   (equal (* 1/2 (floor x y))
				  (+ 1/2 (floor (* 1/2 x) y)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm extra-intp-thm-1
   (IMPLIES (AND (INTEGERP (* (/ I) (/ J) X))
              (REAL/RATIONALP X)
              (INTEGERP I)
              (INTEGERP J)
              (NOT (EQUAL J 0)))
         (INTEGERP (* (/ I) X)))
   :hints (("Goal" :use (:instance
			 (:theorem
			  (implies (and (integerp x)
					(integerp y))
				   (integerp (* x y))))
			 (x (* (/ I) (/ J) X))
			 (y j))))))

(local
 (defthm extra-intp-thm-3
   (IMPLIES (AND (INTEGERP (* (/ I) (/ J) X))
		 (REAL/RATIONALP X)
		 (INTEGERP I)
		 (INTEGERP J))
	    (INTEGERP (* (/ J) (FLOOR X I))))
   :hints (("Goal" :cases ((equal j 0))))))

(defthm |(floor (+ x r) i)|  ;;; OK
  (implies (and (integerp x)
                ;(<= 0 x)
                (real/rationalp r)
                (<= 0 r)
                (< r 1)
                (integerp i)
                (< 0 i)
		)
           (equal (floor (+ x r) i)
                  (floor x i))))

;;; Move with floor-floor-integer?
#|
(defthm mod-x-i*j   ;;; OK
    (implies
     (and (> i 0)
	  (> j 0)
	  (force (integerp i))
	  (force (integerp j))
	  (force (real/rationalp x)))
     (equal (mod x (* i j))
	    (+ (mod x i) (* i (mod (floor x i) j))))))
|#
;;; A safer version.  Introducing (mod (floor x i) j) can cause
;;; subtle loops.

(defthm mod-x-i*j
  (implies (and (< 0 j)
		(integerp i)
		(integerp j)
		(real/rationalp x)
		(INTEGERP (* (/ J) (FLOOR X I))))
	   (equal (mod x (* i j))
		  (mod x i))))

(defthm mod-x-i*j-v2
  (IMPLIES (AND (INTEGERP I)
		(INTEGERP J)
		(REAL/RATIONALP X)
		(< J 0)
		(NOT (INTEGERP (* (/ I) (/ J) X)))
		(INTEGERP (* (/ J) (FLOOR X I))))
	   (EQUAL (MOD X (* I J))
		  (+ (* i j) (mod x i)))))

;;; Is this a good rule?
;;; It breaks the proof of mod-prod.

(defthmd mod-x-i*j-x-2 ;;; OK
  (implies (and (force (integerp i))
		(force (integerp j))
		(force (real/rationalp x)))
   (equal (mod x (* i j))
	  (cond ((and (< j 0)
		      (not (integerp (* (/ i) (/ j) x)))
		      (integerp (* (/ j) (floor x i))))
		 (+ (* i j) (mod x i)))
		(t
		 (+ (mod x i) (* i (mod (floor x i) j))))))))

;;; Subsumed by the above?

(defthm mod-x+i*k-i*j
  (implies
   (and (force (real/rationalp x))
	(force (integerp i))
	(force (integerp j))
	(force (integerp k))
	(< 0 i)
	(< 0 j)
	(<= 0 x)
	(< x i))
  (equal (mod (+ x (* i k)) (* i j))
	 (+ x (* i (mod k j))))))

;;; Subsumed by floor-floor-integer?

(defthm floor-x+i*k-i*j
  (implies
   (and (force (real/rationalp x))
	(force (integerp i))
	(force (integerp j))
	(force (integerp k))
	(< 0 i)
	(< 0 j)
	(<= 0 x)
	(< x i))
   (equal (floor (+ x (* i k)) (* i j))
	  (floor k j))))

(defthm floor-equal-i-over-j-rewrite   ;;; OK
  (implies (and (case-split (not (equal j 0)))
                (case-split (real/rationalp i))
                (case-split (real/rationalp j))
                )
           (equal (equal (* j (floor i j)) i)
                  (integerp (* i (/ j))))))

(defthm mod-plus-mod-n   ;;; OK
  (implies (and (integerp a)
                (integerp b)
		(integerp n))
           (iff (= (mod (+ a b) n) (mod a n))
                (= (mod b n) 0)))
  :rule-classes ())

(defthmd mod-mult-n   ;;; OK
  (equal (mod (* a n) n)
         (* n (mod a 1))))



(defthm mod-theorem-one-a   ;;; OK
  (implies (and (real/rationalp a)
		(integerp b)
		(real/rationalp n)
		(not (equal n 0)))
	   (equal (mod (* (mod a n) b) n)
		  (mod (* a b) n))))

(defthm mod-theorem-one-b   ;;; OK
  (implies (and (real/rationalp a)
		(integerp b)
		(real/rationalp n)
		(not (equal n 0)))
	   (equal (mod (* b (mod a n)) n)
		  (mod (* a b) n))))

(encapsulate ()

(local
  (defun ind-fn (i)
    (if (zp i)
	t
      (ind-fn (+ -1 i)))))

(local (in-theory (enable integerp-mod-1
                           integerp-mod-2
                           integerp-mod-3)))

 ;; Robert Krug writes:  This hint took some knowledge about the
 ;; library, but it is described in the README.  If you can suggest a
 ;; way to make this more easily accessable, I would be interested in
 ;; hearing it.

(local
  (scatter-exponents))

 ;; Robert Krug writes:  I believe I could prove this or an
 ;; equivalent one using instances of mod-theorem-one-a or
 ;; mod-theorem-one-b, but this is what I tried first.

 ;; RBK: Fix this proof.  72 generalizations and 96 destructor
 ;; eliminations!


(local
 (encapsulate
  ()
  (local (in-theory (disable (:REWRITE MOD-X-Y-=-X-Y . 1)
                             (:REWRITE MOD-X-Y-=-X+Y . 1)
                             EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                             EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                             EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                             EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                             EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                             EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE
                             EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                             EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                             (:TYPE-PRESCRIPTION MOD-ZERO . 4)
                             (:REWRITE MOD-X-Y-=-X . 3)
                             (:REWRITE MOD-X-Y-=-X . 4)
                             (:META META-INTEGERP-CORRECT)
                             (:REWRITE
                                    SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<)
                             (:REWRITE MOD-ZERO . 4)
                             (:TYPE-PRESCRIPTION INTEGERP-MOD-2)
                             (:REWRITE DEFAULT-TIMES-2)
                             (:REWRITE DEFAULT-TIMES-1)
                             (:TYPE-PRESCRIPTION MOD-ZERO . 3)
                             (:TYPE-PRESCRIPTION MOD-ZERO . 2)
                             (:TYPE-PRESCRIPTION MOD-ZERO . 1)
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2)
                             (:TYPE-PRESCRIPTION MOD-POSITIVE . 1)
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2)
                             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)
                             (:REWRITE MOD-X-Y-=-X+Y . 3)
                             (:REWRITE MOD-X-Y-=-X-Y . 3)
                             (:REWRITE |(integerp (expt x n))|)
                             (:REWRITE MOD-X-Y-=-X-Y . 2)
                             (:REWRITE DEFAULT-MOD-RATIO)
                             (:REWRITE
                                   SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL)
                             (:REWRITE MOD-X-Y-=-X+Y . 2)
                             (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS)
                             (:REWRITE DEFAULT-PLUS-2)
                             (:REWRITE
                                PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL)
                             (:REWRITE
                                PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<)
                             (:REWRITE DEFAULT-LESS-THAN-2)
                             (:REWRITE DEFAULT-LESS-THAN-1)
                             (:REWRITE DEFAULT-PLUS-1)
                             (:REWRITE INTEGERP-/)
                             (:REWRITE |(< c (- x))|)
                             (:REWRITE BUBBLE-DOWN-*-MATCH-1)
                             (:REWRITE |(< (- x) c)|)
                             (:REWRITE |(* (expt x m) (expt x n))|)
                             (:REWRITE INTEGERP-MINUS-X)
                             (:REWRITE |(< (- x) (- y))|)
                             (:REWRITE |(< 0 (/ x))|)
                             (:REWRITE
                                   REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<)
                             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<)
                             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<)
                             (:REWRITE
                                |(< c (/ x)) positive c --- present in goal|)
                             (:REWRITE
                                   |(< c (/ x)) positive c --- obj t or nil|)
                             (:REWRITE
                                |(< c (/ x)) negative c --- present in goal|)
                             (:REWRITE
                                   |(< c (/ x)) negative c --- obj t or nil|)
                             (:REWRITE
                                |(< (/ x) c) positive c --- present in goal|)
                             (:REWRITE
                                   |(< (/ x) c) positive c --- obj t or nil|)
                             (:REWRITE
                                |(< (/ x) c) negative c --- present in goal|)
                             (:REWRITE
                                   |(< (/ x) c) negative c --- obj t or nil|)
                             (:REWRITE |(< (/ x) (/ y))|)
                             (:REWRITE REMOVE-STRICT-INEQUALITIES)
                             (:REWRITE INTEGERP-<-CONSTANT)
                             (:REWRITE CONSTANT-<-INTEGERP)
                             (:REWRITE MOD-X-Y-=-X . 2)
                             (:REWRITE |(mod (+ x (mod a b)) y)|)
                             (:REWRITE |(mod (+ x (- (mod a b))) y)|)
                             (:REWRITE DEFAULT-DIVIDE)
                             (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX)
                             (:REWRITE DEFAULT-MINUS)
                             (:REWRITE |(equal (- x) c)|)
                             (:LINEAR
                                    EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1)
                             (:LINEAR
                                  EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1)
                             (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1)
                             (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1)
                             (:LINEAR EXPT->=-1-ONE)
                             (:REWRITE DEFAULT-MOD-1)
                             (:TYPE-PRESCRIPTION
                                    RATIONALP-EXPT-TYPE-PRESCRIPTION)
                             (:REWRITE |(equal (- x) (- y))|)
                             (:REWRITE |(* c (* d x))|)
                             (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL)
                             (:REWRITE MOD-CANCEL-*-CONST)
                             (:REWRITE |(equal (/ x) c)|)
                             (:REWRITE
                                |(mod x (* y (/ z))) rewriting-goal-literal|)
                             (:REWRITE
                                |(mod (* x (/ y)) z) rewriting-goal-literal|)
                             (:REWRITE |(< 0 (* x y))|)
                             (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN)
                             (:LINEAR EXPT-X->=-X)
                             (:LINEAR EXPT-X->-X)
                             (:LINEAR EXPT->=-1-TWO)
                             (:LINEAR EXPT->-1-TWO)
                             (:LINEAR EXPT->-1-ONE)
                             (:LINEAR EXPT-<=-1-TWO)
                             (:LINEAR EXPT-<=-1-ONE)
                             (:LINEAR EXPT-<-1-TWO)
                             (:LINEAR EXPT-<-1-ONE)
                             (:REWRITE
                                    REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL)
                             (:REWRITE |(equal c (/ x))|)
                             (:REWRITE |(equal (/ x) (/ y))|)
                             (:REWRITE |(equal c (- x))|)
                             (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER)
                             (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)
                             (:REWRITE |(< (/ x) 0)|)
                             (:REWRITE |(< (* x y) 0)|)
                             (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER)
                             (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)
                             (:REWRITE EQUAL-OF-PREDICATES-REWRITE)
                             (:TYPE-PRESCRIPTION BUBBLE-DOWN)
                             (:REWRITE |(* x (if a b c))|)
                             (:LINEAR EXPT-LINEAR-UPPER-<=)
                             (:LINEAR EXPT-LINEAR-UPPER-<)
                             (:LINEAR EXPT-LINEAR-LOWER-<=)
                             (:LINEAR EXPT-LINEAR-LOWER-<)
                             (:REWRITE |arith (* c (* d x))|)
                             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)
                             (:REWRITE |(equal (mod (+ x y) z) x)|))))

  (defthm mod-theorem-two-helper-helper
    ;; 37.4 seconds
    (IMPLIES (AND (NOT (ZP I))
		  (EQUAL (MOD (EXPT A I) N)
			 (MOD (EXPT (MOD A N) I) N))
		  (INTEGERP A)
		  (integerp b)
		  (INTEGERP N)
		  (NOT (EQUAL N 0)))
	     (EQUAL (MOD (* b (EXPT (MOD A N) I)) N)
		    (MOD (* b (EXPT A I)) N)))
    :hints (("Goal" :induct (ind-fn b))))))

 ;; Robert Krug writes:  This helper, and ones like it, irritate me.
 ;; ACL2 failed to prove theorem two, with the subgoal:

 ;; (IMPLIES (AND (NOT (ZP I))
 ;;               (EQUAL (MOD (EXPT A (+ -1 I)) N)
 ;;                      (MOD (EXPT (MOD A N) (+ -1 I)) N))
 ;;               (INTEGERP A)
 ;;               (INTEGERP N)
 ;;               (NOT (EQUAL N 0)))
 ;;          (EQUAL (MOD (EXPT (MOD A N) I) N)
 ;;                 (MOD (EXPT A I) N)))

 ;; but (EXPT A (+ -1 I)) expand to (* (/ A) (EXPT A I)) and
 ;; thus introduces division which is always harder to reason
 ;; about than multiplication.  It would be nice if ACL2 could
 ;; induct with a base case of I and an inductive case of (+ 1 I),
 ;; rather than using a base case of (+ -1 I) and an indictive
 ;; case of I.  But this is not going to happen.

(local
  (defthm mod-theorem-two-helper
    (IMPLIES (AND (NOT (ZP I))
		  (EQUAL (MOD (EXPT A I) N)
			 (MOD (EXPT (MOD A N) I) N))
		  (INTEGERP A)
		  (INTEGERP N)
		  (NOT (EQUAL N 0)))
	     (EQUAL (MOD (EXPT (MOD A N) (+ 1 I)) N)
		    (MOD (EXPT A (+ 1 I)) N)))))

(local
  (gather-exponents))

(defthm mod-theorem-two
   (implies (and (integerp a)
		 (integerp i)
		 (<= 0 i)
		 (integerp n)
		 (not (equal n 0)))
	    (equal (mod (expt (mod a n) i) n)
		   (mod (expt a i) n)))
   :hints (("Goal" :induct (ind-fn i)
	    :do-not '(generalize))
	   ("Subgoal *1/2''" :cases ((equal i 1)))
	   ("Subgoal *1/2.2" :use (:instance mod-theorem-two-helper
					     (i (+ -1 i)))
	    :in-theory (disable mod-theorem-two-helper))))

 )

;;; two-xxx can certainly be improved.

(defthm two-xxx   ;;; OK
  (IMPLIES (AND (integerp x)
		(< 0 x)
		(INTEGERP N)
		(<= 0 N)
		(NOT (INTEGERP (* 1/2 X))))
	   (EQUAL (+ 1
		     (* 2 (MOD (FLOOR X 2) (EXPT 2 n))))
		  (MOD X (EXPT 2 (+ 1 N)))))
  :hints (("Goal" :do-not '(generalize)
	   :do-not-induct t))
  :otf-flg t)



(defthm mod-theorem-three
  (implies (and (integerp a)
		(integerp i)
		(<= 0 i)
		(integerp n)
		(not (equal n 0))
		(integerp x))
	   (equal (mod (* x (expt (mod a n) i)) n)
		  (mod (* x (expt a i)) n)))
  :hints (("Goal" :use ((:instance mod-theorem-one-a
				  (a (expt (mod a n) i))
				  (b x))
			(:instance mod-theorem-one-a
				  (a (expt a i))
				  (b x)))
	          :in-theory (disable mod-theorem-one-a
                                      mod-theorem-one-b))))



(defthm mod-mult-2
  (implies (integerp a)
           (equal (mod (* a n) n)
                  0))
  :hints (("Goal" :cases ((equal n 0)))))

(defthm mod-prod
  (implies (and (real/rationalp m)
                (real/rationalp n)
                (real/rationalp k)
                )
           (equal (mod (* k m) (* k n))
                  (* k (mod m n))))
  :otf-flg t)

(defthm mod-mult
    (implies (and (integerp a)
                  (real/rationalp m)
		  (real/rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))


;;; floor rule like below also?

(defthm mod-sums-cancel-1
  (implies (and (case-split (<= 0 y))
                (case-split (real/rationalp k))
                (case-split (real/rationalp y))
                (case-split (real/rationalp x1))
                (case-split (real/rationalp x2))
                )
           (equal (equal (mod (+ k x1) y) (mod (+ k x2) y))
                  (equal (mod x1 y) (mod x2 y)))))

(defthm  |(equal (mod a n) (mod b n))|
  (implies (and (integerp (+ (* a (/ n)) (- (* b (/ n)))))
		(real/rationalp a)
		(real/rationalp b)
		(real/rationalp n)
		(not (equal n 0)))
	   (equal (equal (mod a n) (mod b n))
		  t))
  :hints (("Goal" :use (:instance mod-zero
				  (x (+ a (- b)))
				  (y n))
	          :in-theory (e/d ()
				  (mod-zero)))))

;;; What does this comment refer to?
;;; Will this base case for the above be caught, or should we have a
;;; second rule?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The next two theorems correspond to the following thms:
#|
(thm
 (implies (and (integerp x)
	       (integerp y)
	       (rationalp a)
	       (rationalp b))
	  (equal (< (+ x (floor a b))
		    y)
		 (< (+ x (* a (/ b)))
		    y))))

(thm
 (implies (and (integerp x)
	       (integerp y)
	       (rationalp a)
	       (rationalp b)
	       (not (equal (+ x (floor a b)) y)))
	  (equal (< y
		    (+ x (floor a b)))
		 (< y
		    (+ x (* a (/ b)))))))
|#
;;; Is there a similar rule for
;;; (< y
;;;    (+ x (- (floor a b))))

(defun find-nasty-floor-addend-1 (x ans)
  (declare (xargs :mode :program))
  (cond ((variablep x)
	 ans)
	((fquotep x)
	 ans)
	((eq (ffn-symb x) 'FLOOR)
	 (if (term-order ans x)
	     x
	   ans))
	((eq (ffn-symb x) 'BINARY-+)
	 (find-nasty-floor-addend-1 (arg2 x)
				    (find-nasty-floor-addend-1 (arg1 x)
							       ans)))
	(t
	 ans)))

(defun find-nasty-floor-addend (x)
  (declare (xargs :mode :program))
  (let ((ans (find-nasty-floor-addend-1 x nil)))
    (if ans
	(list (cons 'a (arg1 ans))
	      (cons 'b (arg2 ans))
	      (cons 'c `(UNARY-- ,ans)))
      nil)))

(defthm the-floor-above
  (implies (and (syntaxp (in-term-order-+ x mfc state))
		(bind-free (find-nasty-floor-addend x)
			   (a b c))
		(integerp x)
		(integerp y)
		(real/rationalp (* a (/ b)))
		(equal c (- (floor a b))))
	   (equal (< x y)
		  (< (+ (* a (/ b)) c x)
		     y))))

(defthm the-floor-below
  (implies (and (syntaxp (in-term-order-+ y mfc state))
		(bind-free (find-nasty-floor-addend y)
			   (a b c))
		(integerp x)
		(integerp y)
		(real/rationalp (* a (/ b)))
		(equal c (- (floor a b)))
		(not (equal x y)))
	   (equal (< x y)
		  (< x
		     (+ (* a (/ b)) c y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; RBK:!!! Separate rules into units --- i.e. no multiple corr.s

;; (equal (equal (floor a (expt 2 i)) (floor b (expt 2 j))
;;        (equal (floor a (expt (...)) b)))

#|
(defthm thm-1
    (implies (and (integerp a)
                  (integerp b)
                  (integerp n))
             (equal (MOD (+ (* B (FIBONACCI (+ -2 N)))
                            (* (FIBONACCI (+ -2 N))
                               (MOD (+ A B) 4294967296))
                            (* (FIBONACCI (+ -3 N))
                               (MOD (+ A B) 4294967296)))
                         4294967296)
                    (MOD (+ (* A (FIBONACCI (+ -2 N)))
                            (* A (FIBONACCI (+ -3 N)))
                            (* B (FIBONACCI (+ -3 N)))
                            (* 2 B (FIBONACCI (+ -2 N))))
                         4294967296)))
  :hints (("Goal" :in-theory (enable mod))))
|#


#|
; Something like the following rules are missing from my library.
; The versions below do not seem particularly good, but I have
; not given it much thought yet.

;;; Make a mod-floor rule like floor-mod

;Basic idea: mod chops off some high bits from x and fl chops off some
;low bits.  We can do the chops in either order.


(defthm crock-628
  (equal (floor 0 x)
	 0))


(defthm mod-pull-inside-fl-shift
   (implies (and ;no hyp about x
	     (real/rationalp x)
             (integerp i)
             (integerp j)
             )
            (equal (mod (floor x (expt 2 j))
                        (expt 2 i))
                   (floor (mod x (expt 2 (+ i j)))
                          (expt 2 j))))
   :hints (("Goal" :cases ((<= 0 i))))
   :otf-flg t)


|#

#|
Subgoal 8.9'
(IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (< 0 X)
              (< Y 1)
              (< X 1/2)
              (<= 1/2 Y)
              (<= (FLOOR 1 X) (/ Y)))
         (< (* 1/2 (/ X)) (FLOOR 1 Y)))

Subgoal 8.3'5'
(IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (< 0 X)
              (< Y 1)
              (< X 1/2)
              (< 1/2 Y))
         (< (/ Y) (FLOOR 1 X)))
|#
