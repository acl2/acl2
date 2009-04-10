;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; logand.lisp
;;;
;;; A crude start on a book about logand and friends.
;;; One should look through the RTL and IHS books to get an
;;; idea of what others have found useful.
;;;
;;; What other logxxx ops should be here?
;;; logandc1, logandc2, logbitp, logcount, logeqv, logior, lognand,
;;; lognor, lognot, logorc1, logorc2, logtest, logxor are defined
;;; in ACL2.
;;;
;;; For the moment, we only treat lognot, logand, and logior.  I
;;; should look again, but I believe that lognot and logand (or,
;;; rather binary-logand) are the ``primitive'' definitions, and that
;;; the others are defined in terms of those two. 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/building-blocks")

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
 (include-book "logand-helper"))

(local
 (SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID
                                  STABLE-UNDER-SIMPLIFICATIONP HIST NIL))))

(local
 (in-theory (e/d (ash-to-floor) (ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logand associativity and commutativity:

(defthm |(logand y x)|
  (equal (logand y x)
	 (logand x y)))

(defthm |(logand (logand x y) z)|
  (equal (logand (logand x y) z)
	 (logand x y z)))

(defthm |(logand y x z)|
  (equal (logand y x z)
	 (logand x y z))
  :hints (("Goal" :use (:instance logand-y-x-z))))

(defthm |(logand c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logand c d x)
		  (logand (logand c d) x))))

;;; ``Base'' theorems:

(defthm logand-0-x
  (equal (logand 0 x)
	 0))

(defthm |(logand 1 x)|
  (implies (integerp x)
	   (equal (logand 1 x)
		  (if (evenp x)
		      0
		    1)))
  :hints (("Goal" :expand ((logand 1 x)
			   (LOGAND 0 (FLOOR X 2))))))

(defthm logand--1-x
  (implies (integerp x)
	   (equal (logand -1 x)
		  x)))

(defthm logand-x-x
  (implies (integerp x)
	   (equal (logand x x)
		  x)))

;;; Misc:

(defthm logand-bounds-pos
  (implies (and (integerp x) 
		(integerp y)
		(< 0 x))
	   (<= (logand x y) x))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-bounds-neg
  (implies (and (integerp x)
		(integerp y)
		(< x 0)
		(< y 0))
	   (<= (logand x y) x))
  :hints (("Goal" :in-theory (enable logand))))

(defthm |(equal (logand x y) -1)|
  (equal (equal (logand x y) -1)
	 (and (equal x -1)
	      (equal y -1))))

;;; Do |(< 0 (logand x y))| and |(< (logand x y) (expt 2 n))|

(defthm |(< (logand x y) 0)|
  (equal (< (logand x y) 0)
	 (and (integerp x)
	      (< x 0)
	      (integerp y)
	      (< y 0)))
  :rule-classes ((:rewrite)

;;; Make these linear also?

		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (< x 0)
				 (integerp y)
				 (< y 0))
			    (and (integerp (logand x y))
				 (< (logand x y) 0))))
		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (integerp y)
				 (<= 0 y))
			    (and (integerp (logand x y))
				 (<= 0 (logand x y)))))
		 (:type-prescription
		  :corollary
		   (implies (and (integerp x)
				 (<= 0 x)
				 (integerp y))
			    (and (integerp (logand x y))
				 (<= 0 (logand x y)))))))

#|
(THM (IMPLIES (IF (< I (EXPT '2 N))
                  (< J (EXPT '2 N))
                  'NIL)
              (< (BINARY-LOGIOR I J) (EXPT '2 N))))

and variants
|#

;;; This next bunch should be generalized to any power of 2
;;; I should also consider (+ -1 (* 2 x)) and other variants.

(defthm |(logand (* 2 x) (* 2 y))|
  (implies (and (rationalp x)
		(rationalp y)
		(integerp (* 2 x))
		(integerp (* 2 y)))
	   (equal (logand (* 2 x) (* 2 y))
		  (cond ((and (integerp x)
			      (integerp y))
			 (* 2 (logand x y)))
			((and (integerp x)
			      (not (integerp y)))
			 (* 2 (logand x (+ -1/2 y))))
			((and (not (integerp x))
			      (integerp y))
			 (* 2 (logand (+ -1/2 x) y)))
			(t
			 (+ 1 (* 2 (logand (+ -1/2 x) (+ -1/2 y))))))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(rationalp x)
				(rationalp y)
				(integerp (* 2 x))
				(integerp (* 2 y)))
			   (equal (logand (* 2 x) (* 2 y))
				  (cond ((and (integerp x)
					      (integerp y))
					 (* 2 (logand x y)))
					((and (integerp x)
					      (not (integerp y)))
					 (* 2 (logand x (+ -1/2 y))))
					((and (not (integerp x))
					      (integerp y))
					 (* 2 (logand (+ -1/2 x) y)))
					(t
					 (+ 1 (* 2 (logand (+ -1/2 x) (+ -1/2 y)))))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(integerp x)
				(integerp y))
			   (equal (logand (* 2 x) (* 2 y))
				  (* 2 (logand x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(rationalp x)
				(not (integerp x))
				(integerp y))
			   (equal (logand (* 2 x) (* 2 y))
				  (* 2 (logand (+ -1/2 x) y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(integerp x)
				(rationalp y)
				(not (integerp y)))
			   (equal (logand (* 2 x) (* 2 y))
				  (* 2 (logand x (+ -1/2 y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(rationalp x)
				(not (integerp x))
				(rationalp y)
				(not (integerp y)))
			   (equal (logand (* 2 x) (* 2 y))
				  (+ 1 (* 2 (logand (+ -1/2 x) (+ -1/2 y)))))))))

;;; Which is the correct direction for the next rule?
;;; SHould I have two normal forms like gather and scatter exponents?
;;; Also, consider affects of |(floor x 2)| and the proliferation
;;; of corollaries.

(defthm |(logand (floor x 2) (floor y 2))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (logand (floor x 2) (floor y 2))
		  (floor (logand x y) 2)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y))
			   (equal (logand (floor x 2) (floor y 2))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 y)))
			   (equal (logand (floor x 2) (* 1/2 y))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 y))))
			   (equal (logand (floor x 2) (+ -1/2 (* 1/2 y)))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x)))
			   (equal (logand (* 1/2 x) (floor y 2))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (equal (logand (* 1/2 x) (* 1/2 y))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(not (integerp (* 1/2 y))))
			   (equal (logand (* 1/2 x) (+ -1/2 (* 1/2 y)))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x))))
			   (equal (logand (+ -1/2 (* 1/2 x)) (floor y 2))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(integerp (* 1/2 y)))
			   (equal (logand (+ -1/2 (* 1/2 x)) (* 1/2 y))
				  (floor (logand x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (equal (logand (+ -1/2 (* 1/2 x)) (+ -1/2 (* 1/2 y)))
				  (floor (logand x y) 2))))))
		
(local
 (defun ind-fn (n)
   (cond ((not (integerp n))
	  0)
	 ((equal n 0)
	  1)
	 ((< n 0)
	  (ind-fn (+ 1 n)))
	 (t
	  (ind-fn (+ -1 n))))))

(defthm logand-floor-expt-2-n
   (implies (and (integerp x)
		 (integerp y)
		 (integerp n))
	    (equal (logand (floor x (expt 2 n))
			   (floor y (expt 2 n)))
		   (floor (logand x y) (expt 2 n))))
   :hints (("Goal"			;:in-theory (enable logand)
	    :induct (ind-fn n)
	    :do-not '(generalize eliminate-destructors))
	   ("Subgoal *1/3" :use ((:instance |(logand (floor x 2) (floor y 2))|
					    (x (FLOOR X (EXPT 2 (+ -1 N))))
					    (y (FLOOR Y (EXPT 2 (+ -1 N))))))
	                   :in-theory (disable |(logand (floor x 2) (floor y 2))|
					       logand))
	   ))

(defthm |(mod (logand x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logand x y) 2)
		  (if (and (not (integerp (* 1/2 x)))
			   (not (integerp (* 1/2 y))))
		      1
		    0)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x)
				(integerp y))
			   (equal (mod (logand x y) 2)
				  (if (and (not (integerp (* 1/2 x)))
					   (not (integerp (* 1/2 y))))
				      1
				    0))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (equal (mod (logand x y) 2)
				  1)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x)))
			   (equal (mod (logand x y) 2)
				  0)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 y)))
			   (equal (mod (logand x y) 2)
				  0)))))

;;; Clean this up --- this is a crude patch job on an
;;; earlier proof

(encapsulate
 ()

 (local
  (defun floor-2-n-ind (x y n)
    (cond ((zip n)
	   (+ x y))
	  ((< 0 n)
	   (floor-2-n-ind (floor x 2) (floor y 2) (+ -1 n)))
	  (t
	   (floor-2-n-ind (floor x 2) (floor y 2) (+ 1 n))))))

 (local
  (defthm break-logand-apart
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logand x y)
		    (+ (* 2 (logand (floor x 2) (floor y 2)))
		       (logand (mod x 2) (mod y 2)))))
    :hints (("Subgoal 4'" :in-theory (disable logand)))
    :rule-classes nil))

 ;; Very irritating --- these lemmatta prove easily as lemmas, but
 ;; the goals do not behave under the induction.

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.6'|
    (IMPLIES (AND (INTEGERP (* 1/2 X))
		  (NOT (INTEGERP (* 1/2 Y)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.8'|
    (IMPLIES (AND (INTEGERP (* 1/2 X))
		  (NOT (INTEGERP (* 1/2 Y)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.9'|
    (IMPLIES (AND (INTEGERP (* 1/2 X))
		  (NOT (INTEGERP (* 1/2 Y)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2
				    (LOGAND (MOD X (EXPT 2 N))
					    (MOD Y (EXPT 2 N))))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.22'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (INTEGERP (* 1/2 X))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.26'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (INTEGERP (* 1/2 X))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.27'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (INTEGERP (* 1/2 X))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2
				    (LOGAND (MOD X (EXPT 2 N))
					    (MOD Y (EXPT 2 N))))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.40'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (NOT (INTEGERP (* 1/2 X)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.42'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (NOT (INTEGERP (* 1/2 X)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.48'|
    (IMPLIES (AND (INTEGERP (* 1/2 Y))
		  (NOT (INTEGERP (* 1/2 X)))
		  (INTEGERP (* 1/2 (LOGAND X Y)))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (NOT (INTEGERP (* 1/2
				    (LOGAND (MOD X (EXPT 2 N))
					    (MOD Y (EXPT 2 N))))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 0)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    0))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.49''|
    (IMPLIES (AND (NOT (INTEGERP (* 1/2 Y)))
		  (NOT (INTEGERP (* 1/2 X)))
		  (NOT (INTEGERP (* 1/2 (LOGAND X Y))))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD Y (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 1)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    1))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.65''|
    (IMPLIES (AND (NOT (INTEGERP (* 1/2 Y)))
		  (NOT (INTEGERP (* 1/2 X)))
		  (NOT (INTEGERP (* 1/2 (LOGAND X Y))))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (INTEGERP (* 1/2 (MOD X (EXPT 2 N))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 1)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    1))
    :RULE-CLASSES NIL))

 (local
  (DEFTHM |MOD-LOGAND Subgoal *1/2.81''|
    (IMPLIES (AND (NOT (INTEGERP (* 1/2 Y)))
		  (NOT (INTEGERP (* 1/2 X)))
		  (NOT (INTEGERP (* 1/2 (LOGAND X Y))))
		  (INTEGERP (* 1/2 (MOD Y (EXPT 2 N))))
		  (NOT (INTEGERP (* 1/2 (MOD X (EXPT 2 N)))))
		  (INTEGERP (* 1/2
			       (LOGAND (MOD X (EXPT 2 N))
				       (MOD Y (EXPT 2 N)))))
		  (< 0 N)
		  (EQUAL (MOD (LOGAND X Y) (EXPT 2 N)) 1)
		  (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP N))
	     (EQUAL (LOGAND (MOD X (EXPT 2 N))
			    (MOD Y (EXPT 2 N)))
		    1))
    :RULE-CLASSES NIL))

 (defthm mod-logand
   (implies (and (integerp x)
		 (integerp y)
		 (integerp n))
	    (equal (logand (mod x (expt 2 n))
			   (mod y (expt 2 n)))
		   (mod (logand x y) (expt 2 n))))
   :hints (("Goal" :induct (floor-2-n-ind x y n)
	    :in-theory (disable logand
				)
	    :do-not '(generalize eliminate-destructors))
	   ("Subgoal *1/2" :use ((:instance break-logand-apart)
				 (:instance break-logand-apart
					    (x (MOD X (EXPT 2 N)))
					    (y (MOD Y (EXPT 2 N))))))
	   ("Subgoal *1/2.81''" :by |MOD-LOGAND Subgoal *1/2.81''|)
	   ("Subgoal *1/2.65''" :by |MOD-LOGAND Subgoal *1/2.65''|)
	   ("Subgoal *1/2.49''" :by |MOD-LOGAND Subgoal *1/2.49''|)
	   ("Subgoal *1/2.48'" :by |MOD-LOGAND Subgoal *1/2.48'|)
	   ("Subgoal *1/2.42'" :by |MOD-LOGAND Subgoal *1/2.42'|)
	   ("Subgoal *1/2.41''" :by |MOD-LOGAND Subgoal *1/2.41''|)
	   ("Subgoal *1/2.40'" :by |MOD-LOGAND Subgoal *1/2.40'|)
	   ("Subgoal *1/2.27'" :by |MOD-LOGAND Subgoal *1/2.27'|)
	   ("Subgoal *1/2.26'" :by |MOD-LOGAND Subgoal *1/2.26'|)
	   ("Subgoal *1/2.22'" :by |MOD-LOGAND Subgoal *1/2.22'|)
	   ("Subgoal *1/2.9'" :by |MOD-LOGAND Subgoal *1/2.9'|)
	   ("Subgoal *1/2.8'" :by |MOD-LOGAND Subgoal *1/2.8'|)
	   ("Subgoal *1/2.6'" :by |MOD-LOGAND Subgoal *1/2.6'|)
	   ))

 )

(defthm |(integerp (* 1/2 (logand x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logand x y)))
		  (or (integerp (* 1/2 x))
		      (integerp (* 1/2 y)))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x)
				(integerp y))
			   (equal (integerp (* 1/2 (logand x y)))
				  (or (integerp (* 1/2 x))
				      (integerp (* 1/2 y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x)))
			   (integerp (* 1/2 (logand x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 y)))
			   (integerp (* 1/2 (logand x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (not (integerp (* 1/2 (logand x y))))))))

;;; Masks:

(local
 (defun ind-hint (x n)
   (declare (xargs :measure (nfix n)))
   (if (or (zip x) (zp n))
       t
     (ind-hint (floor x 2) (+ -1 n)))))

(defthm logand-mask
  (implies (and (integerp x) 
		(integerp n)
		(<= 0 n))
	   (equal (logand x (+ -1 (expt 2 n)))
		  (mod x (expt 2 n))))
  :hints (("Goal" :do-not '(generalize)
	   :in-theory (enable mod)
	   :cases ((equal n 0)))
	  ("Subgoal 2" :induct (ind-hint x n))))

(defun l-c-m-fn (c)  
  ;; logand-constant-mask, not least-common-multiple.  We need fewer
  ;; collisions among TLAs.
  (let ((n (power-of-2-minus-1 c)))
    (if n
	(list (cons 'n (kwote n)))
      nil)))

(defthm logand-constant-mask
 (implies (and (bind-free (l-c-m-fn c) (n))
	       (integerp n)
	       (<= 0 n)
	       (equal (+ -1 (expt 2 n)) c)
	       (integerp x) )
	  (equal (logand c x)
		 (mod x (+ 1 c)))))

;;; A messy, slow, proof:

(defthm logand-mask-shifted
  (implies (and (integerp x) 
		(integerp n1)
		(integerp n2)
		(<= 0 n1)
		(<= 0 n2))
	   (equal (logand x (* (expt 2 n1)
			       (+ -1 (expt 2 n2))))
		  (* (expt 2 n1)
		     (mod (floor x (expt 2 n1))
			  (expt 2 n2)))))
  :hints (("Goal" :do-not '(generalize)
	   :induct (ind-hint x n1))))

(in-theory (disable logand))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logior associativity and commutativity:

(defthm |(logior y x)|
  (equal (logior y x)
	 (logior x y)))

(defthm |(logior (logior x y) z)|
  (equal (logior (logior x y) z)
	 (logior x y z)))

(defthm |(logior y x z)|
  (equal (logior y x z)
	 (logior x y z)))

(defthm |(logior c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logior c d x)
		  (logior (logior c d) x))))

;;; ``Base'' theorems:

(defthm logior-0-x
  (implies (integerp x)
	   (equal (logior 0 x)
		  x)))

(defthm |(logior 1 x)|
  (implies (integerp x)
	   (equal (logior 1 x)
		  (if (evenp x)
		      (+ 1 x)
		    x)))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logior--1-x
  (implies (integerp x)
	   (equal (logior -1 x)
		  -1)))

(defthm logior-x-x
  (implies (integerp x)
	   (equal (logior x x)
		  x)))

;;; Misc:

(defthm logior-bounds-pos
  (implies (and (integerp x)
		(integerp y)
		(< 0 x)
		(< 0 y))
	   (<= x (logior x y)))
  :hints (("Goal" :in-theory (e/d (logior
				   lognot)
				  (;lognot-logand
				   logand-bounds-neg))
	   :use (:instance logand-bounds-neg
			   (X (+ -1 (- x)))
			   (y (+ -1 (- y)))))))

(defthm |(equal (logior x y) 0)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (equal (logior x y) 0)
		  (and (equal x 0)
		       (equal y 0)))))

(defthm |(< (logior x y) 0)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (< (logior x y) 0)
		  (or (< x 0)
		      (< y 0))))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0))
			   (< (logior x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< y 0))
			   (< (logior x y) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< 0 x)
				(< 0 y))
			   (< 0 (logior x y))))))

;;; this next bunch should be generalized to any power of 2

(defthm |(logior (* 2 x) (* 2 y))|
  (implies (and (rationalp x)
		(rationalp y)
		(integerp (* 2 x))
		(integerp (* 2 y)))
	   (equal (logior (* 2 x) (* 2 y))
		  (cond ((and (integerp x)
			      (integerp y))
			 (* 2 (logior x y))
			 )
			((and (integerp x)
			      (not (integerp y)))
			 (+ 1 (* 2 (logior x (+ -1/2 y))))
			 )
			((and (not (integerp x))
			      (integerp y))
			 (+ 1 (* 2 (logior (+ -1/2 x) y)))
			 )
			(t
			 (+ 1 (* 2 (logior (+ -1/2 x) (+ -1/2 y))))
			 ))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(rationalp x)
				(rationalp y)
				(integerp (* 2 x))
				(integerp (* 2 y)))
			   (equal (logior (* 2 x) (* 2 y))
				  (cond ((and (integerp x)
					      (integerp y))
					 (* 2 (logior x y)))
					((and (integerp x)
					      (not (integerp y)))
					 (+ 1 (* 2 (logior x (+ -1/2 y)))))
					((and (not (integerp x))
					      (integerp y))
					 (+ 1 (* 2 (logior (+ -1/2 x) y))))
					(t
					 (+ 1 (* 2 (logior (+ -1/2 x) (+ -1/2 y)))))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(integerp x)
				(integerp y))
			   (equal (logior (* 2 x) (* 2 y))
				  (* 2 (logior x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(rationalp x)
				(not (integerp x))
				(integerp y))
			   (equal (logior (* 2 x) (* 2 y))
				  (+ 1 (* 2 (logior (+ -1/2 x) y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(integerp x)
				(rationalp y)
				(not (integerp y)))
			   (equal (logior (* 2 x) (* 2 y))
				  (+ 1 (* 2 (logior x (+ -1/2 y)))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(rationalp x)
				(not (integerp x))
				(rationalp y)
				(not (integerp y)))
			   (equal (logior (* 2 x) (* 2 y))
				  (+ 1 (* 2 (logior (+ -1/2 x) (+ -1/2 y))))))))
  :hints (("Goal" :expand ((LOGAND (+ -1 (* -2 X))
				   (+ -1 (* -2 Y)))))))

(defthm |(logior (floor x 2) (floor y 2))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (logior (floor x 2) (floor y 2))
		  (floor (logior x y) 2)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y))
			   (equal (logior (floor x 2) (floor y 2))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 y)))
			   (equal (logior (floor x 2) (* 1/2 y))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 y))))
			   (equal (logior (floor x 2) (+ -1/2 (* 1/2 y)))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x)))
			   (equal (logior (* 1/2 x) (floor y 2))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (equal (logior (* 1/2 x) (* 1/2 y))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(not (integerp (* 1/2 y))))
			   (equal (logior (* 1/2 x) (+ -1/2 (* 1/2 y)))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x))))
			   (equal (logior (+ -1/2 (* 1/2 x)) (floor y 2))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(integerp (* 1/2 y)))
			   (equal (logior (+ -1/2 (* 1/2 x)) (* 1/2 y))
				  (floor (logior x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (equal (logior (+ -1/2 (* 1/2 x)) (+ -1/2 (* 1/2 y)))
				  (floor (logior x y) 2)))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logior-floor-expt-2-n
  (implies (and (integerp x)
		(integerp y)
		(integerp n)
		(<= 0 n))
	   (equal (logior (floor x (expt 2 n))
			  (floor y (expt 2 n)))
		  (floor (logior x y) (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (;LOGNOT-LOGAND
				   )
				  (logior))
				  :induct (ind-fn n)
				  :do-not '(generalize eliminate-destructors))
	  ("Subgoal *1/2" :use ((:instance |(logior (floor x 2) (floor y 2))|
					   (x (FLOOR X (EXPT 2 (+ -1 N))))
					   (y (FLOOR Y (EXPT 2 (+ -1 N)))))
				))
	   ))

(defthm |(mod (logior x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logior x y) 2)
		  (if (and (integerp (* 1/2 x))
			   (integerp (* 1/2 y)))
		      0
		    1)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x)
				(integerp y))
			   (equal (mod (logior x y) 2)
				  (if (and (integerp (* 1/2 x))
					   (integerp (* 1/2 y)))
				      0
				    1))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (equal (mod (logior x y) 2)
				  0)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x))))
			   (equal (mod (logior x y) 2)
				  1)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 y))))
			   (equal (mod (logior x y) 2)
				  1)))))

;;; Speed me up.  This is a crude patch job on an earlier proof.

(encapsulate
 ()

 (local
  (defun floor-2-n-ind (x y n)
    (cond ((zip n)
	   (+ x y))
	  ((< 0 n)
	   (floor-2-n-ind (floor x 2) (floor y 2) (+ -1 n)))
	  (t
	   (floor-2-n-ind (floor x 2) (floor y 2) (+ 1 n))))))

 (local
  (defthm |(integerp (* 1/2 (logior x y)))|
    (implies (and (integerp x)
		  (integerp y))
	     (equal (integerp (* 1/2 (logior x y)))
		    (and (integerp (* 1/2 x))
			 (integerp (* 1/2 y)))))))

 (local
  (defthm break-logior-apart
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logior x y)
		    (+ (* 2 (logior (floor x 2) (floor y 2)))
		       (logior (mod x 2) (mod y 2)))))
    :hints (("Goal" :in-theory (disable logior)))
    :rule-classes nil))

 (local
 (defthm crock-0
  (implies (and (integerp x)
		(not (integerp (* 1/2 x)))
		(integerp n)
		(< 0 n))
	   (not (integerp (* 1/2 (mod x (expt 2 n))))))))

 (local
  (defthm crock-1
    (implies (and (integerp x)
		  (integerp (* 1/2 x))
		  (integerp n)
		  (< 0 n))
	     (integerp (* 1/2 (mod x (expt 2 n)))))))

 (local
  (defthm crock-2
    (implies (and (integerp x)
		  (integerp n)
		  (< 0 n)
		  (EQUAL (MOD X (EXPT 2 N)) 0))
	     (INTEGERP (* 1/2 X)))))

 (defthm mod-logior-expt-2-n
   (implies (and (integerp x)
		 (integerp y)
		 (integerp n))
	    (equal (logior (mod x (expt 2 n))
			   (mod y (expt 2 n)))
		   (mod (logior x y) (expt 2 n))))
   :hints (("Goal" :induct (floor-2-n-ind x y n)
	    :in-theory (disable logior)
	    :do-not '(generalize eliminate-destructors))
	   ("Subgoal *1/2" :use ((:instance break-logior-apart)
				 (:instance break-logior-apart
					    (x (MOD X (EXPT 2 N)))
					    (y (MOD Y (EXPT 2 N))))))
	   ))
 )

(defthm |(integerp (* 1/2 (logior x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logior x y)))
		  (and (integerp (* 1/2 x))
		       (integerp (* 1/2 y))))))

;;; Masks
#|
(IMPLIES (AND (< Y (EXPT 2 N))
              (INTEGERP X)
              (<= 0 X)
              (INTEGERP Y)
              (<= 0 Y)
              (INTEGERP N)
              (<= 0 N))
         (EQUAL (LOGIOR Y (* X (EXPT 2 N)))
                (+ Y (* X (EXPT 2 N)))))
|#

(in-theory (disable logior))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Do I want logand or logior on the outside?
#|
(defthm logior-logand
  (implies (and (integerp x)
		(integerp y)
		(integerp z))
	   (equal (logior x (logand y z))
		  (logand (logior x y) (logior x z)))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logxor associativity and commutativity:

(defthm |(logxor y x)|
  (equal (logxor y x)
	 (logxor x y)))
#|
(defthm |(logxor (logxor x y) z)|
  (equal (logxor (logxor x y) z)
	 (logxor x y z)))

(defthm |(logxor y x z)|
  (equal (logxor y x z)
	 (logxor x y z)))

(defthm |(logxor c d x)|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (logxor c d x)
		  (logxor (logxor c d) x))))
|#
;;; ``Base'' theorems:

(defthm logxor-0-x
  (implies (integerp x)
	   (equal (logxor 0 x)
		  x)))

(defthm logxor-1-x
  (implies (integerp x)
	   (equal (logxor 1 x)
		  (if (evenp x)
		      (+ 1 x)
		    (+ -1 x))))
  :hints (("Goal" :in-theory (enable logior 
				     logand))))

(defthm logxor--1-x
  (implies (integerp x)
	   (equal (logxor -1 x)
		  (lognot x))))

(defthm logxor-x-x
  (implies (integerp x)
	   (equal (logxor x x)
		  0))
  :hints (("Goal" :in-theory (enable logior 
				     logand))))

;;; Misc:



;;; this next bunch should be generalized to any power of 2

(defthm |(logxor (floor x 2) (floor y 2))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (logxor (floor x 2) (floor y 2))
		  (floor (logxor x y) 2)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y))
			   (equal (logxor (floor x 2) (floor y 2))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 y)))
			   (equal (logxor (floor x 2) (* 1/2 y))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 y))))
			   (equal (logxor (floor x 2) (+ -1/2 (* 1/2 y)))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x)))
			   (equal (logxor (* 1/2 x) (floor y 2))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (equal (logxor (* 1/2 x) (* 1/2 y))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(not (integerp (* 1/2 y))))
			   (equal (logxor (* 1/2 x) (+ -1/2 (* 1/2 y)))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x))))
			   (equal (logxor (+ -1/2 (* 1/2 x)) (floor y 2))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(integerp (* 1/2 y)))
			   (equal (logxor (+ -1/2 (* 1/2 x)) (* 1/2 y))
				  (floor (logxor x y) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (equal (logxor (+ -1/2 (* 1/2 x)) (+ -1/2 (* 1/2 y)))
				  (floor (logxor x y) 2)))))
  :hints (("Goal" :in-theory (enable logand
				     logior))))

(defthm |(mod (logxor x y) 2)|
  (implies (and (integerp x)
		(integerp y))
	   (equal (mod (logxor x y) 2)
		  (cond ((and (integerp (* 1/2 x))
			      (not (integerp (* 1/2 y))))
			 1)
			((and (not (integerp (* 1/2 x)))
			      (integerp (* 1/2 y)))
			 1)
			(t
			 0))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x)
				(integerp y))
			   (equal (mod (logxor x y) 2)
				  (cond ((and (integerp (* 1/2 x))
					      (not (integerp (* 1/2 y))))
					 1)
					((and (not (integerp (* 1/2 x)))
					      (integerp (* 1/2 y)))
					 1)
					(t
					 0)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(not (integerp (* 1/2 y))))
			   (equal (mod (logxor x y) 2)
				  1)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(integerp (* 1/2 y)))
			   (equal (mod (logxor x y) 2)
				  1)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (equal (mod (logxor x y) 2)
				  0)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (equal (mod (logxor x y) 2)
				  0)))))

(defthm |(integerp (* 1/2 (logxor x y)))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (integerp (* 1/2 (logxor x y)))
		  (iff (integerp (* 1/2 x))
		       (integerp (* 1/2 y)))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x)
				(integerp y))
			   (equal (integerp (* 1/2 (logxor x y)))
				  (iff (integerp (* 1/2 x))
				       (integerp (* 1/2 y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(integerp (* 1/2 y)))
			   (integerp (* 1/2 (logxor x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (integerp (* 1/2 (logxor x y)))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(integerp (* 1/2 x))
				(not (integerp (* 1/2 y))))
			   (not (integerp (* 1/2 (logxor x y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(integerp (* 1/2 y)))
			   (not (integerp (* 1/2 (logxor x y))))))))

(in-theory (disable logxor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; lognot

#|
(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (< '-1 (LOGNOT I)) (< I '0))))

(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (< '0 (LOGNOT I)) (< I '-1))))

(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (< (LOGNOT I) '-1) (< '0 I))))

(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (< (LOGNOT I) '0)
                     (NOT (< I '0)))))

(THM (IMPLIES (IF (CASE-SPLIT (INTEGERP I))
		  (CASE-SPLIT (RATIONALP K))
		  'NIL)
	      (EQUAL (< (LOGNOT I) K)
		     (< (BINARY-+ '-1 (UNARY-- K)) I))))
|#

(defthm |(equal (lognot x) (lognot y))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (equal (lognot x) (lognot y))
		  (equal x y))))

(defthm |(equal (lognot x) -1)|
  (implies (integerp x)
	   (equal (equal (lognot x) -1)
		  (equal x 0))))

(defthm |(equal (lognot x) 0)|
  (equal (equal (lognot x) 0)
         (equal x -1)))

;;; this next bunch should be generalized to any power of 2

(defthm |(lognot (* 2 x))|
  (implies (and (rationalp x)
		(integerp (* 2 x)))
	   (equal (lognot (* 2 x))
		  (if (integerp x)
		      (+ 1 (* 2 (lognot x)))
		    (* 2 (lognot (+ -1/2 x))))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(rationalp x)
				(integerp (* 2 x)))
			   (equal (lognot (* 2 x))
				  (if (integerp x)
				      (+ 1 (* 2 (lognot x)))
				    (* 2 (lognot (+ -1/2 x)))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x))
			   (equal (lognot (* 2 x))
				  (+ 1 (* 2 (lognot x))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp (* 2 x))
				(rationalp x)
				(not (integerp x)))
			   (equal (lognot (* 2 x))
				  (* 2 (lognot (+ -1/2 x))))))))

(defthm |(lognot (floor x 2))|
  (implies (integerp x)
	   (equal (lognot (floor x 2))
		  (floor (lognot x) 2)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (integerp x)
			   (equal (lognot (floor x 2))
				  (floor (lognot x) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp (* 1/2 x)))
			   (equal (lognot (* 1/2 x))
				  (floor (lognot x) 2))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(not (integerp (* 1/2 x))))
			   (equal (lognot (+ -1/2 (* 1/2 x)))
				  (floor (lognot x) 2))))))

(local
 (defthm floor-lognot-helper
   (implies (and (integerp x)
		 (integerp n)
		 (equal (+ 1 (mod x n))
			n))
	    (integerp (+ (/ n) (* x (/ n)))))
   :rule-classes nil))

(defthm floor-lognot
  (implies (and (integerp x)
		(integerp n)
		(<= 0 n))
	   (equal (lognot (floor x (expt 2 n)))
		  (floor (lognot x) (expt 2 n))))
  :hints (("Goal"			;:in-theory (enable logand)
	   :induct (ind-fn n)
	   :do-not '(generalize eliminate-destructors))
	  ("Subgoal *1/2" :use ((:instance
				 (:theorem
				  (implies (equal x y)
					   (equal (floor x 2)
						  (floor y 2))))
				 (x (FLOOR (LOGNOT X) (EXPT 2 (+ -1 N))))
				 (y (LOGNOT (FLOOR X (EXPT 2 (+ -1 N))))))))
	  ("Subgoal *1/2.2" :use (:instance floor-lognot-helper
					    (x x)
					    (n (expt 2 n))))))

(defthm |(mod (lognot x) 2)|
  (implies (integerp x)
	   (equal (mod (lognot x) 2)
		  (if (integerp (* 1/2 x))
		      1
		    0)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp x))
			   (equal (mod (lognot x) 2)
				  (if (integerp (* 1/2 x))
				      1
				    0))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(integerp (* 1/2 x)))
			   (equal (mod (lognot x) 2)
				  1)))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
				(integerp x)
				(not (integerp (* 1/2 x))))
			   (equal (mod (lognot x) 2)
				  0)))))

(defthm |(integerp (* 1/2 (lognot x)))|
  (implies (integerp x)
	   (equal (integerp (* 1/2 (lognot x)))
		  (not (integerp (* 1/2 x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Should I flip the rhs and lhs of the below?

(defthm lognot-logand
  (implies (and (integerp x)
		(integerp y))
	   (equal (lognot (logand x y))
		  (logior (lognot x) (lognot y))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm lognot-logior
  (implies (and (integerp x)
		(integerp y))
	   (equal (lognot (logior x y))
		  (logand (lognot x) (lognot y))))
  :hints (("Goal" :in-theory (enable logior))))

#|
(defthm lognot-logxor
  (IMPLIES (AND (INTEGERP J) (INTEGERP I))
	   (EQUAL (LOGNOT (LOGXOR I J))
		  (LOGXOR J (LOGNOT I)))))

(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (BINARY-LOGAND I (LOGNOT I))
                     '0)))

(THM (IMPLIES (CASE-SPLIT (INTEGERP I))
              (EQUAL (BINARY-LOGIOR I (LOGNOT I))
                     '-1)))
|#

(defthm lognot-lognot
    (implies (case-split (integerp i))
	     (equal (lognot (lognot i))
		    i)))

(in-theory (disable lognot))
