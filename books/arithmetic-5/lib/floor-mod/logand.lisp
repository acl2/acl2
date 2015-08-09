; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

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

(local (in-theory (disable not-integerp-type-set-rules

                           EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                           EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A

                           ;; new ones
                           default-plus-1
                           default-plus-2
                           default-times-1
                           default-times-2
                           default-floor-ratio
                           default-divide
                           default-minus
                           cancel-floor-+
                           |(floor (+ x r) i)|
                           mod-positive
                           mod-negative
                           mod-nonpositive
                           floor-nonnegative
                           floor-negative
                           floor-positive
                           floor-nonpositive
                           rationalp-x
                           INTEGERP-/-EXPT-2
                           the-floor-below
                           |(equal c (- x))|
                           (:REWRITE FLOOR-X-Y-=-1 . 2)
                           (:REWRITE MOD-X-Y-=-X+Y . 1)
                           default-less-than-1
                           default-expt-1
                           default-expt-2
                           default-floor-1
                           default-floor-2
                           default-mod-2
                           mod-bounds-2
                           floor-zero
                           mod-zero
                           mod-x-y-=-x
                           mod-x-y-=-x-y


                           )))


;; Consider these:
; EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE
; EXPT-TYPE-PRESCRIPTION-NON-0-BASE

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
		(<= 0 x))
	   (<= (logand x y) x))
  :hints (("Goal" :in-theory (enable logand)))
  :rule-classes ((:rewrite)
		 (:linear)
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(<= 0 y))
			   (<= (logand x y) y)))

		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(<= 0 y))
			   (<= (logand x y) y)))))

(defthm logand-bounds-neg
  (implies (and (integerp x)
		(integerp y)
		(< x 0)
		(< y 0))
	   (<= (logand x y) x))
  :hints (("Goal" :in-theory (enable logand)))
  :rule-classes ((:rewrite)
		 (:linear)
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0)
				(< y 0))
			   (<= (logand x y) y)))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0)
				(< y 0))
			   (<= (logand x y) y)))))

(defthm |(equal (logand x y) -1)|
  (equal (equal (logand x y) -1)
	 (and (equal x -1)
	      (equal y -1))))

;;; Is there a nice rule for (< 0 (logand x y))
;;; Do |(< (logand x y) (expt 2 n))|

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
  (implies (and (real/rationalp x)
		(real/rationalp y)
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
				(real/rationalp x)
				(real/rationalp y)
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
				(real/rationalp x)
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
				(real/rationalp y)
				(not (integerp y)))
			   (equal (logand (* 2 x) (* 2 y))
				  (* 2 (logand x (+ -1/2 y))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(real/rationalp x)
				(not (integerp x))
				(real/rationalp y)
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

(encapsulate
 ()
 (local (in-theory (enable EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
 (defthm logand-floor-expt-2-n
   (implies (and (integerp x)
		 (integerp y)
		 (integerp n))
	    (equal (logand (floor x (expt 2 n))
			   (floor y (expt 2 n)))
		   (floor (logand x y) (expt 2 n))))
   :hints (("Goal" ;:in-theory (enable logand)
	    :induct (ind-fn n)
	    :do-not '(generalize eliminate-destructors))
	   ("Subgoal *1/3" :use ((:instance |(logand (floor x 2) (floor y 2))|
					    (x (FLOOR X (EXPT 2 (+ -1 N))))
					    (y (FLOOR Y (EXPT 2 (+ -1 N))))))
            :in-theory (disable |(logand (floor x 2) (floor y 2))|
                                logand))
	   )))

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

 (local (in-theory (enable EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                           mod-zero)))

 (local
  (defthm |(integerp (* 1/2 (mod x (expt 2 n))))|
    ;; Jared discovered this rule by analyzing the several lemmas that used to
    ;; be here.  It turns out that this one rule takes care of everything.
    ;; Robert, should this rule be unlocalized?
    (implies (and (< 0 n)
                  (integerp n))
             (equal (integerp (* 1/2 (mod x (expt 2 n))))
                    (integerp (* 1/2 x))))))

 (local (in-theory (disable cancel-mod-+
                            (:TYPE-PRESCRIPTION MOD-ZERO . 4)
                            default-mod-ratio
                            default-times-2
                            default-+-2
                            (:REWRITE MOD-X-Y-=-X-Y . 2)
                            (:REWRITE MOD-X-Y-=-X . 4)
                            )))

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
					    (y (MOD Y (EXPT 2 N))))))))

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


(encapsulate
 ()
 (local (in-theory (enable expt-type-prescription-integerp-base
                           default-expt-1
                           default-expt-2
                           mod-zero)))

 (local (in-theory (disable (:REWRITE MOD-X-Y-=-X-Y . 2)
                            default-plus-1
                            default-plus-2
                            default-times-1
                            default-times-2
                            (:TYPE-PRESCRIPTION MOD-ZERO . 4)
                            (:TYPE-PRESCRIPTION FLOOR-ZERO . 4)
                            cancel-mod-+
                            (:REWRITE MOD-X-Y-=-X . 3)
                            (:REWRITE MOD-X-Y-=-X . 4)
                            )))

 ;; Jared just distilled these lemmas from the checkpoints.
 (local
  (defthm lemma
    (IMPLIES (and (EQUAL (EXPT 2 N1)
                         (MOD X (* (EXPT 2 N1) (EXPT 2 N2))))
                  (NOT (ZP N1)))
             (INTEGERP (* 1/2 X)))))

 (local
  (defthm lemma2
    (IMPLIES (AND (EQUAL (+ (* 1/2 (EXPT 2 N1))
                            (LOGAND (+ -1/2 (* 1/2 X))
                                    (+ (* -1/2 (EXPT 2 N1))
                                       (* 1/2 (EXPT 2 N1) (EXPT 2 N2)))))
                         (* 1/2 (MOD X (* (EXPT 2 N1) (EXPT 2 N2)))))
                  (NOT (ZP N1)))
             (INTEGERP (* 1/2 X)))))

 (local
  (defthm lemma3
    (IMPLIES (AND (EQUAL (+ (* 1/2 (EXPT 2 N1))
                            (LOGAND (+ -1/2 (* 1/2 X))
                                    (+ (* -1/2 (EXPT 2 N1))
                                       (* 1/2 (EXPT 2 N1) (EXPT 2 N2)))))
                         (+ (* 1/2 (EXPT 2 N1) (EXPT 2 N2))
                            (* 1/2
                               (MOD X (* (EXPT 2 N1) (EXPT 2 N2))))))
                  (NOT (ZP N1))
                  (INTEGERP N2)
                  (<= 0 N2))
             (integerp (* 1/2 x)))))

 (defthm logand-mask-shifted
   ;; This was taking 34 seconds, now it takes 6.24
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
   :hints (("Goal"
            :do-not '(generalize)
            :induct (ind-hint x n1)))))

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
		(<= 0 x)
		(<= 0 y))
	   (<= x (logior x y)))
  :hints (("Goal" :in-theory (e/d (logior
				   lognot)
				  (;lognot-logand
				   logand-bounds-neg))
	   :use (:instance logand-bounds-neg
			   (X (+ -1 (- x)))
			   (y (+ -1 (- y))))))
  :rule-classes ((:rewrite)
		 (:linear)
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(<= 0 x)
				(<= 0 y))
			   (<= y (logior x y))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(<= 0 x)
				(<= 0 y))
			   (<= y (logior x y))))))

(defthm logior-bounds-neg
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
			   (y (+ -1 (- y))))))
  :rule-classes ((:rewrite)
		 (:linear)
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0)
				(< y 0))
			   (<= y (logior x y))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< x 0)
				(< y 0))
			   (<= y (logior x y))))))

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
			   (< (logior x y) 0)))))

(defthm |(< 0 (logior x y))|
  (implies (and (integerp x)
		(integerp y))
	   (equal (< 0 (logior x y))
		  (or (and (< 0 x)
			   (<= 0 y))
		      (and (<= 0 x)
			   (< 0 y)))))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< 0 x)
				(<= 0 y))
			   (< 0 (logior x y))))
		 (:type-prescription
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(<= 0 x)
				(< 0 y))
			   (< 0 (logior x y))))))

;;; this next bunch should be generalized to any power of 2

(defthm |(logior (* 2 x) (* 2 y))|
  (implies (and (real/rationalp x)
		(real/rationalp y)
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
				(real/rationalp x)
				(real/rationalp y)
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
				(real/rationalp x)
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
				(real/rationalp y)
				(not (integerp y)))
			   (equal (logior (* 2 x) (* 2 y))
				  (+ 1 (* 2 (logior x (+ -1/2 y)))))))
		 (:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(integerp (* 2 x))
				(integerp (* 2 y))
				(real/rationalp x)
				(not (integerp x))
				(real/rationalp y)
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
 (local (in-theory (enable EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                           mod-zero)))

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
    (implies (and (EQUAL (MOD X (EXPT 2 N)) 0)
                  (integerp x)
		  (integerp n)
		  (< 0 n))
	     (INTEGERP (* 1/2 X)))))

 (local
  (in-theory
   (disable
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A)
    (:TYPE-PRESCRIPTION MOD-ZERO . 4)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B)
    (:REWRITE MOD-X-Y-=-X-Y . 2)
    (:TYPE-PRESCRIPTION MOD-ZERO . 2)
    (:REWRITE CANCEL-MOD-+)
    (:REWRITE DEFAULT-TIMES-2)
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
    (:REWRITE DEFAULT-PLUS-2)
    (:REWRITE DEFAULT-MOD-RATIO)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)
    (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2)
    (:REWRITE MOD-X-Y-=-X-Y . 1)
    (:REWRITE MOD-X-Y-=-X . 4)
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)
    (:REWRITE MOD-X-Y-=-X+Y . 1)
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2)
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)
    (:REWRITE DEFAULT-PLUS-1)
    (:REWRITE DEFAULT-TIMES-1)
    (:REWRITE |(mod (+ x (mod a b)) y)|)
    (:REWRITE |(mod (+ x (- (mod a b))) y)|)
    (:REWRITE DEFAULT-DIVIDE)
    (:TYPE-PRESCRIPTION MOD-ZERO . 3)
    (:TYPE-PRESCRIPTION MOD-POSITIVE . 2)
    (:TYPE-PRESCRIPTION MOD-POSITIVE . 1)
    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2)
    (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1)
    (:REWRITE MOD-X-Y-=-X-Y . 3)
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
    (:TYPE-PRESCRIPTION MOD-NONPOSITIVE)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A)
    (:REWRITE |(* (- x) y)|)
    (:REWRITE MOD-X-Y-=-X . 2)
    (:REWRITE |(< (logior x y) 0)|)
    (:REWRITE DEFAULT-MINUS)
    (:REWRITE DEFAULT-LESS-THAN-2)
    (:REWRITE DEFAULT-LESS-THAN-1)
    (:REWRITE MOD-CANCEL-*-CONST)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A)
    (:REWRITE MOD-X-Y-=-X+Y . 3)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A)
    (:REWRITE DEFAULT-TIMES-2)
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT)
    (:REWRITE DEFAULT-MOD-2)
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-<)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT)
    (:REWRITE |(* (+ x y) z)|)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT)
    (:LINEAR MOD-BOUNDS-2)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT)
    (:REWRITE DEFAULT-EXPT-2)
    (:REWRITE DEFAULT-EXPT-1)
; (:REWRITE |(expt 1/c n)|)
; (:REWRITE |(expt (- x) n)|)
    (:TYPE-PRESCRIPTION BUBBLE-DOWN)
    (:REWRITE DEFAULT-FLOOR-RATIO)
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<)
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<)
    (:REWRITE THE-FLOOR-BELOW)
    (:REWRITE THE-FLOOR-ABOVE)
    (:REWRITE INTEGERP-<-CONSTANT)
    (:REWRITE REMOVE-STRICT-INEQUALITIES)
    (:REWRITE |(< (/ x) (/ y))|)
    (:REWRITE |(< c (/ x)) positive c --- present in goal|)
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|)
    (:REWRITE |(< c (/ x)) negative c --- present in goal|)
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|)
    (:REWRITE |(< (/ x) c) positive c --- present in goal|)
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|)
    (:REWRITE |(< (/ x) c) negative c --- present in goal|)
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|)
    (:REWRITE CONSTANT-<-INTEGERP)
    (:REWRITE |(* (if a b c) x)|)
    (:REWRITE |(< (+ (- c) x) y)|)
    (:TYPE-PRESCRIPTION INTEGERP-MOD-2)
    (:TYPE-PRESCRIPTION INTEGERP-MOD-1)
    (:TYPE-PRESCRIPTION RATIONALP-MOD)
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B)
    (:META META-INTEGERP-CORRECT)
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL)
    (:LINEAR EXPT-X->-X)
    (:REWRITE DEFAULT-MOD-1)
    (:LINEAR EXPT-X->=-X)
    (:TYPE-PRESCRIPTION FLOOR-ZERO . 4)
; (:REWRITE BUBBLE-DOWN-*-MATCH-3)
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER)
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)
    (:LINEAR EXPT-<=-1-TWO)
    (:REWRITE |(< (* x y) 0)|)
    (:REWRITE |(< (/ x) 0)|)
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1)
    (:REWRITE |(equal (- x) (- y))|)
    (:LINEAR EXPT-LINEAR-UPPER-<=)
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
    (:REWRITE |(equal (/ x) c)|)
    (:REWRITE |(equal (- x) c)|)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT)
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT)
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1)
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1)
    (:REWRITE |(equal c (/ x))|)
    (:REWRITE |(equal (/ x) (/ y))|)
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE)
    (:REWRITE |(equal c (- x))|)
    (:TYPE-PRESCRIPTION FLOOR-ZERO . 2)
    (:REWRITE |(< x (+ c/d y))|)
    (:REWRITE DEFAULT-FLOOR-1)
    (:LINEAR EXPT-<-1-TWO)
    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1)
    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1)
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER)
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)
    (:REWRITE |(< 0 (* x y))|)
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)
    (:REWRITE MOD-ZERO . 1)
    (:LINEAR EXPT-LINEAR-UPPER-<)
    (:LINEAR EXPT-LINEAR-LOWER-<)
    (:LINEAR EXPT->=-1-TWO)
    (:LINEAR EXPT->-1-TWO)
    (:LINEAR EXPT-<=-1-ONE)
    (:LINEAR EXPT-<-1-ONE)
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL)
    (:REWRITE |(mod x (- y))| . 3)
    (:REWRITE |(mod x (- y))| . 2)
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|)
    (:REWRITE |(mod (- x) y)| . 3)
    (:REWRITE |(mod (- x) y)| . 2)
    (:REWRITE |(mod (- x) y)| . 1)
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|)
    (:REWRITE |(equal (mod (+ x y) z) x)|)
    (:TYPE-PRESCRIPTION ABS)
    (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<)
    (:REWRITE |(not (equal x (/ y)))|)
    (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<)
    (:TYPE-PRESCRIPTION FLOOR-ZERO . 3)
    (:TYPE-PRESCRIPTION FLOOR-ZERO . 1)
    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3)
    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2)
    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3)
    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2)
    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3)
    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2)
    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3)
    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2)
    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)
    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1)
    (:REWRITE |(equal x (/ y))|)
    (:REWRITE MOD-ZERO . 2)
    )))

 (defthm mod-logior-expt-2-n
   ;; 7.65 sec for the encapsulate
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

(encapsulate nil
  (local (in-theory
          (e/d ()
               (reduce-additive-constant-<
                (:REWRITE |(< (- x) c)|)
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3)
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2)
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1)
                (:LINEAR LOGAND-BOUNDS-POS . 1)
                (:LINEAR LOGAND-BOUNDS-POS . 2)
                (:LINEAR LOGAND-BOUNDS-NEG . 2)
                (:LINEAR LOGAND-BOUNDS-NEG . 1)
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL)
                (:REWRITE NORMALIZE-ADDENDS)
                (:REWRITE |(< (+ (- c) x) y)|)
                (:REWRITE |(< x (/ y)) with (< 0 y)|)
                (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|)
                (:REWRITE |(<= (* (/ x) y) -1) with (< 0 x)|)
                (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|)
                (:REWRITE |(<= (* (/ x) y) -1) with (< x 0)|)
                (:REWRITE |(< (/ x) y) with (< 0 x)|)
                (:REWRITE |(<= (/ x) y) with (< 0 x)|)
                (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|)
                (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|)
                (:REWRITE |(< -1 (* (/ x) y)) with (< 0 x)|)
                (:REWRITE |(< x (/ y)) with (< y 0)|)
                (:REWRITE |(<= (/ x) y) with (< x 0)|)
                (:REWRITE |(< -1 (* (/ x) y)) with (< x 0)|)
                (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<)
                (:REWRITE |(< (+ c/d x) y)|)
                (:REWRITE
                                    NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B)
                (:REWRITE DEFAULT-LESS-THAN-2)
                (:REWRITE
                                    |(floor (+ x y) z) where (< 0 z)| . 3)
                (:REWRITE PREFER-POSITIVE-ADDENDS-<)
                (:REWRITE
                                    |(floor (+ x y) z) where (< 0 z)| . 2)
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS)
                (:REWRITE THE-FLOOR-ABOVE)
                (:REWRITE FLOOR-X-Y-=--1 . 2)
                (:REWRITE
                                   REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<)
                (:REWRITE |(* (- x) y)|)
                (:REWRITE |(< (- x) (- y))|)
                (:REWRITE |(< (* x y) 0)|)
                (:REWRITE CONSTANT-<-INTEGERP)
                (:REWRITE
                                    SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)
                (:REWRITE |(floor x 2)| . 2)
                (:REWRITE |(< (logior x y) 0)|)
                (:REWRITE FLOOR-=-X/Y . 1)
                (:REWRITE
                                |(< c (/ x)) positive c --- present in goal|)
                (:REWRITE
                                   |(< c (/ x)) positive c --- obj t or nil|)
                (:REWRITE
                                |(< c (/ x)) negative c --- present in goal|)
                (:REWRITE
                                   |(< c (/ x)) negative c --- obj t or nil|)
                (:REWRITE |(< c (- x))|)
                (:REWRITE
                                |(< (/ x) c) positive c --- present in goal|)
                (:REWRITE
                                   |(< (/ x) c) positive c --- obj t or nil|)
                (:REWRITE
                                |(< (/ x) c) negative c --- present in goal|)
                (:REWRITE
                                   |(< (/ x) c) negative c --- obj t or nil|)
                (:REWRITE |(< (/ x) (/ y))|)
                (:REWRITE MOD-CANCEL-*-CONST)
                (:REWRITE REMOVE-STRICT-INEQUALITIES)
                (:REWRITE INTEGERP-<-CONSTANT)
                (:REWRITE FLOOR-CANCEL-*-CONST)
                (:REWRITE MOD-X-Y-=-X+Y . 2)
                (:REWRITE SIMPLIFY-SUMS-<)
                (:REWRITE REDUCE-INTEGERP-+)
                (:META META-INTEGERP-CORRECT)
                (:LINEAR LOGIOR-BOUNDS-POS . 2)
                (:LINEAR LOGIOR-BOUNDS-POS . 1)
                (:LINEAR LOGIOR-BOUNDS-NEG . 2)
                (:LINEAR LOGIOR-BOUNDS-NEG . 1)
                (:REWRITE |(* (* x y) z)|)
                (:REWRITE
                                    SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                (:LINEAR MOD-BOUNDS-3)
                (:REWRITE MOD-X-Y-=-X+Y . 3)
                (:REWRITE DEFAULT-LOGAND-2)
                (:REWRITE REMOVE-WEAK-INEQUALITIES)
                (:REWRITE |(< (logand x y) 0)|)
                (:REWRITE |(< (/ x) y) with (< x 0)|)
                (:REWRITE |(< (/ x) 0)|)
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2)
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1)
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2)
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)
                (:REWRITE SIMPLIFY-SUMS-EQUAL)
                (:REWRITE CANCEL-MOD-+)
                (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER)
                (:REWRITE
                                SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)
                (:REWRITE |(equal (/ x) (/ y))|)
                (:REWRITE |(equal c (/ x))|)
                (:REWRITE |(equal (/ x) c)|)
                (:TYPE-PRESCRIPTION MOD-NONNEGATIVE)
                (:TYPE-PRESCRIPTION INTEGERP-MOD-2)
                (:TYPE-PRESCRIPTION INTEGERP-MOD-1)
                (:REWRITE |(< (* x y) 0) rationalp (* x y)|)
                (:REWRITE DEFAULT-MOD-RATIO)
                (:TYPE-PRESCRIPTION RATIONALP-MOD)
                (:REWRITE |(floor x (- y))| . 2)
                (:REWRITE |(floor (- x) y)| . 2)
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE)
                (:REWRITE DEFAULT-LOGAND-1)
                (:REWRITE |(equal (+ (- c) x) y)|)
                (:REWRITE |(<= x (/ y)) with (< y 0)|)
                (:REWRITE LOGAND-CONSTANT-MASK)
                (:REWRITE |(not (equal (* (/ x) y) -1))|)
                (:REWRITE |(equal (* (/ x) y) -1)|)
                (:REWRITE |(mod x 2)| . 2)
                (:REWRITE |(< x (+ c/d y))|)
                (:REWRITE |(< y (+ (- c) x))|)
                (:REWRITE DEFAULT-LOGIOR-2)
                ))))
  (defthm |(logxor (floor x 2) (floor y 2))|
    ;; 9.66 seconds
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
    :hints (("Goal" :in-theory (enable logior logand)))))

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
  (implies (and (real/rationalp x)
		(integerp (* 2 x)))
	   (equal (lognot (* 2 x))
		  (if (integerp x)
		      (+ 1 (* 2 (lognot x)))
		    (* 2 (lognot (+ -1/2 x))))))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
				(real/rationalp x)
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
				(real/rationalp x)
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

(encapsulate
 ()
 (local (in-theory (enable expt-type-prescription-integerp-base)))

 (defthm floor-lognot
   ;; 10.2 seconds

   (implies (and (integerp x)
                 (integerp n)
                 (<= 0 n))
            (equal (lognot (floor x (expt 2 n)))
                   (floor (lognot x) (expt 2 n))))
   :hints (("Goal" ;:in-theory (enable logand)
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
                                             (n (expt 2 n)))))))

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

