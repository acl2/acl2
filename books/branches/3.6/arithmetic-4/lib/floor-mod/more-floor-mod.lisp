;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; more-floor-mod.lisp
;;;
;;; Here are some more theorems about floor and mod.
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

(SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID STABLE-UNDER-SIMPLIFICATIONP
                                  HIST NIL)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm extra-intp-thm-1
   (IMPLIES (AND (INTEGERP (* (/ I) (/ J) X))
              (RATIONALP X)
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
		 (RATIONALP X)
		 (INTEGERP I)
		 (INTEGERP J))
	    (INTEGERP (* (/ J) (FLOOR X I))))
   :hints (("Goal" :cases ((equal j 0))))))

(defthm |(floor (+ x r) i)|
  (implies (and (integerp x)
                ;(<= 0 x)
                (rationalp r)
                (<= 0 r)
                (< r 1)
                (integerp i)
                (< 0 i)
		)
           (equal (floor (+ x r) i)
                  (floor x i))))

;;; Move with floor-floor-integer?

(defthm mod-x-i*j   ;;; OK
    (implies
     (and (> i 0)
	  (> j 0)
	  (force (integerp i))
	  (force (integerp j))
	  (force (real/rationalp x)))
     (equal (mod x (* i j))
	    (+ (mod x i) (* i (mod (floor x i) j))))))

;;; Beter version:

(local
 (defthm this-is-odd
  (IMPLIES (AND (INTEGERP I)
		(INTEGERP J)
		(RATIONALP X)
		(< J 0)
		(NOT (INTEGERP (* (/ I) (/ J) X)))
		(INTEGERP (* (/ J) (FLOOR X I))))
	   (EQUAL (MOD X (* I J))
		  (+ (* i j) (mod x i))))))

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
		 (+ (mod x i) (* i (mod (floor x i) j)))))))
  :hints (("Subgoal 3" :use (:instance this-is-odd))
	  ("Subgoal 2" :cases ((equal j 0))))
  :otf-flg t)

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
                (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (equal (equal (* j (floor i j)) i)
                  (integerp (* i (/ j))))))

(defthm mod-plus-mod-2   ;;; OK
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
  (implies (and (rationalp a)
		(integerp b)
		(rationalp n)
		(not (equal n 0)))
	   (equal (mod (* (mod a n) b) n)
		  (mod (* a b) n))))

(defthm mod-theorem-one-b   ;;; OK
  (implies (and (rationalp a)
		(integerp b)
		(rationalp n)
		(not (equal n 0)))
	   (equal (mod (* b (mod a n)) n)
		  (mod (* a b) n))))

(encapsulate ()

 (local
  (defun ind-fn (i)
    (if (zp i)
	t
      (ind-fn (+ -1 i)))))

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
  (defthm mod-theorem-two-helper-helper
    (IMPLIES (AND (NOT (ZP I))
		  (EQUAL (MOD (EXPT A I) N)
			 (MOD (EXPT (MOD A N) I) N))
		  (INTEGERP A)
		  (integerp b)
		  (INTEGERP N)
		  (NOT (EQUAL N 0)))
	     (EQUAL (MOD (* b (EXPT (MOD A N) I)) N)
		    (MOD (* b (EXPT A I)) N)))
    :hints (("Goal" :induct (ind-fn b)))))

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
  (implies (and (rationalp m)
                (rationalp n)
                (rationalp k)
                )
           (equal (mod (* k m) (* k n))
                  (* k (mod m n))))
  :otf-flg t)

(defthm mod-mult
    (implies (and (integerp a)
                  (rationalp m)
		  (rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))


;;; floor rule like below also?

(defthm mod-sums-cancel-1
  (implies (and (case-split (<= 0 y))
                (case-split (rationalp k))
                (case-split (rationalp y))
                (case-split (rationalp x1))
                (case-split (rationalp x2))
                )
           (equal (equal (mod (+ k x1) y) (mod (+ k x2) y))
                  (equal (mod x1 y) (mod x2 y)))))

(defthm  |(equal (mod a n) (mod b n))|
  (implies (and (integerp (+ (* a (/ n)) (- (* b (/ n)))))
		(rationalp a)
		(rationalp b)
		(rationalp n)
		(not (equal n 0)))
	   (equal (equal (mod a n) (mod b n))
		  t))
  :hints (("Goal" :use (:instance mod-zero
				  (x (+ a (- b)))
				  (y n))
	          :in-theory (e/d ()
				  (mod-zero)))))

;;; Will this base case for the above be caught, or should we have a
;;; second rule?

;;; Add default-xxx rules 
;;; add if normalization rules

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
	     (rationalp x)
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
