; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; expt.lisp
;;
;;
;; This book contains some simple rules about expt.
;;
;; NOTE:  See also the end of this file.  We include six rules
;; which are too expensive for normal use, but are occasionally
;; useful.  They can be enabled as a group with
;; (in-theory (enable strong-expt-rules)).
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(local
 (include-book "../pass1/top"))

(local
 (include-book "expt-helper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We start out with some :type-prescription and :generalize
;; rules.

(defthm expt-type-prescription-rational
  (implies (rationalp x)
           (rationalp (expt x i)))
  :rule-classes (:type-prescription :generalize))

#+:non-standard-analysis
(defthm expt-type-prescription-real
  (implies (realp x)
           (realp (expt x i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integer
  (implies (and (<= 0 i)
                (integerp x))
           (integerp (expt x i)))
  :rule-classes (:type-prescription :generalize))

;; NOTE: Should the next 3 rules be :linear rules also?
;; Since they compare to zero, probably not.

(defthm expt-type-prescription-non-zero
  (implies (and (acl2-numberp x)
                (not (equal x 0)))
           (not (equal (expt x i) 0)))
  :rule-classes (:type-prescription :generalize))

; In expt-type-prescription-positive, variable x was renamed to r in v2-8 in order to get
; compatibility with books/arithmetic/equalities.
(defthm expt-type-prescription-positive
  (implies (and (< 0 r)
                (real/rationalp r))
           (< 0 (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonnegative
  (implies (and (<= 0 x)
                (real/rationalp x))
           (<= 0 (expt x i)))
  :rule-classes (:type-prescription :generalize))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Since expt will be disabled, I provide some rules to take care
;; of the ``simple'' cases.  These include a couple of rules
;; which will ensure that I know that all of the arguments of
;; expt are of the appropriate type when I get to
;; collect-terms.lisp and cancel-terms.lisp.

(defthm |(equal (expt x i) 0)|
  (equal (equal (expt x i) 0)
	 (and (equal (fix x) 0)
	      (not (equal (ifix i) 0)))))

(defthm |(expt x 0)|
  (equal (expt x 0)
        1))

(defthm |(expt 0 i)|
  (equal (expt 0 i)
         (if (zip i)
             1
           0)))

(defthm |(expt x 1)|
  (equal (expt x 1)
         (fix x)))

(defthm |(expt 1 i)|
  (equal (expt 1 i)
         1))

(defthm |(expt x -1)|
  (equal (expt x -1)
	 (/ x)))

(defthm case-split-on-non-integer-exponents
  (implies (case-split (not (integerp n)))
	   (equal (expt x n)
		  1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; I should probably expand (expt (+ c x) d), when c and d are const.

(defthm |(expt (+ x y) 2)|
  (equal (expt (+ x y) 2)
	 (+ (expt x 2) (* 2 x y) (expt y 2)))
  :hints (("Goal" :expand (expt (+ x y) 2))))

(defthm |(expt (+ x y) 3)|
  (equal (expt (+ x y) 3)
	 (+ (expt x 3) (* 3 (expt x 2) y) (* 3 x (expt y 2)) (expt y 3)))
  :hints (("Goal" :expand ((expt (+ x y) 3)
			   (expt (+ x y) 2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm |(/ (expt x i))|
  (equal (/ (expt x i))
         (expt (/ x) i)))

(local
 (in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-EXPT-/-BASE)))

; !!! I should look more closely at the next two lemmatta. !!!

(defthm |(expt x (- i))|
  (equal (expt x (- i))
	 (expt (/ x) i)))

(defthm |(expt (/ x) (* c i))|
  (implies (syntaxp (quotep c))
	   (equal (expt (/ x) (* c i))
                  (expt x (* (- c) i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(expt (* x y) i)|
  (equal (expt (* x y) i)
         (* (expt x i)
            (expt y i))))

(defthm |(expt (expt x i) j)|
  (implies (and (integerp i)
                (integerp j))
           (equal (expt (expt x i) j)
                  (expt x (* i j)))))

(defthm |(expt x (+ i j))|
  (implies (and (integerp i)
		(integerp j))
	   (equal (expt x (+ i j))
		  (if (equal (+ i j) 0)
		      1
		      (* (expt x i)
			 (expt x j))))))

; Do I really need these next three lemmas?

(defthm |(expt x (+ i j)) with non-negative exponents|
  (implies (and (<= 0 i)
		(<= 0 j)
		(integerp i)
		(integerp j))
	   (equal (expt x (+ i j))
		  (* (expt x i)
		     (expt x j)))))

(defthm |(expt x (+ i j)) with non-positive exponents|
  (implies (and (<= i 0)
		(<= j 0)
		(integerp i)
		(integerp j))
	   (equal (expt x (+ i j))
		  (* (expt x i)
		     (expt x j)))))

(defthm |(expt x (+ i j)) with non-zero base|
  (implies (and (not (equal 0 x))
		(acl2-numberp x)
		(integerp i)
		(integerp j))
	   (equal (expt x (+ i j))
		  (* (expt x i)
		     (expt x j)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; !!! This next batch of lemmatta should be eliminated by my
; forthcoming free-var-hack. !!!

;; Two sets of linear rules for expt.
;; The first set consists of rules which are both linear and
;; rewrite rules.  The second set are linear rules only.

(defthm expt-expt-linear-a
  (implies (and (< 1 x)
		(< i j)
		(real/rationalp x)
		(integerp i)
		(integerp j))
	   (< (expt x i)
	      (expt x j)))
  :rule-classes (:rewrite :linear))

(defthm expt-expt-linear-b
  (implies (and (< 0 x)
                (< x 1)
                (< i j)
                (real/rationalp x)
                (integerp i)
                (integerp j))
           (< (expt x j)
              (expt x i)))
  :rule-classes (:rewrite :linear))

(defthm expt-expt-linear-c
  (implies (and (<= 1 x)
                (<= i j)
                (real/rationalp x)
                (integerp i)
                (integerp j))
           (<= (expt x i)
               (expt x j)))
  :rule-classes (:rewrite :linear))

(defthm expt-expt-linear-d
  (implies (and (< 0 x)
                (<= x 1)
                (<= i j)
                (real/rationalp x)
                (integerp i)
                (integerp j))
           (<= (expt x j)
               (expt x i)))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-a
  (implies (and (real/rationalp x)
                (< 1 x)
                (integerp c)
                (< 1 c))
           (< x (expt x c)))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-b
  (implies (and (real/rationalp x)
                (< x 1)
                (< 0 x)
                (integerp c)
                (< 1 c))
           (< (expt x c) x))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-c
  (implies (and (real/rationalp x)
                (<= 1 x)
                (integerp c)
                (<= 1 c))
           (<= x (expt x c)))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-d
  (implies (and (real/rationalp x)
                (<= x 1)
                (<= 0 x)
                (integerp c)
                (<= 1 c))
           (<= (expt x c) x))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-e
  (implies (and (real/rationalp x)
                (< 1 x)
                (integerp c)
                (<= c 0))
           (< (expt x c) x))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-f
  (implies (and (real/rationalp x)
                (< x 1)
                (< 0 x)
                (integerp c)
                (<= c 0))
           (< x (expt x c)))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-g
  (implies (and (real/rationalp x)
                (<= 1 x)
                (integerp c)
                (<= c 0))
           (<= (expt x c) x))
  :rule-classes (:rewrite :linear))

(defthm expt-x-linear-h
  (implies (and (real/rationalp x)
                (<= x 1)
                (<= 0 x)
                (integerp c)
                (<= c 0))
           (<= x (expt x c)))
  :rule-classes (:rewrite :linear))

;; Should these be rewrite rules also? Probably not.

(defthm expt-1-linear-a
  (implies (and (< 1 x)
		(< 0 i)
		(real/rationalp x)
		(integerp i))
	   (< 1 (expt x i)))
  :rule-classes :linear)

(defthm expt-1-linear-b
  (implies (and (<= 0 x)
		(< x 1)
		(< 0 i)
		(real/rationalp x)
		(integerp i))
	   (< (expt x i) 1))
  :rule-classes :linear)

(defthm expt-1-linear-c
  (implies (and (<= 1 x)
		(<= 0 i)
		(real/rationalp x)
		(integerp i))
	   (<= 1 (expt x i)))
  :rule-classes :linear)

(defthm expt-1-linear-d
  (implies (and (<= 0 x)
		(<= x 1)
		(<= 0 i)
		(real/rationalp x)
		(integerp i))
	   (<= (expt x i) 1))
  :rule-classes :linear)

(defthm expt-1-linear-e
  (implies (and (< 1 x)
		(< i 0)
		(real/rationalp x)
		(integerp i))
	   (< (expt x i) 1))
  :rule-classes :linear)

(defthm expt-1-linear-f
  (implies (and (< 0 x)
		(< x 1)
		(< i 0)
		(real/rationalp x)
		(integerp i))
	   (< 1 (expt x i)))
  :rule-classes :linear)

(defthm expt-1-linear-g
  (implies (and (<= 1 x)
		(<= i 0)
		(real/rationalp x)
		(integerp i))
	   (<= (expt x i) 1))
  :rule-classes :linear)

(defthm expt-1-linear-h
  (implies (and (< 0 x)
		(<= x 1)
		(< i 0)
		(real/rationalp x)
		(integerp i))
	   (<= 1 (expt x i)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The next six rules are exported disabled.  They are
;; somewhat expensive for daily wear, but are occasionally
;; useful.

(defthm expt-type-negative-base-even-exponent
  (implies (and (< x 0)
		(real/rationalp x)
		(integerp i)
		(integerp (* 1/2 i)))
	   (< 0 (expt x i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-negative-base-odd-exponent
  (implies (and (< x 0)
		(real/rationalp x)
		(integerp i)
		(not (integerp (* 1/2 i))))
	   (< (expt x i) 0))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-nonpositive-base-even-exponent
  (implies (and (<= x 0)
                (real/rationalp x)
		(integerp i)
		(integerp (* 1/2 i)))
           (<= 0 (expt x i)))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-negative-base-even-exponent)))))

(defthm expt-type-nonpositive-base-odd-exponent
  (implies (and (<= x 0)
                (real/rationalp x)
		(integerp i)
		(not (integerp (* 1/2 i))))
           (<= (expt x i) 0))
  :rule-classes (:type-prescription :generalize)
  :hints (("Goal" :use ((:instance
			 expt-type-negative-base-odd-exponent)))))

(defthm expt-negative-base-even-exponents
  (implies (and (real/rationalp x)
		(integerp i)
		(integerp (* 1/2 i)))
	   (equal (expt (- x) i)
		  (expt x i)))
  :hints (("Goal" :use ((:instance
                         expt-negative-base-even-exponent
                         (r x))))))

(defthm expt-negative-base-odd-exponents
  (implies (and (real/rationalp x)
		(integerp i)
		(not (integerp (* 1/2 i))))
	   (equal (expt (- x) i)
		  (- (expt x i))))
  :hints (("Goal" :use ((:instance
                         expt-negative-base-odd-exponent
                         (r x))))))

(deftheory strong-expt-rules
  `(expt-type-negative-base-even-exponent
    expt-type-negative-base-odd-exponent
    expt-type-nonpositive-base-even-exponent
    expt-type-nonpositive-base-odd-exponent
    expt-negative-base-even-exponents
    expt-negative-base-odd-exponents))

(in-theory (disable strong-expt-rules))
