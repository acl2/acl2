;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

; The following proof is due to John Cowles.

(in-package "ACL2")

(local (include-book "../../../arithmetic/top-with-meta"))

(local (include-book "../../../arithmetic/mod-gcd"))

;; The definition of nonneg-int-gcd often interacts with the rewrite rule,
;; commutativity-of-nonneg-int-gcd, to cause the rewriter to loop and stack
;; overflow. 
(local (in-theory (disable commutativity-of-nonneg-int-gcd)))

(local
 (defthm lemma-1
   (implies (and (rationalp x)
                 (integerp (* 2 x x)))
            (equal
             (* 2 (abs (numerator x))(abs (numerator x)))
             (* (denominator x)(denominator x)(numerator (* 2 x x)))))
   :rule-classes nil))

(local
 (defthm lemma-2
   (implies (and (integerp x)
                 (> x 0)
                 (integerp y)
                 (equal (* x y) z))
            (equal (nonneg-int-mod z x) 0))
   :rule-classes nil))

(local
 (defthm lemma-3
   (implies (and (rationalp x)
                 (integerp (* 2 x x)))
            (equal (nonneg-int-mod (* 2 (abs (numerator x)))
                                   (denominator x))
                   0))
   :hints (("Goal"
            :in-theory (disable abs)
            :use ((:instance
                   Divisor-of-product-divides-factor
	           (x (* 2 (abs (numerator x))))
                   (y (abs (numerator x)))
                   (z (denominator x)))
		  lemma-1
		  (:instance
                   lemma-2
                   (x (denominator x))
                   (y (* (denominator x)(numerator (* 2 x x))))
		   (z (* 2 (abs (numerator x))(abs (numerator x)))))
		  Nonneg-int-gcd-numerator-denominator)))))

(local
 (defthm lemma-4
   (implies (and (rationalp x)
                 (integerp (* 2 x x)))
            (equal (nonneg-int-mod 2 (denominator x))
                   0))
   :hints (("Goal"
            :in-theory (disable abs)
            :use ((:instance
                   Divisor-of-product-divides-factor
	           (x 2)
                   (y (abs (numerator x)))
                   (z (denominator x)))
		  Nonneg-int-gcd-numerator-denominator)))))

(local
 (defthm lemma-5
   (implies (and (rationalp x)
                 (integerp (* 2 x x)))
            (or (equal (denominator x) 1)
                (equal (denominator x) 2)))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance
                  Divisor-<=
                  (d (denominator x))
                  (n 2))))))

(local
 (defthm lemma-6
   (implies (and (rationalp x)
                 (integerp (* 2 x x))
                 (equal (denominator x) 2))
            (equal (* (abs (numerator x))(abs (numerator x)))
                   (* 2 (numerator (* 2 x x)))))
   :hints (("Goal"
            :in-theory (disable abs)
            :use lemma-1)))) 

(local
 (defthm lemma-7
   (implies (and (rationalp x)
                 (integerp (* 2 x x))
                 (equal (denominator x) 2))
            (equal (nonneg-int-mod (* (abs (numerator x))(abs (numerator x)))
                                   2)
                   0))
   :hints (("Goal"
            :in-theory (disable abs)
            :use (:instance
                  lemma-2
                  (x 2)
                  (y (numerator (* 2 x x)))
                  (z (* (abs (numerator x))(abs (numerator x)))))))))

(local
 (defthm lemma-8
   (implies (and (rationalp x)
                 (integerp (* 2 x x))
                 (equal (denominator x) 2))
            (equal (nonneg-int-mod (abs (numerator x))
                                   2)
                   0))
   :hints (("Goal"
            :use ((:instance
                   Divisor-of-product-divides-factor
                   (x (abs (numerator x)))
                   (y (abs (numerator x)))
                   (z (denominator x)))
                  Nonneg-int-gcd-numerator-denominator
                  lemma-7)))))

(defthm x-2xx
  (implies (and (rationalp x)
		(integerp (* 2 x x)))
	   (integerp x))
  :hints (("Goal"
	   :in-theory (disable abs)
	   :use (lemma-5
		 Nonneg-int-gcd-numerator-denominator)))
  :rule-classes ())
