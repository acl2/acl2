; Area of a Circle
; Application of Integration by Substitution
;
; Copyright (C) 2021 University of Wyoming
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "area-of-a-circle-1")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun f-sine (x)
  (if (realp x)
      (acl2-sine x)
    0)
  )

(defun f2-x (x)
  (if (realp x)
      (* 2 x)
    0)
  )

(defun f2-range() (interval 0 (acl2-pi)))

(local
 (defthm-std standard-f2-range
   (standardp (f2-range))))

(local
 (defthm-std standard-f2-range-left-endpoint
   (standardp (interval-left-endpoint (f2-range)))))

(local
 (defthm-std standard-f2-range-right-endpoint
   (standardp (interval-right-endpoint (f2-range)))))

(defthmd intervalp-f2-range
  (interval-p (f2-range))
  )

(defthmd f2-range-real
  (implies (inside-interval-p x (f2-range))
	   (realp x)))

(defthmd f2-range-non-trivial
  (or (null (interval-left-endpoint (f2-range)))
      (null (interval-right-endpoint (f2-range)))
      (< (interval-left-endpoint (f2-range))
	 (interval-right-endpoint (f2-range)))))

(defthmd f-sine-real
  (realp (f-sine x)))

(defthmd f2-x--real
  (realp (f2-x x)))

(defthmd f2-range-in-domain-of-f-sine
  (implies (inside-interval-p x (fi-domain))
	   (inside-interval-p (f2-x x) (f2-range)))
  :hints (("Goal"
	   :use ((:instance acl2-pi-type-prescription)
		 (:instance pi-between-2-4)
		 (:instance fi-domain-real))
	   :in-theory (enable interval-definition-theory)
	   ))
  )

(defthm-std f-sine-std
  (implies (standardp x)
	   (standardp (f-sine x)))
  )

(local (defthm-std acl2-cosine-std
	 (implies (standardp x)
		  (standardp (acl2-cosine x)))
	 ))

(defthmd f-sine-differentiable
  (implies (and (standardp x)
		(inside-interval-p x (f2-range))
		(inside-interval-p y1 (f2-range))
		(inside-interval-p y2 (f2-range))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2))
		)
	   (and (i-limited (/ (- (f-sine x) (f-sine y1)) (- x y1)))
		(i-close (/ (- (f-sine x) (f-sine y1)) (- x y1))
			 (/ (- (f-sine x) (f-sine y2)) (- x y2)))
		))
  :hints (("Goal"
	   :use ((:instance f2-range-real)
		 (:instance f2-range-real(x y1))
		 (:instance f2-range-real(x y2))
		 (:instance acl2-sine-derivative(x x)
			    (y y1))
		 (:instance standards-are-limited-forward (x (acl2-cosine x)))
		 (:instance i-close-limited-2
			    (y (acl2-cosine x))
			    (x (/ (- (f-sine x) (f-sine y1)) (- x y1))))
		 (:instance acl2-sine)
		 (:instance acl2-cosine)
		 (:instance f-sine-std)
		 (:instance f-sine)
		 (:instance f-sine (x y1))
		 (:instance f-sine (x y2))
		 (:instance acl2-cosine-std)
		 (:instance acl2-sine-derivative(x x)
			    (y y2))
		 (:instance i-close-transitive
			    (x (/ (- (f-sine x) (f-sine y1)) (- x y1)))
			    (y (acl2-cosine x))
			    (z (/ (- (f-sine x) (f-sine y2)) (- x y2)))
			    )
		 (:instance i-close-symmetric
			    (x (/ (- (f-sine x) (f-sine y2)) (- x y2)))
			    (y (acl2-cosine x))
			    )
		 )
	   :in-theory nil
	   ))

  )

(local
 (defthm lemma-23
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= x y)))
	    (not (= (- x y) 0))
	    )
   )
 )

(encapsulate
 nil

 (local (in-theory nil))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (include-book "nonstd/nsa/nsa" :dir :system))

 (local (defthm f2-x-def
	  (implies (realp x)
		   (equal (f2-x x) (* 2 x)))
	  :hints (("Goal"
		   :use (:instance f2-x (x x))
		   ))
	  ))
 (local
  (defthm lemma-21
    (equal (- (* 2 x)  (* 2 y)) (* 2 (- x y)))
    )
  )

 (local
  (defthm f2-x-diff-lemma
    (implies (and (realp x)
		  (realp y1)
		  (not (= (- x y1) 0)))
	     (equal (/ (- (f2-x x) (f2-x y1)) (- x y1)) (/ (* 2 (- x y1)) (- x y1))))
    :hints (("Goal"
	     :use (
		   (:instance F2-X-def(x x))
		   (:instance f2-x (x y1))
		   (:instance lemma-21
			      (x x)
			      (y y1)
			      )
		   )
	     :in-theory nil
	     ))

    ))

 (local
  (defthm lemma-22
    (implies (and (acl2-numberp x)
		  (not (= x 0)))
	     (equal (/ (* 2 x) x) 2)
	     )
    )
  )

 (local
  (defthm f2-x-differentiable-lemma
    (implies (and (standardp x)
		  (inside-interval-p x (fi-domain))
		  (inside-interval-p y1 (fi-domain))
		  (i-close x y1) (not (= x y1))
		  (not (= (- x y1) 0))
		  )
	     (equal (/ (- (f2-x x) (f2-x y1)) (- x y1)) 2)
	     )
    :hints (("Goal"
	     :use (
		   (:instance f2-x-diff-lemma)
		   (:instance fi-domain-real (x y1))
		   (:instance fi-domain-real (x x))
		   (:instance lemma-22 (x (- x y1)))
		   )
	     :in-theory nil
	     )
	    )
    )
  )

 (defthmd f2-x-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (fi-domain))
		 (inside-interval-p y1 (fi-domain))
		 (inside-interval-p y2 (fi-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and  (i-limited (/ (- (f2-x x) (f2-x y1)) (- x y1)))
		  (i-close (/ (- (f2-x x) (f2-x y1)) (- x y1))
			   (/ (- (f2-x x) (f2-x y2)) (- x y2)))))
   :hints (("Goal"
	    :use (
		  (:instance f2-x-differentiable-lemma
			     (x x)
			     (y1 y1))
		  (:instance f2-x-differentiable-lemma
			     (x x)
			     (y1 y2))
		  (:instance lemma-23
			     (x x)
			     (y y1))
		  (:instance lemma-23
			     (x x)
			     (y y2))
		  (:instance fi-domain-real (x y1))
		  (:instance fi-domain-real (x x))
		  (:instance fi-domain-real (x y2))
		  (:instance standard-numberp-integers-to-100000000
			     (x 2))
		  (:instance standards-are-limited-forward (x 2))
		  (:instance i-close-reflexive (x 2))
		  )
	    ))
   )

 )

(encapsulate

 ( ((differential-f-sine * *) => *) )

 (local (in-theory nil))
 (local
  (defun differential-f-sine (x eps)
    (/ (- (f-sine (+ x eps)) (f-sine x)) eps)))

 (defthm differential-f-sine-definition
   (implies (and (inside-interval-p x (f2-range))
                 (inside-interval-p (+ x eps) (f2-range)))
            (equal (differential-f-sine x eps)
                   (/ (- (f-sine (+ x eps)) (f-sine x)) eps))))

 )

(defthmd realp-differential-f-sine
  (implies (and (inside-interval-p x (f2-range))
		(inside-interval-p (+ x eps) (f2-range))
		(realp eps))
	   (realp (differential-f-sine x eps)))
  :hints (("Goal"
	   :use (:functional-instance realp-differential-cr-fn1
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (cr-fn2 f2-x))
	   )
	  ("Subgoal 5"
	   :use (:instance f2-range-in-domain-of-f-sine)
	   )
	  ("Subgoal 6"
	   :use (:instance f-sine-differentiable)
	   )
	  ("Subgoal 7"
	   :use (:instance f2-x-differentiable)
	   )
	  )

  )

(defthm differential-f-sine-limited
  (implies (and (standardp x)
		(inside-interval-p x (f2-range))
		(inside-interval-p (+ x eps) (f2-range))
		(i-small eps))
	   (i-limited (differential-f-sine x eps)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn1-limited
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (cr-fn2 f2-x)))))

(in-theory (disable differential-f-sine-definition))

(encapsulate

 ( ((derivative-f-sine *) => *) )

 (local
  (defun-std derivative-f-sine (x)
    (if (inside-interval-p x (f2-range))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (f2-range))
            (standard-part (differential-f-sine x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (f2-range))
	      (standard-part (differential-f-sine x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-f-sine-definition
   (implies (and (inside-interval-p x (f2-range))
                 (standardp x))
            (equal (derivative-f-sine x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (f2-range))
                       (standard-part (differential-f-sine x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (f2-range))
                         (standard-part (differential-f-sine x (- (/ (i-large-integer)))))
                       'error))))

   :hints (("Goal"
	    :use (:functional-instance derivative-cr-fn1-definition
				       (differential-cr-fn1 differential-f-sine)
				       (cr-fn1 f-sine)
				       (cr-fn2-range f2-range)
				       (cr-fn2-domain fi-domain)
				       (derivative-cr-fn1 derivative-f-sine)
				       (cr-fn2 f2-x)))))


 )

(encapsulate

 ( ((differential-cr-f2 * *) => *) )

 (local
  (defun differential-cr-f2 (x eps)
    (/ (- (f2-x (+ x eps)) (f2-x x)) eps)))

 (defthm differential-cr-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (inside-interval-p (+ x eps) (fi-domain)))
            (equal (differential-cr-f2 x eps)
                   (/ (- (f2-x (+ x eps)) (f2-x x)) eps)))))


(defthmd realp-differential-cr-f2
  (implies (and (inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain))
		(realp eps))
	   (realp (differential-cr-f2 x eps)))
  :hints (("Goal"
	   :use (:functional-instance realp-differential-cr-fn2
				      (differential-cr-fn2 differential-cr-f2)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn1 derivative-f-sine)
				      (cr-fn2 f2-x))
	   )
	  ))

(defthm differential-cr-f2-limited
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain))
		(i-small eps))
	   (i-limited (differential-cr-f2 x eps)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn2-limited
				      (differential-cr-fn2 differential-cr-f2)
				      (cr-fn1 f-sine)
				      (cr-fn2-range f2-range)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn1 derivative-f-sine)
				      (cr-fn2 f2-x))
	   )
	  ))


(in-theory (disable differential-cr-f2-definition))

(encapsulate
 ( ((derivative-cr-f2 *) => *) )

 (local
  (defun-std derivative-cr-f2 (x)
    (if (inside-interval-p x (fi-domain))
        (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-domain))
            (standard-part (differential-cr-f2 x (/ (i-large-integer))))
	  (if (inside-interval-p (- x (/ (i-large-integer))) (fi-domain))
	      (standard-part (differential-cr-f2 x (- (/ (i-large-integer)))))
            'error))
      'error)))

 (defthm derivative-cr-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (standardp x))
            (equal (derivative-cr-f2 x)
                   (if (inside-interval-p (+ x (/ (i-large-integer))) (fi-domain))
                       (standard-part (differential-cr-f2 x (/ (i-large-integer))))
                     (if (inside-interval-p (- x (/ (i-large-integer))) (fi-domain))
                         (standard-part (differential-cr-f2 x (- (/ (i-large-integer)))))
                       'error)))))
 )


(encapsulate
 ( ((f-sine-o-f2 *) => *) )

 (local
  (defun f-sine-o-f2 (x)
    (f-sine (f2-x x))))

 (defthm f-sine-o-f2-definition
   (implies (inside-interval-p x (fi-domain))
            (equal (f-sine-o-f2 x)
                   (f-sine (f2-x x)))))
 )

(encapsulate
 ( ((differential-f-sine-o-f2 * *) => *) )

 (local
  (defun differential-f-sine-o-f2 (x eps)
    (if (equal (f2-x (+ x eps)) (f2-x x))
        0
      (* (differential-f-sine (f2-x x) (- (f2-x (+ x eps)) (f2-x x)))
	 (differential-cr-f2 x eps)))))

 (defthm differential-f-sine-o-f2-definition
   (implies (and (inside-interval-p x (fi-domain))
                 (inside-interval-p (+ x eps) (fi-domain)))
            (equal (differential-f-sine-o-f2 x eps)
                   (if (equal (f2-x (+ x eps)) (f2-x x))
                       0
                     (* (differential-f-sine (f2-x x) (- (f2-x (+ x eps)) (f2-x x)))
                        (differential-cr-f2 x eps))))))
 )

(encapsulate
 ( ((derivative-f-sine-o-f2 *) => *) )

 (local
  (defun derivative-f-sine-o-f2 (x)
    (* (derivative-f-sine (f2-x x))
       (derivative-cr-f2 x))))

 (defthm derivative-f-sine-o-f2-definition
   (implies (inside-interval-p x (fi-domain))
            (equal (derivative-f-sine-o-f2 x)
                   (* (derivative-f-sine (f2-x x))
                      (derivative-cr-f2 x)))))
 )


(defthmd differential-f-sine-o-f2-close
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(realp eps) (i-small eps) (not (= eps 0))
		(inside-interval-p (+ x eps) (fi-domain))
		(syntaxp (not (equal eps (/ (i-large-integer))))))
	   (equal (standard-part (differential-f-sine-o-f2 x eps))
		  (derivative-f-sine-o-f2 x)))
  :hints (("Goal"
	   :use (:functional-instance differential-cr-fn1-o-fn2-close
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range)
				      )


	   )))

; Matt K. addition to speed up proofs:
(local (deftheory slow-rules-1 '((:REWRITE SMALL-IF-<-SMALL)
                                 (:DEFINITION I-LARGE)
                                 (:REWRITE I-CLOSE-LIMITED-2)
                                 (:REWRITE DEFAULT-<-1)
                                 (:REWRITE STANDARD-PART-OF-TIMES)
                                 (:REWRITE REALP-DIFFERENTIAL-RDFN2))))

(defthmd differential-f-sine-std-equals
  (implies (and
	    (standardp x)
	    (inside-interval-p x (f2-range))
	    (inside-interval-p (+ x eps) (f2-range))
	    (i-small eps)
	    (not (= eps 0)))
	   (equal (standard-part (differential-f-sine x eps)) (acl2-cosine x))
	   )
  :hints(("Goal"
	  :use ((:instance acl2-sine-derivative
			   (x x)
			   (y (+ x eps)))

		(:instance f2-range-real)
		(:instance f2-range-real(x (+ x eps)))
		(:instance i-close (x x)
			   (y (+ x eps))
			   )
		(:instance differential-f-sine-definition)
		)
	  :in-theory (e/d (nsa-theory)
; Matt K. addition to speed up proofs:
                          (slow-rules-1))
	  ))
  )

(defthmd differential-cr-f2-equals
  (implies (and (standardp x)
		(i-small eps)
		(not (= eps 0))
		(inside-interval-p x (fi-domain))
		(inside-interval-p (+ x eps) (fi-domain)))
	   (equal (differential-cr-f2 x eps) 2)
	   )
  :hints (("Goal"
	   :use (:instance differential-cr-f2-definition)
	   ))
  )

(local
 (defthm lemma-101
   (implies (and (realp eps)
		 (i-small eps))
	    (< eps 1))
   :hints (("Goal"
	    :use ((:instance i-small (x eps))
		  (:instance standard-part-<-2
			     (x eps)
			     (y 1)))
	    ))
   )
 )

(local
 (defthm lemma-102
   (implies (and (realp x)
		 (realp eps)
		 (< x eps)
		 (< 0 eps)
		 (<= 0 x))
	    (< (abs x) (abs eps)))
   )
 )

(local
 (defthm lemma-103
   (implies (and (realp x)
		 (realp eps)
		 (< (- x eps) 0))
	    (< x eps))
   )
 )

(local
 (defthm lemma-104
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (i-small (+ eps x)))
   :hints (("Goal"
	    :use ((:instance lemma-103)
		  (:instance lemma-102)
		  (:instance small-if-<-small
			     (x eps)
			     (y x))
		  (:instance i-small-plus
			     (x eps)
			     (y x))
		  )))
   )
 )

(local
 (defthm lemma-105
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) 1))
   :hints (("Goal"
	    :use ((:instance lemma-104)
		  (:instance lemma-101 (eps (+ eps x)))
		  (:instance pi-between-2-4)
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-106
   (implies (and (<= x y)
		 (< z x)
		 (< p z))
	    (< p y))
   )
 )


(local
 (defthm lemma-107
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) (acl2-pi)))
   :hints (("Goal"
	    :use ((:instance lemma-105)
		  (:instance pi-between-2-4)
		  (:instance lemma-106
			     (x 2)
			     (y (acl2-pi))
			     (z 1)
			     (p (+ eps x)))
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-108
   (equal (car (f2-range)) 0)
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(local
 (defthm lemma-109
   (equal (cdr (f2-range)) (acl2-pi))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "area-of-a-circle-1"))
 (defthmd x-in-interval-implies-x+-eps-in-interval-f2-range
   (implies (and (inside-interval-p x (f2-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (f2-range))
		(inside-interval-p (- x eps) (f2-range))))
   :hints (("Goal"
	    :use ((:instance lemma-101)
		  (:instance pi-between-2-4)
		  (:instance lemma-107)
		  (:instance f2-range)
		  (:instance lemma-108)
		  (:instance lemma-109)
		  )
	    :in-theory (enable interval-definition-theory)
	    )))
 )

(defthmd derivative-f-sine-equals
  (implies (and (inside-interval-p x (f2-range))
		(standardp x)
		)
	   (equal (derivative-f-sine x) (acl2-cosine x))
	   )
  :hints (("Goal"
	   :use (
		 (:instance derivative-f-sine-definition)
		 (:instance x-in-interval-implies-x+-eps-in-interval-f2-range
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-f-sine-std-equals
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-f-sine-std-equals
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 )
	   ))
  )

(local
 (defthm lemma-110
   (implies (<= x y)
	    (<= (* 1/2 x) (* 1/2 y)))
   )
 )

(local
 (defthm lemma-111
   (implies (and (<= x y)
		 (< z x))
	    (< z y))
   )
 )

(local
 (defthm lemma-112
   (implies (and (standardp x)
		 (realp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps)
		 (<= 0 x)
		 (< (- x eps) 0))
	    (< (+ eps x) (* 1/2 (ACL2-PI))))
   :hints (("Goal"
	    :use ((:instance lemma-105)
		  (:instance pi-between-2-4)
		  (:instance lemma-110
			     (x 2)
			     (y (acl2-pi)))
		  (:instance lemma-111
			     (x 1)
			     (y (* 1/2 (ACL2-PI)))
			     (z (+ eps x)))
		  (:instance acl2-pi-type-prescription)
		  )))
   )
 )

(local
 (defthm lemma-113
   (equal (car (fi-domain)) 0)
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(local
 (defthm lemma-114
   (equal (cdr (fi-domain)) (* 1/2 (acl2-pi)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "area-of-a-circle-1"))
 (defthmd x-in-interval-implies-x+-eps-in-interval-fi-dom
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps)
		 (< 0 eps))
	    (or (inside-interval-p (+ x eps) (fi-domain))
		(inside-interval-p (- x eps) (fi-domain))))
   :hints (("Goal"
	    :use ((:instance lemma-112)
		  (:instance lemma-113)
		  (:instance lemma-114))
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(defthmd derivative-cr-f2-equals
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		)
	   (equal (derivative-cr-f2 x) 2)
	   )
  :hints (("Goal"
	   :use (
		 (:instance derivative-cr-f2-definition)
		 (:instance x-in-interval-implies-x+-eps-in-interval-fi-dom
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-cr-f2-equals
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-cr-f2-equals
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 )
	   ))
  )


(defthmd differential-f-sine-o-f2-close-1
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(realp eps) (i-small eps) (not (= eps 0))
		(inside-interval-p (+ x eps) (fi-domain)))
	   (equal (standard-part (differential-f-sine-o-f2 x eps))
		  (* 2 (acl2-cosine (* 2 x)))))
  :hints (("Goal"
	   :use (
		 (:instance differential-f-sine-o-f2-close)
		 (:instance derivative-cr-f2-equals)
		 (:instance derivative-f-sine-equals(x (f2-x x)))
		 (:instance derivative-f-sine-o-f2-definition)
		 (:instance f2-range-in-domain-of-f-sine)
		 )
	   ))
  )

(local
 (defthm lemma-24
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (= (standard-part x) y))
	    (i-close x y)
	    )
   :hints (("Goal"
	    :in-theory (enable nsa-theory)
	    ))
   )
 )

(defthmd differential-f-sine-o-f2-derivative
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(realp eps) (i-small eps) (not (= eps 0))
		(inside-interval-p (+ x eps) (fi-domain)))
	   (i-close  (/ (- (acl2-sine (* 2 (+ x eps))) (acl2-sine (* 2 x))) eps) (* 2 (acl2-cosine (* 2 x)))))
  :hints (
	  ("Goal"
	   :use ((:instance differential-f-sine-o-f2-close-1)
		 )

	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal'"
	   :use (:functional-instance realp-differential-cr-fn1-o-fn2
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range))
	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal''"
	   :use (
		 (:instance lemma-24
		 	    (x (differential-f-sine-o-f2 x eps))
		 	    (y (* 2 (acl2-cosine (* 2 x)))))
		 )
	   :in-theory (disable differential-f-sine-o-f2-definition fi-domain f-sine-o-f2-definition COSINE-2X)
	   )
	  ("Goal'''"
	   :use (:functional-instance expand-differential-cr-fn1-o-fn2
				      (derivative-cr-fn1-o-fn2 derivative-f-sine-o-f2)
				      (differential-cr-fn1-o-fn2 differential-f-sine-o-f2)
				      (cr-fn1-o-fn2 f-sine-o-f2)
				      (cr-fn2-domain fi-domain)
				      (derivative-cr-fn2 derivative-cr-f2)
				      (differential-cr-fn2 differential-cr-f2)
				      (derivative-cr-fn1 derivative-f-sine)
				      (differential-cr-fn1 differential-f-sine)
				      (cr-fn1 f-sine)
				      (cr-fn2 f2-x)
				      (cr-fn2-range f2-range))
	   :in-theory nil
	   )
	  ("Subgoal 1"
	   :use (:instance f-sine-o-f2-definition)
	   )
	  ("Goal'4'"
	   :use ((:instance f-sine-o-f2-definition(x x) )
		 (:instance f-sine-o-f2-definition(x (+ x eps)))
		 (:instance f-sine (x (f2-x (+ x eps))))
		 (:instance f2-x (x (+ x eps)))
		 (:instance f-sine (x (f2-x x)))
		 (:instance f2-x (x x))
		 (:instance f2-range-in-domain-of-f-sine (x x))
		 (:instance f2-range-in-domain-of-f-sine (x (+ x eps)))
		 (:instance f2-range-real)
		 (:instance fi-domain-real)
		 )
	   )
	  ("Subgoal 2"
	   :use ((:instance f-sine-o-f2-definition(x x) )
		 (:instance f-sine-o-f2-definition(x (+ x eps)))
		 (:instance f-sine (x (f2-x (+ x eps))))
		 (:instance f2-x (x (+ x eps)))
		 (:instance f-sine (x (f2-x x)))
		 (:instance f2-x (x x))
		 (:instance f2-range-in-domain-of-f-sine (x x))
		 (:instance f2-range-in-domain-of-f-sine (x (+ x eps)))
		 (:instance f2-range-real)
		 (:instance fi-domain-real)
		 ))

	  )
  )

; Matt K. addition to speed up proofs:
(local (deftheory slow-rules-2 '(I-CLOSE-LARGE-2
                                 LIMITED-SQUEEZE
                                 LARGE-IF->-LARGE
                                 STANDARD-PART-OF-UMINUS
                                 LEMMA-103
                                 SQRT-EPSILON-DELTA
                                 I-CLOSE-SYMMETRIC
                                 STANDARD-PART-OF-TIMES
                                 STANDARD-PART-OF-PLUS
                                 LEMMA-24
                                 )))

(encapsulate
 nil
 (local (include-book "arithmetic/equalities" :dir :system))

 (local
  (defthm lemma-1-1
    (implies (and (acl2-numberp a)
		  (acl2-numberp b))
	     (equal (* -1 (- a b))
		    (- b a)
		    ))

    )
  )

 (local
  (defthm lemma-1-2
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  (acl2-numberp d))
	     (equal (/ (* -1 (- a b)) (* -1 (- c d)))
		    (/ (- b a) (- d c)))
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1-1)
		   (:instance lemma-1-1 (a c) (b d)))
	     :in-theory nil
	     ))
    )
  )

 (local
  (defthm lemma-1-3
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (acl2-numberp c)
		  (acl2-numberp d))
	     (equal (* (/ a b) (/ c d))
		    (/ (* a c) (* b d))))
    )
  )

 (local
  (defthm lemma-1
    (implies (and
	      (acl2-numberp a)
	      (acl2-numberp b)
	      (acl2-numberp c)
	      (acl2-numberp d))
	     (equal (/ (- a b) (- c d))
		    (/ (- b a) (- d c))
		    )
	     )
    :hints (("Goal"
	     :use ((:instance lemma-1-3
			      (a -1) (b -1) (c (- a b)) (d (- c d)))
		   (:instance lemma-1-2))

	     ))
    )
  )

 (defthmd differential-f-sine-o-f2-derivative-1
   (implies (and (inside-interval-p x (fi-domain))
		 (standardp x)
		 (i-close x x1)
		 (not (= x x1))
		 (inside-interval-p x1 (fi-domain)))
	    (i-close  (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (* 2 (acl2-cosine (* 2 x)))))
   :hints (("Goal"
            :in-theory (disable slow-rules-2) ; Matt K. addition to speed up proofs:
	    :use (:instance differential-f-sine-o-f2-derivative
			    (x x)
			    (eps (- x1 x))
			    )
	    )
	   ("Subgoal 2"
	    :in-theory (e/d (nsa-theory)
                            (slow-rules-2) ; Matt K. addition to speed up proofs:
                            )
	    )
	   ("Subgoal 1"
	    :use (:instance lemma-1
			    (a (acl2-sine (* 2 x1))) (b (acl2-sine (* 2 x)))
			    (c x1) (d x))
	    )
	   )
   )
 )



(local
 (defthm lemma-25
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= y 0))
		 (= x y))
	    (i-close (/ (* 2 x) y) 2)
	    )

   )
 )

(local
 (defthm lemma-26
   (implies (and (acl2-numberp x)
		 (acl2-numberp y))
	    (= (* 2 (- x y)) (- (* 2 x) (* 2 y) ))
	    )
   )
 )

(local
 (defthm lemma-27
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (not (= x y)))
	    (not (= (- x y) 0))
	    )

   )
 )

(defthmd differential-f2-x
  (implies (and (inside-interval-p x (fi-domain))
		(standardp x)
		(i-close x x1)
		(not (= x x1))
		(inside-interval-p x1 (fi-domain)))
	   (i-close (/ (- (* 2 x) (* 2 x1)) (- x x1)) 2))
  :hints (("Goal"
	   :use ((:instance i-close-reflexive (x 2))
		 (:instance fi-domain-real (x x))
		 (:instance fi-domain-real (x x1))
		 (:instance lemma-25 (x (- x x1))
			    (y (- x x1))
			    )
		 (:instance lemma-26 (x x)
			    (y x1)
			    )
		 (:instance lemma-27 (x x)
			    (y x1)
			    )
		 )
	   :in-theory nil
	   ))
  )

(local
 (defthm lemma-5
   (implies (inside-interval-p x (fi-domain))
	    (>= (acl2-cosine x) 0))
   :hints (("Goal"
	    :use ((:instance acl2-pi-type-prescription)
		  (:instance cosine-positive-in-0-pi/2)
		  (:instance cosine-pi/2)
		  (:instance acl2-cos-0-=-1))
	    :in-theory (e/d (interval-definition-theory)
                            (slow-rules-2) ; Matt K. addition to speed up proofs:
                            )
	    ))))

(local
 (defthm lemma-6
   (implies (inside-interval-p x (fi-domain))
	    (equal (circle-sub-prime x) (*  (* (rad) (acl2-cosine x)) (* (rad) (acl2-cosine x)))))
   :hints (("Goal"
	    :use ((:instance circle-sub-prime-equals)
		  (:instance cosine-positive-in-0-pi/2)
		  (:instance cosine-pi/2)
		  (:instance acl2-cos-0-=-1)
		  (:instance lemma-5))
	    :in-theory (enable interval-definition-theory)
	    ))))

(defun rcdfn-f (x)
  (if (realp x)
      (* (rad) (rad) (/ 4) (* (+ (acl2-sine (* 2 x)) (* 2 x))))
    0)
  )

(defthmd rcdfn-f-real
  (realp (rcdfn-f x))
  )

(defthm-std rcdfn-f-std
  (implies (standardp x)
	   (standardp (rcdfn-f x)))
  )

(local
 (defthm lemma-28
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y)))
	    (i-close x y))
   :hints (("Goal"
	    :in-theory (enable nsa-theory)
	    ))
   )
 )

(local
 (defthm lemma-29
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (acl2-numberp z)
		 (i-limited z)
		 (i-close x y))
	    (i-close (* x z) (* y z)))
   :hints (("Goal"
	    :use (
		  (:instance i-close (x x) (y y))
		  (:instance small*limited->small (x (- x y)) (y z))
		  (:instance lemma-28 (x (* x z)) (y (* y z)))
		  )
	    ))
   )
 )

(local
 (defthm lemma-30
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp c)
		 (acl2-numberp d))
	    (equal (+ (- a b) (- c d))
		   (- (+ a c) (+ b d)))
	    )
   )
 )

(local
 (defthm lemma-31
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (acl2-numberp c))
	    (equal (+ (/ a c) (/ b c))
		   (/ (+ a b) c))
	    )
   )
 )

; Matt K. addition to speed up proofs:
(local (deftheory slow-rules-3 '((:LINEAR SQRT-EPSILON-DELTA)
                                 (:REWRITE LEMMA-103)
                                 (:REWRITE 0-<-*)
                                 (:REWRITE LEMMA-24)
                                 (:REWRITE I-CLOSE-LARGE-2)
                                 (:REWRITE <-MINUS-ZERO)
                                 (:REWRITE NON-STANDARD-BETWEEN-STANDARDS-2)
                                 (:REWRITE NON-STANDARD-BETWEEN-STANDARDS)
                                 (:REWRITE COSINE-POSITIVE-IN-3PI/2-2PI)
                                 (:LINEAR INTERVAL-LEFT-<=-RIGHT)
                                 (:REWRITE COSINE-POSITIVE-IN-0-PI/2))))

(defthmd circle-sub-prime-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(inside-interval-p x1 (fi-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (rcdfn-f x) (rcdfn-f x1)) (- x x1))
		    (circle-sub-prime x)))
  :hints (("Goal"
	   :use ((:instance differential-f-sine-o-f2-derivative-1)
		 (:instance lemma-6)
		 (:instance differential-f2-x)
		 (:instance i-close
			    (x  (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)))
			    (y (* 2 (acl2-cosine (* 2 x))))
			    )
		 (:instance i-close
			    (x (/ (- (* 2 x) (* 2 x1)) (- x x1)))
			    (y 2)
			    )
		 (:instance i-small-plus
			    (x (- (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (* 2 (acl2-cosine (* 2 x)))))
			    (y (- (/ (- (* 2 x) (* 2 x1)) (- x x1)) 2))
			    )
		 (:instance lemma-30
			    (a (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)))
			    (b (* 2 (acl2-cosine (* 2 x))))
			    (c (/ (- (* 2 x) (* 2 x1)) (- x x1)))
			    (d 2)
			    )
		 (:instance lemma-28
			    (x (+ (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (/ (- (* 2 x) (* 2 x1)) (- x x1))))
			    (y (+ (* 2 (acl2-cosine (* 2 x))) 2))
			    )
		 (:instance lemma-31
		 	    (a (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))))
		 	    (b (/ (- (* 2 x) (* 2 x1))))
		 	    (c (- x x1))
		 	    )
		 (:instance standards-are-limited-forward (x (rad)))
		 (:instance rad-def)
		 (:instance i-limited-times (x (rad)) (y (rad)))
		 (:instance i-limited-times (x (* (rad) (rad))) (y (/ 4)))
		 (:instance lemma-29
			    (x (+ (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- x x1)) (/ (- (* 2 x) (* 2 x1)) (- x x1))))
			    (y (+ (* 2 (acl2-cosine (* 2 x))) 2))
			    (z (* (rad) (rad) (/ 4)))
			    )
		 (:instance cosine-2x)
		 (:instance cos**2->1-sin**2)
		 (:instance rcdfn-f (x x))
		 (:instance rcdfn-f (x x1))
		 )
           :in-theory (disable slow-rules-3) ; Matt K. addition to speed up proofs:
	   ))
  )

(defthmd circle-sub-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (fi-domain))
		(i-close x x1)
		(inside-interval-p x1 (fi-domain)))
	   (i-close (circle-sub-prime x)
		    (circle-sub-prime x1)))
  :hints (("Goal"
	   :use ((:instance cosine-continuous
			    (x x)
			    (y y))
		 (:instance lemma-6)
		 (:instance rad-def)
		 (:instance standards-are-limited-forward(x (rad)))
		 (:instance lemma-29
			    (x (acl2-cosine x))
			    (y (acl2-cosine x1))
			    (z (rad)))
		 (:instance square-is-continuous
			    (x1 (* (rad) (acl2-cosine x)))
			    (x2 (* (rad) (acl2-cosine x1))))
		 )
           :in-theory (disable slow-rules-3) ; Matt K. addition to speed up proofs:
	   ))
  )

(defthmd circle-area-ftc-2
  (implies (and (inside-interval-p a (fi-domain))
		(inside-interval-p b (fi-domain)))
	   (equal (int-circle-sub-prime a b)
		  (- (rcdfn-f b)
		     (rcdfn-f a))))
  :hints (("Goal"
	   :use (:functional-instance ftc-2
				      (rcdfn rcdfn-f)
				      (rcdfn-prime circle-sub-prime)
				      (map-rcdfn-prime map-circle-sub-prime)
				      (riemann-rcdfn-prime riemann-circle-sub-prime)
				      (rcdfn-domain fi-domain)
				      (int-rcdfn-prime int-circle-sub-prime)
				      (strict-int-rcdfn-prime strict-int-circle-sub-prime)
				      )
	   )
	  ("Goal"
	   :use (
		 (:instance circle-sub-prime-continuous)
		 (:instance circle-sub-prime-is-derivative)
		 (:instance intervalp-fi-domain)
		 (:instance fi-domain-non-trivial)
		 (:instance fi-domain-standard)
		 (:instance fi-domain)
		 )
	   )
	  ("Subgoal 9"
	   :use (:instance circle-sub-prime-continuous)
	   )
	  ("Subgoal 8"
	   :use (:instance circle-sub-prime-is-derivative)
	   )
	  )
  )

(defthmd lemma-0-inside
  (inside-interval-p 0 (fi-domain))
  :hints (("Goal"
	   :use ((:instance fi-domain))
	   :in-theory (enable interval-definition-theory)
	   ))
  )

(defthmd lemma-1/2-pi-inside
  (inside-interval-p (* 1/2 (acl2-pi)) (fi-domain))
  :hints (("Goal"
	   :use ((:instance fi-domain)
		 (:instance pi-between-2-4)
		 (:instance acl2-pi-type-prescription)
		 )
	   :in-theory (enable interval-definition-theory)
	   ))
  )

(defthm circle-area
  (equal (* 4 (int-circle-sub-prime 0 (* 1/2 (acl2-pi)))) (* (rad) (rad) (acl2-pi)))
  :hints (("Goal"
	   :use ((:instance circle-area-ftc-2 (a 0)
			    (b (* 1/2 (acl2-pi))))
		 (:instance lemma-0-inside)
		 (:instance lemma-1/2-pi-inside)
		 (:instance acl2-pi-type-prescription)
		 (:instance rcdfn-f (x 0))
		 (:instance rcdfn-f (x (* 1/2 (acl2-pi))))
		 )
	   ))
  )
