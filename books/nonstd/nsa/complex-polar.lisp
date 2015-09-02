(in-package "ACL2")
(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "inverse-trig")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(defun radiuspart (x)
  (acl2-sqrt (+ (* (realpart x)
                   (realpart x))
                (* (imagpart x)
                   (imagpart x)))))

(defun anglepart (x)
  (if (equal (fix x) 0)
      0
    (let ((angle (acl2-acos (/ (realpart x) (radiuspart x)))))
      (if (< (imagpart x) 0)
          (- (* 2 (acl2-pi)) angle)
        angle))))

(defthm e^ix-cos-i-sin
  (equal (acl2-exp (* #c(0 1) x))
         (+ (acl2-cosine x)
            (* #c(0 1)
               (acl2-sine x))))
  :hints (("Goal"
           :in-theory (enable acl2-sine acl2-cosine)))
  )

(local
 (defthm realp-cosine-inverse
     (implies (and (realp x)
		   (<= -1 x)
		   (<= x 1))
	      (REALP (ACL2-ACOS X)))
   :hints (("Goal"
	    :use ((:instance ACL2-ACOS-EXISTS (y x)))
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm range-of-cosine-inverse
     (implies (and (realp x)
		   (<= -1 x)
		   (<= x 1))
	      (and (<= 0 (acl2-acos x))
		   (<= (acl2-acos x) (acl2-pi))))
   :hints (("Goal"
	    :use ((:instance ACL2-ACOS-EXISTS (y x)))
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:linear :rewrite)
   ))

(local
 (defthm cosine-cosine-inverse
     (implies (and (realp x)
		   (<= -1 x)
		   (<= x 1))
	      (equal (acl2-cosine (acl2-acos x))
		     x))
   :hints (("Goal"
	    :use ((:instance ACL2-ACOS-EXISTS (y x)))
	    :in-theory (enable interval-definition-theory)))))

(encapsulate
 ()
 (local
  (defthm lemma-1
    (implies (and (realp rr)
                  (realp ss)
                  (<= 0 rr)
                  (<= 0 ss))
             (<= (* rr (/ (+ rr ss))) 1))
    :hints (("Goal"
             :use ((:instance <-*-/-right
                              (a 1)
                              (y (+ rr ss))
                              (x rr)))
             :in-theory (disable <-*-/-right)))))
 (local
  (defthm lemma-2
    (implies (and (realp r)
                  (realp s))
             (equal (* r r (/ (acl2-sqrt (+ (* r r) (* s s))))
                       (/ (acl2-sqrt (+ (* r r) (* s s)))))
                    (* r r (/ (+ (* r r) (* s s))))))
    :hints (("Goal"
             :use ((:instance sqrt-sqrt
                              (x (+ (* r r) (* s s))))
                   )
             :in-theory (disable sqrt-sqrt
                                 equal-*-/-2)))))
 (local
  (defthm lemma-3
    (implies (and (realp x)
                  (< 1 x))
             (< 1 (* x x)))
    :hints (("Goal"
             :use ((:instance *-preserves->-for-nonnegatives-1
                              (x1 x)
                              (y1 x)
                              (x2 1)
                              (y2 1)))
             :in-theory (disable *-preserves->-for-nonnegatives-1)))))
 (local
  (defthm lemma-4
    (implies (and (realp r)
                  (realp s))
             (<= (* r
                    (/ (acl2-sqrt (+ (* r r) (* s s)))))
                 1))
    :hints (("Goal"
             :use ((:instance lemma-3
                              (x (* r
                                    (/ (acl2-sqrt (+ (* r r)
                                                     (* s s)))))))
                   (:instance lemma-1
                              (rr (* r r))
                              (ss (* s s))))
             :in-theory (disable lemma-1 lemma-3)))))
 (local
  (defthm lemma-5
    (implies (and (realp r)
                  (realp s))
             (<= -1
                 (* r
                    (/ (acl2-sqrt (+ (* r r) (* s s)))))))
    :hints (("Goal"
             :use ((:instance lemma-4
                              (r (- r))))
             :in-theory (disable lemma-4)))))

 (defthm anglepart-angle-in-domain
   (and (realp (* (REALPART X)
                  (/ (ACL2-SQRT (+ (* (IMAGPART X) (IMAGPART X))
                                   (* (REALPART X) (REALPART X)))))))
        (<= -1 (* (REALPART X)
                  (/ (ACL2-SQRT (+ (* (IMAGPART X) (IMAGPART X))
                                   (* (REALPART X) (REALPART X)))))))
        (<= (* (REALPART X)
               (/ (ACL2-SQRT (+ (* (IMAGPART X) (IMAGPART X))
                                (* (REALPART X) (REALPART X))))))
            1))
   :hints (("Goal" :use ((:instance lemma-4
                                    (r (realpart x))
                                    (s (imagpart x)))
                         (:instance lemma-5
                                    (r (realpart x))
                                    (s (imagpart x))))
            :in-theory (disable lemma-4
                                lemma-5))))
 (defthm realp-inverse-cosine-anglepart-angle
     (realp (acl2-acos (* (REALPART X)
				    (/ (ACL2-SQRT (+ (* (IMAGPART X) (IMAGPART X))
						     (* (REALPART X) (REALPART X))))))))
   :hints (("Goal"
	    :use ((:instance anglepart-angle-in-domain))
	    :in-theory (enable interval-definition-theory))))

 (local
  (defthm lemma-6
    (implies (and (acl2-numberp y)
                  (not (equal 0 y)))
             (equal (* x y (/ y))
                    (fix x)))))
 (local
  (defthm lemma-7
    (implies (and (realp r)
                  (realp s))
             (equal (equal (+ (* r r) (* s s)) 0)
                    (and (equal r 0)
                         (equal s 0))))))
 (local
  (defthm lemma-8
    (implies (and (realp x)
                  (<= 0 x))
             (equal (equal (acl2-sqrt x) 0)
                    (equal x 0)))))
 (local
  (defthm lemma-9
    (implies (and (realp r)
                  (realp s)
                  (not (equal (complex r s) 0)))
             (not (equal (acl2-sqrt (+ (* r r) (* s s))) 0)))))
 (local
  (defthm lemma-10
    (implies (and (realp r)
                  (realp s))
             (equal (* s s (/ (acl2-sqrt (+ (* r r) (* s s))))
                       (/ (acl2-sqrt (+ (* r r) (* s s)))))
                    (* s s (/ (+ (* r r) (* s s))))))
    :hints (("Goal"
             :use ((:instance lemma-2
                              (r s)
                              (s r)))
             :in-theory (disable lemma-2)))))
 (local
  (defthm lemma-11
    (implies (not (equal (fix y) 0))
             (equal (+ 1 (- (* x x (/ y))))
                    (/ (+ y (- (* x x)))
                       y)))))
 (local
  (defthm lemma-12
    (implies (and (realp r)
                  (realp s)
                  (not (equal (complex r s) 0)))
             (equal (* (acl2-sine
                        (acl2-acos
                         (* R (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
                       (acl2-sine
                        (acl2-acos
                         (* R (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
                    (* (* s (/ (ACL2-SQRT (+ (* R R) (* S S)))))
                       (* s (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
    :hints (("Goal"
             :use ((:instance sin**2->1-cos**2
                              (x (acl2-acos
                                  (* R (/ (ACL2-SQRT (+ (* R R) (* S S)))))))))
             :in-theory (disable sin**2->1-cos**2))
            ("Goal'5'"
             :use ((:instance lemma-11
                              (x r)
                              (y (+ (* R R) (* S S)))))
             :in-theory (disable lemma-11)))))
 (local
  (defthm lemma-13
    (implies (and (realp x)
                  (realp y)
                  (equal (* x x) (* y y)))
             (or (equal x y)
                 (equal x (- y))))
    :hints (("Goal"
             :use ((:instance sqrt-*-x-x (x x))
                   (:instance sqrt-*-x-x (x y)))
             :in-theory (enable-disable (abs) (sqrt-*-x-x
                                               sqrt-*
                                               y-=-sqrt
                                               sqrt-=-y))))
    :rule-classes nil))
 (local
  (defthm lemma-14
    (equal (acl2-sine (* 1/2 (acl2-pi))) 1)))
 (local
  (defthm lemma-15
    (implies (and (realp x)
                  (<= -1 x)
                  (<= x 1))
             (<= 0 (acl2-sine (acl2-acos x))))
    :hints (("Goal"
             :use ((:instance sine-positive-in-0-pi/2
                              (x (acl2-acos x)))
                   (:instance sine-positive-in-pi/2-pi
                              (x (acl2-acos x)))
                   ;(:instance acl2-cosine-acl2-acos
                   ;           (y x))
		   )
             :in-theory (disable sine-positive-in-0-pi/2
                                 sine-positive-in-pi/2-pi
                                 ;acl2-cosine-acl2-acos
                                 sine-2x
                                 sine-3x
                                 cosine-2x
				 EQUAL-*-/-1)))))
 (local
  (defthm lemma-16
    (implies (and (realp r)
                  (realp s)
                  (not (equal (complex r s) 0))
                  (<= 0 s))
             (equal (acl2-sine
                     (acl2-acos
                      (* R (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
                    (* s (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
    :hints (("Goal"
             :use ((:instance lemma-12)
                   (:instance lemma-13
                              (x (acl2-sine
                                  (acl2-acos
                                   (* R (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
                              (y (* s (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
                   (:instance lemma-15
                              (x (* R (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
             :in-theory (disable lemma-12 lemma-15)))))
 (local
  (defthm lemma-17
    (implies (and (realp r)
                  (realp s)
                  (< s 0))
             (equal (acl2-sine
                     (acl2-acos
                      (* R (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
                    (- (* s (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
    :hints (("Goal"
             :use ((:instance lemma-12)
                   (:instance lemma-13
                              (x (acl2-sine
                                  (acl2-acos
                                   (* R (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
                              (y (* s (/ (ACL2-SQRT (+ (* R R) (* S S)))))))
                   (:instance lemma-15
                              (x (* R (/ (ACL2-SQRT (+ (* R R) (* S S))))))))
             :in-theory (disable lemma-12 lemma-15)))))
 (local
  (defthm lemma-18
    (implies (and (realp r)
                  (realp s))
             (equal (EQUAL (+ R (* #C(0 1) S))
                           (COMPLEX R S))
                    t))
    :hints (("Goal"
             :use ((:instance complex-definition
                              (x r)
                              (y s)))))))
 (defthm correctness-of-polar-form
   (equal (* (radiuspart x)
             (acl2-exp (* #c(0 1) (anglepart x))))
          (fix x)))
 )

(local
 (defthm zero-imag-real-parts
     (implies (and (realp r)
		   (realp s))
	      (equal (equal (+ (* r r) (* s s)) 0)
		     (and (equal r 0)
			  (equal s 0))))))


(defthm radiuspart-is-non-negative
  (and (realp (radiuspart x))
       (<= 0 (radiuspart x))))

(defthm radiuspart-is-zero-only-for-zero
  (implies (equal (radiuspart x) 0)
           (equal (fix x) 0)))

(defthm radiuspart-of-realp
  (implies (realp x)
           (equal (radiuspart x) (abs x)))
  :hints (("Goal"
           :in-theory (enable abs))))

(encapsulate
 ()
 (local
  (defthm lemma-1
    (implies (and (realp s)
                  (< s 0))
             (not (equal r (acl2-sqrt (+ (* r r) (* s s))))))
    :hints (("Goal"
             :use ((:instance y-=-sqrt
                              (y r)
                              (x (+ (* r r) (* s s)))))
             :in-theory (disable y-=-sqrt)))))
 (local
  (defthm lemma-2
      (implies (and (equal (acl2-acos x) 0)
		    (realp x)
		    (<= -1 x)
		    (<= x 1))
	       (equal x 1))
    :hints (("Goal"
	     :use ((:instance acl2-acos-exists (y x)))
	     :in-theory (enable-disable (interval-definition-theory)
					(acl2-acos-exists acl2-acos-unique))
	     ))
    :rule-classes nil))

 (defthm anglepart-between-0-and-2pi
   (and (realp (anglepart x))
        (<= 0 (anglepart x))
        (< (anglepart x) (* 2 (acl2-pi))))
   :hints (("Goal"
            :use ((:instance anglepart-angle-in-domain)
                  (:instance range-of-cosine-inverse
                             (x (* (realpart x)
                                   (/ (acl2-sqrt (+ (* (imagpart x)
                                                       (imagpart x))
                                                    (* (realpart x)
                                                       (realpart x))))))))
		  (:instance lemma-2
			     (x (* (REALPART X)
				   (/ (ACL2-SQRT (+ (* (IMAGPART X) (IMAGPART X))
						    (* (REALPART X) (REALPART X))))))))
		  )
            :in-theory (disable anglepart-angle-in-domain
				range-of-cosine-inverse))))
   )

(encapsulate
 ()
 (local
  (defthm lemma-1
    (equal (acl2-acos 1) 0)
    :hints (("Goal"
             :use ((:instance acl2-acos-unique
                              (y 1)
                              (x 0)))
	     :in-theory (enable-disable (interval-definition-theory)
					(acl2-acos-unique))
	     ))))
 (local
  (defthm lemma-2
    (equal (acl2-acos -1) (acl2-pi))
    :hints (("Goal"
             :use ((:instance acl2-acos-unique
                              (y -1)
                              (x (acl2-pi))))
	     :in-theory (enable-disable (interval-definition-theory)
					(acl2-acos-unique))))))

 (defthm anglepart-of-realp
  (implies (realp x)
           (equal (anglepart x)
                  (if (<= 0 x)
                      0
                    (acl2-pi))))
  :hints (("Goal"
	   :use ((:instance lemma-1)
		 (:instance lemma-2))
           :in-theory (enable-disable (abs) (lemma-1 lemma-2)))))
 )
