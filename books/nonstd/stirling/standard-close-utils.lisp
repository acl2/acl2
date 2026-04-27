(in-package "ACL2")

(local (include-book "nonstd/nsa/nsa" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(defthm standard-part-of-real-is-real
    (implies (realp x)
             (realp (standard-part x)))
  :hints (("Goal"
           :use ((:instance standard-part-of-complex
                            (x x)
                            (y 0))))))

(local
 (defthmd standard-part-is-standard-implies-limited-part1
     (implies (and (realp x)
                   (<= 0 x)
                   (equal (standard-part x) stdx)
                   (standardp stdx))
              (i-limited x))
   :hints (("Goal"
            :use ((:instance standard-part-<=
                             (x (1+ stdx))
                             (y x))
                  (:instance large-if->-large
                             (x x)
                             (y (1+ stdx)))
                  )
            :in-theory (disable large-if->-large
                                standard-part-<=)
            )
           )
   ))

(local
 (defthmd standard-part-is-standard-implies-limited-part2
     (implies (and (realp x)
                   (< x 0)
                   (equal (standard-part x) stdx)
                   (standardp stdx))
              (i-limited x))
   :hints (("Goal"
            :use ((:instance standard-part-is-standard-implies-limited-part1
                             (x (- x))
                             (stdx (- (standard-part x))))
                  )
            :in-theory (disable large-if->-large
                                standard-part-<=)
            )
           )
   ))

(local
 (defthmd standard-part-is-standard-implies-limited-real
     (implies (and (realp x)
                   (equal (standard-part x) stdx)
                   (standardp stdx))
              (i-limited x))
   :hints (("Goal"
            :use ((:instance standard-part-is-standard-implies-limited-part1)
                  (:instance standard-part-is-standard-implies-limited-part2)
                  )
            )
           )
   ))

(defthmd standard-part-is-standard-implies-limited
    (implies (and (acl2-numberp x)
                  (equal (standard-part x) stdx)
                  (standardp stdx))
             (i-limited x))
  :hints (("Goal"
           :cases ((realp x)))
          ("Subgoal 2"
           :use ((:instance complex-limited-1)
                 (:instance standard-part-is-standard-implies-limited-real
                            (x (realpart x))
                            (stdx (realpart stdx)))
                 (:instance standard-part-is-standard-implies-limited-real
                            (x (imagpart x))
                            (stdx (imagpart stdx)))
                 )
           )
          ("Subgoal 1"
           :use ((:instance standard-part-is-standard-implies-limited-real)
                 )
           )
          )
  )

(local
 (defthmd standard-part-is-standard-implies-close-to-standard-part-real
     (implies (and (realp x)
                   (equal (standard-part x) stdx)
                   (standardp stdx))
              (i-close x stdx))
   :hints (("Goal"
            :use ((:instance standard-part-is-standard-implies-limited)
                  (:instance standard-part-close))))))

(defthm complex-small-stronger
    (implies (acl2-numberp x)
             (equal (i-small x)
                    (and (i-small (realpart x))
                         (i-small (imagpart x)))))
  :hints (("Goal"
           :use ((:instance complex-small))
           :in-theory (e/d (i-small)
                           (complex-small))))
  :rule-classes nil)

(defthmd complex-uminus
    (IMPLIES (and (realp X)
                  (REALP Y))
             (EQUAL (COMPLEX (- X) (- Y))
                    (- (COMPLEX X Y))))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x x)
                            (y y))
                 (:instance complex-definition
                            (x (- x))
                            (y (- y))))
           )))

(defthmd realpart-uminus
    (IMPLIES (ACL2-NUMBERP X)
             (EQUAL (REALPART (- X))
                    (- (REALPART X))))
  :hints (("Goal"
           :use ((:instance COMPLEX-UMINUS
                            (x (REALPART X))
                            (y (IMAGPART X))))
           )))

(defthmd IMAGPART-uminus
    (IMPLIES (ACL2-NUMBERP X)
             (EQUAL (IMAGPART (- X))
                    (- (IMAGPART X))))
  :hints (("Goal"
           :use ((:instance COMPLEX-UMINUS
                            (x (REALPART X))
                            (y (IMAGPART X))))
           )))

(defthm complex-close
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (i-close x y)
                    (and (i-close (realpart x) (realpart y))
                         (i-close (imagpart x) (imagpart y)))))
  :hints  (("Goal"
            :use ((:instance complex-small-stronger
                             (x (- x y))))
            :in-theory (e/d (i-close
                             REALPART-UMINUS
                             IMAGPART-UMINUS)
                            (complex-small))))
  :rule-classes nil)

(defthmd standard-part-is-standard-implies-close-to-standard-part
     (implies (and (acl2-numberp x)
                   (equal (standard-part x) stdx)
                   (standardp stdx))
              (i-close x stdx))
  :hints (("Goal"
           :cases ((realp x)))
          ("Subgoal 2"
           :use ((:instance complex-limited-1)
                 (:instance standard-part-is-standard-implies-limited-real
                            (x (realpart x))
                            (stdx (realpart stdx)))
                 (:instance standard-part-is-standard-implies-limited-real
                            (x (imagpart x))
                            (stdx (imagpart stdx)))
                 )
           )
          ("Subgoal 1"
           :use ((:instance standard-part-is-standard-implies-limited-real)
                 )
           )
          )
)

(defthmd limited-if-standard-part-close-to-standard
    (implies (and (acl2-numberp x)
                  (i-close (standard-part x) stdx)
                  (acl2-numberp stdx)
                  (standardp stdx))
             (i-limited x))
  :hints (("Goal"
           :use ((:instance close-x-y->same-standard-part
                            (x stdx)
                            (y (standard-part x)))
                 (:instance standard-part-is-standard-implies-limited)
                 )
           )
          )
  )

(defthmd close-standards-are-equal
    (implies (and (standardp x1)
                  (standardp x2)
                  (i-close x1 x2))
             (equal (equal x1 x2) t))
  :hints (("Goal"
           :use ((:instance close-x-y->same-standard-part
                            (x x1)
                            (y x2)))
           :in-theory (e/d (i-close)
                           (close-x-y->same-standard-part)))))

(defthmd close-to-standard-are-close
    (implies (and (acl2-numberp x1)
                  (i-close (standard-part x1) stdx)
                  (acl2-numberp x2)
                  (i-close (standard-part x2) stdx)
                  (acl2-numberp stdx)
                  (standardp stdx))
             (i-close x1 x2))
  :hints (("Goal"
           :use ((:instance standard-part-is-standard-implies-close-to-standard-part
                            (x x1))
                 (:instance standard-part-is-standard-implies-close-to-standard-part
                            (x x2))
                 (:instance limited-if-standard-part-close-to-standard
                            (x x1))
                 (:instance limited-if-standard-part-close-to-standard
                            (x x2))
                 (:instance close-standards-are-equal
                            (x1 (standard-part x1))
                            (x2 stdx))
                 (:instance close-standards-are-equal
                            (x1 (standard-part x2))
                            (x2 stdx))
                 (:instance standardp-standard-part
                            (x x1))
                 (:instance standardp-standard-part
                            (x x2))
                 (:instance i-close-transitive
                            (x x1)
                            (y stdx)
                            (z x2))
                 )
           :in-theory (disable i-close-transitive
                               standardp-standard-part)
           )
          )
  )

(defthmd standard-part-close-to-standard-implies-standard-part-is-that-standard
    (implies (and (acl2-numberp x)
                  (i-close (standard-part x) stdx)
                  (acl2-numberp stdx)
                  (standardp stdx))
             (equal (standard-part x) stdx))
  :hints (("Goal"
           :use ((:instance limited-if-standard-part-close-to-standard)
                 (:instance close-x-y->same-standard-part
                            (x (standard-part x))
                            (y stdx))))))

(defthmd close-to-standard-implies-standard-part-is-that-standard
    (implies (and (acl2-numberp x)
                  (i-close x stdx)
                  (acl2-numberp stdx)
                  (standardp stdx))
             (equal (standard-part x) stdx))
  :hints (("Goal"
           :use ((:instance i-close-limited-2
                            (x x)
                            (y stdx)
                            )
                 (:instance close-x-y->same-standard-part
                            (x x)
                            (y stdx)
                            )))))

(defthm close-times
    (implies (and (i-close x1 x2)
		  (i-limited y))
	     (i-close (* x1 y) (* x2 y)))
  :hints (("Goal"
	   :use ((:instance small*limited->small
			    (x (- x1 x2))
			    (y y)))
           :in-theory (enable i-close)
           )))

(defthm close-times-2
    (implies (and (i-close x1 x2)
		  (i-close y1 y2)
		  (i-limited x1)
		  (i-limited y1))
	     (i-close (* x1 y1) (* x2 y2)))
  :hints (("Goal"
	   :use ((:instance close-times (x1 x1) (x2 x2) (y y1))
		 (:instance close-times (x1 y1) (x2 y2) (y x2))
		 (:instance i-close-transitive
			    (x (* x1 y1))
			    (y (* x2 y1))
			    (z (* x2 y2)))
		 (:instance i-close-limited
			    (x x1)
			    (y x2)))
           )))
