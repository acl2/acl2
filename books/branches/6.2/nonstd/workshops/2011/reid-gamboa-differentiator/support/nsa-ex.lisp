(in-package "ACL2")

(include-book "nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)

(defthm close-uminus
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (i-close (- x) (- y))
                  (i-close x y)))
  :hints (("Goal"
           :use ((:instance i-small-uminus (x (+ x (- y)))))
           :in-theory (enable i-close i-small-uminus))))

(defthm large-not-small
  (implies (i-large x)
           (not (i-small x))))

(defthm prod-of-non-small-is-non-small
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (not (i-small x))
                (not (i-small y)))
           (not (i-small (* x y))))
  :hints (("Goal"
           :use ((:instance standard-part-of-times))
           :in-theory '(i-small))
          ("Subgoal 2"
           :use ((:instance large-not-small (x (* x y)))
                 (:instance large*limited->large (x x) (y y))))
          ("Subgoal 1"
           :use ((:instance large-not-small (x (* x y)))
                 (:instance limited*large->large (x x) (y y))))))
		
(defthm realp-standard-part
  (implies (realp x)
           (realp (standard-part x))))

(encapsulate
 nil
 (local 
  (defthm close-/-lemma-1
    (implies (and (not (i-small x))
		  (i-close x y))
	     (equal (/ (standard-part x)) (/ (standard-part y))))
    :hints (("Goal" :in-theory (enable nsa-theory)))))

 (local
  (defthm close-/-lemma-2
    (implies (and (not (i-small x))
		  (i-close x y)
		  (i-limited x)
                  )
	     (equal (standard-part (/ x)) (standard-part (/ y))))
    :hints (("Goal"
	     :use ((:instance close-/-lemma-1)
		   (:instance standard-part-of-udivide
			      (x y)))))))

 (local
  (defthm close-/-lemma-3
    (implies (and (i-large x)
                  (i-close x y))
             (equal (standard-part (/ x)) (standard-part (/ y))))
    :hints (("Goal" :in-theory (enable i-large i-small)
             :use (:instance i-close-large
                             (x x) (y y))))))
 (defthm close-/
   (implies (and (not (i-small x))
		 (i-close x y))
	    (i-close (/ x) (/ y)))
   :hints (("Goal" 
            :cases ((i-limited x)))
           ("Subgoal 2"
            :use (:instance close-/-lemma-3)
            :in-theory (enable i-close i-small))
           ("Subgoal 1"
            :use (:instance close-/-lemma-2)
            :in-theory (enable i-close i-small)))))



; WTS that is x*x ~= y*y, then x ~= y
(encapsulate
 nil
 (local
  (defthm large-x-lemma
    (implies (and (realp x)
                  (<= 0 x)
                  (i-large x)
                  (realp eps)
                  (< 0 eps)
                  (i-small (- (* (+ x eps) (+ x eps))
                              (* x x))))
             (i-small eps))
    :hints (("Goal" 
             :use ((:instance large->-non-large
                              (x x)
                              (y 1))
                   (:instance <-y-*-x-y
                              (y eps)
                              (x(+ x x eps)))
                   (:instance small-if-<-small
                              (y eps)
                              (x (- (* (+ x eps) (+ x eps))
                                    (* x x)))))
             :in-theory (enable abs)))))
 (local
  (defthm squares-close-large
    (implies (and (realp x) (i-large x) (<= 0 x)
                  (realp y) (<= 0 y)
                  (i-close (* x x) (* y y)))
             (i-close x y))
    :hints (("Goal" :in-theory (enable-disable (i-close) (large-x-lemma))
             :cases ((< x y)
                     (< y x)
                     (= x y)))
            ("Subgoal 3"
             :use ((:instance large-x-lemma
                              (x x)
                              (eps (- y x)))
                   (:instance i-small-uminus (x (- x y)))
                   (:instance i-small-uminus (x (- (* x x) (* y y))))))
            ("Subgoal 2"
             :use ((:instance large-x-lemma
                              (x y)
                              (eps (- x y))))))))

 (local
  (defthm x*x<y*y
    (implies (and (realp x)
                  (realp y)
                  (<= 0 x)
                  (<= 0 y)
                  (< x y))
             (< (* x x) (* y y)))
    :hints (("Goal"
             :cases ((= 0 x)
                     (= 0 y)
                     (and (< 0 x) (< 0 y)))))))

 (local
  (defthm squares-equal
    (implies (and (realp x)
                  (realp y)
                  (<= 0 x)
                  (<= 0 y)
                  (equal (* x x) (* y y)))
             (equal x y))
    :hints (("Goal"
             :cases ((< x y)
                     (< y x)
                     (= x y)))
            ("Subgoal 2" :use (:instance x*x<y*y (x x) (y y)))
            ("Subgoal 1" :use (:instance x*x<y*y (x y) (y x))))
    :rule-classes nil))

 (defthm squares-close
   (implies (and (realp x) (<= 0 x)
                 (realp y) (<= 0 y)
                 (i-close (* x x) (* y y)))
            (i-close x y))
   :hints (("Goal" :cases ((i-large x)
                           (i-large y)
                           (and (i-limited x)
                                (i-limited y))))
           ("Subgoal 2"
            :use ((:instance i-close-symmetric (x y) (y x))))
           ("Subgoal 1"
            :in-theory (enable i-close i-small)
            :use (:instance squares-equal 
                            (x (standard-part x))
                            (y (standard-part y)) )))))

(defthm i-small-*
  (implies (acl2-numberp x)
           (equal (i-small (* x x))
                  (i-small x)))
  :hints (("Goal" 
           :cases ((i-large x)
                   (i-limited x))
           :in-theory (enable i-small))))
