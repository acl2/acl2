(in-package "ACL2")

(local (include-book "ftc-2"))
(local (include-book "nonstd/nsa/continuity-product" :dir :system))
(local (include-book "nonstd/nsa/derivatives" :dir :system))
(local (include-book "nonstd/nsa/derivatives-composition" :dir :system))
(local (include-book "nonstd/integrals/continuous-function" :dir :system))
(local (include-book "nonstd/integrals/integration-composition" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/intervals" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)

(encapsulate
 ( ((bpfn-u * *) => *)
   ((bpfn-u-prime * *) => *)
   ((bpfn-v * *) => *)
   ((bpfn-v-prime * *) => *)
   ((bpfn-domain) => *)
   ((bpfn-car-context *) => *)
   ((bpfn-cdr-context *) => *)
   )

   (local (defun bpfn-u (contextu x) (declare (ignore contextu x)) 0))
   (local (defun bpfn-u-prime (contextu x) (declare (ignore contextu x)) 0))
   (local (defun bpfn-v (contextv x) (declare (ignore contextv x)) 0))
   (local (defun bpfn-v-prime (contextv x) (declare (ignore contextv x)) 0))
   (local (defun bpfn-domain () (interval 0 1)))

   (local (defun bpfn-car-context (context) (car context)))
   (local (defun bpfn-cdr-context (context) (cdr context)))

   (defthm intervalp-bpfn-domain
     (interval-p (bpfn-domain))
   :rule-classes (:type-prescription :rewrite))

   (defthm bpfn-domain-real
     (implies (inside-interval-p x (bpfn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

   (defthm bpfn-domain-non-trivial
     (or (null (interval-left-endpoint (bpfn-domain)))
	 (null (interval-right-endpoint (bpfn-domain)))
	 (< (interval-left-endpoint (bpfn-domain))
	    (interval-right-endpoint (bpfn-domain))))
     :rule-classes nil)

   (defthm bpfn-u-real
     (realp (bpfn-u contextu x))
   :rule-classes (:rewrite :type-prescription))

   (defthm bpfn-v-real
     (realp (bpfn-v contextv x))
   :rule-classes (:rewrite :type-prescription))

   (defthm bpfn-u-prime-real
     (realp (bpfn-u-prime contextu x))
   :rule-classes (:rewrite :type-prescription))

   (defthm bpfn-v-prime-real
     (realp (bpfn-v-prime contextv x))
   :rule-classes (:rewrite :type-prescription))

   (defthm bpfn-u-prime-is-derivative
     (implies (and (standardp x)
                   (standardp contextu)
		   (inside-interval-p x (bpfn-domain))
		   (inside-interval-p x1 (bpfn-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (bpfn-u contextu x)
                             (bpfn-u contextu x1))
                          (- x x1))
		       (bpfn-u-prime contextu x))))

   (defthm bpfn-v-prime-is-derivative
     (implies (and (standardp x)
                   (standardp contextv)
		   (inside-interval-p x (bpfn-domain))
		   (inside-interval-p x1 (bpfn-domain))
		   (i-close x x1) (not (= x x1)))
	      (i-close (/ (- (bpfn-v contextv x)
                             (bpfn-v contextv x1))
                          (- x x1))
		       (bpfn-v-prime contextv x))))

   (defthm bpfn-u-prime-continuous
     (implies (and (standardp x)
                   (standardp contextu)
		   (inside-interval-p x (bpfn-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (bpfn-domain)))
	      (i-close (bpfn-u-prime contextu x)
		       (bpfn-u-prime contextu x1))))

   (defthm bpfn-v-prime-continuous
     (implies (and (standardp x)
                   (standardp contextv)
		   (inside-interval-p x (bpfn-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (bpfn-domain)))
	      (i-close (bpfn-v-prime contextv x)
		       (bpfn-v-prime contextv x1))))
   )

(encapsulate
    (((bpfn-u*v * *) => *)
     ((bpfn-u*v-prime * *) => *)
     )

    (local
     (defun bpfn-u*v (context x)
       (* (bpfn-u (bpfn-car-context context) x)
          (bpfn-v (bpfn-cdr-context context) x))))

  (defthm bpfn-u*v-definition
      (implies t ; (inside-interval-p x (bpfn-domain))
               (equal (bpfn-u*v context x)
                      (* (bpfn-u (bpfn-car-context context) x)
                         (bpfn-v (bpfn-cdr-context context) x)))))

  (local
   (defun bpfn-u*v-prime (context x)
     (+ (* (bpfn-u (bpfn-car-context context) x)
           (bpfn-v-prime (bpfn-cdr-context context) x))
        (* (bpfn-v (bpfn-cdr-context context) x)
           (bpfn-u-prime (bpfn-car-context context) x)))))

  (defthm bpfn-u*v-prime-definition
      (implies t ; (inside-interval-p x (bpfn-domain))
               (equal (bpfn-u*v-prime context x)
                      (+ (* (bpfn-u (bpfn-car-context context) x)
                            (bpfn-v-prime (bpfn-cdr-context context) x))
                         (* (bpfn-v (bpfn-cdr-context context) x)
                            (bpfn-u-prime (bpfn-car-context context) x))))))
  )

(local
 (defthm-std standard-bpfn-u
     (implies (and (standardp x)
                   (standardp contextu))
              (standardp (bpfn-u contextu x)))))

(local
 (defthm-std standard-bpfn-u-prime
     (implies (and (standardp x)
                   (standardp contextu))
              (standardp (bpfn-u-prime contextu x)))))

(local
 (defthm-std standard-bpfn-v
     (implies (and (standardp x)
                   (standardp contextv))
              (standardp (bpfn-v contextv x)))))

(local
 (defthm-std standard-bpfn-v-prime
     (implies (and (standardp x)
                   (standardp contextv))
              (standardp (bpfn-v-prime contextv x)))))

(local
 (defthm close-if-same-standard-part
     (implies (and (acl2-numberp x)
		   (acl2-numberp y)
		   (i-limited x)
		   (i-limited y)
		   (equal (standard-part x) (standard-part y)))
	      (i-close x y))
   :hints (("Goal"
	    :use ((:instance i-close-transitive
			     (x x)
			     (y (standard-part x))
			     (z y)))
	    :in-theory (disable i-close-transitive)))))

(defthm bpfn-u-differentiable
   (implies (and (standardp x)
                 (standardp contextu)
		 (inside-interval-p x (bpfn-domain))
		 (inside-interval-p y1 (bpfn-domain))
		 (inside-interval-p y2 (bpfn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (bpfn-u contextu x) (bpfn-u contextu y1))
                               (- x y1)))
		 (i-close (/ (- (bpfn-u contextu x) (bpfn-u contextu y1))
                             (- x y1))
			  (/ (- (bpfn-u contextu x) (bpfn-u contextu y2))
                             (- x y2)))))
  :hints (("Goal"
           :use ((:instance i-close-limited
                            (x (bpfn-u-prime contextu x))
                            (y (/ (- (bpfn-u contextu x) (bpfn-u contextu y1))
                                  (- x y1))))
                 (:instance i-close-limited
                            (x (bpfn-u-prime contextu x))
                            (y (/ (- (bpfn-u contextu x) (bpfn-u contextu y2))
                               (- x y2))))
                 (:instance close-if-same-standard-part
                            (x (/ (- (bpfn-u contextu x)
                                     (bpfn-u contextu y2))
                                  (- x y2)))
                            (y (/ (- (bpfn-u contextu x)
                                     (bpfn-u contextu y1))
                                  (- x y1))))
                 (:instance bpfn-u-prime-is-derivative
                            (x1 y1))
                 (:instance bpfn-u-prime-is-derivative
                            (x1 y2))
                 (:instance STANDARDS-ARE-LIMITED
                            (x (BPFN-U-PRIME CONTEXTu X))))
           :in-theory (disable i-close-limited
                               bpfn-u-prime-is-derivative))
          ))

(defthm bpfn-v-differentiable
   (Implies (and (standardp x)
                 (standardp contextv)
		 (inside-interval-p x (bpfn-domain))
		 (inside-interval-p y1 (bpfn-domain))
		 (inside-interval-p y2 (bpfn-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (bpfn-v contextv x) (bpfn-v contextv y1))
                               (- x y1)))
		 (i-close (/ (- (bpfn-v contextv x) (bpfn-v contextv y1))
                             (- x y1))
			  (/ (- (bpfn-v contextv x) (bpfn-v contextv y2))
                             (- x y2)))))
  :hints (("Goal"
           :use ((:instance i-close-limited
                            (x (bpfn-v-prime contextv x))
                            (y (/ (- (bpfn-v contextv x) (bpfn-v contextv y1))
                                  (- x y1))))
                 (:instance i-close-limited
                            (x (bpfn-v-prime contextv x))
                            (y (/ (- (bpfn-v contextv x) (bpfn-v contextv y2))
                               (- x y2))))
                 (:instance close-if-same-standard-part
                            (x (/ (- (bpfn-v contextv x)
                                     (bpfn-v contextv y2))
                                  (- x y2)))
                            (y (/ (- (bpfn-v contextv x)
                                     (bpfn-v contextv y1))
                                  (- x y1))))
                 (:instance bpfn-v-prime-is-derivative
                            (x1 y1))
                 (:instance bpfn-v-prime-is-derivative
                            (x1 y2))
                 (:instance STANDARDS-ARE-LIMITED
                            (x (BPFN-v-PRIME CONTEXTv X))))
           :in-theory (disable i-close-limited
                               bpfn-v-prime-is-derivative))
          ))


(defthm bpfn-u-continuous
    (implies (and (standardp x)
                  (standardp contextu)
		  (inside-interval-p x (bpfn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (bpfn-domain)))
	     (i-close (bpfn-u contextu x)
		      (bpfn-u contextu x1)))
  :hints (("Goal"
           :by (:instance
                (:functional-instance
                 rdfn-continuous
                 (rdfn bpfn-u)
                 (rdfn-domain bpfn-domain))
                (context contextu)))
          ("Subgoal 3"
           :use ((:instance bpfn-u-differentiable
                            (contextu context))))
          ("Subgoal 2"
           :use ((:instance bpfn-domain-non-trivial)))
          )

  )

(defthm bpfn-v-continuous
    (implies (and (standardp x)
                  (standardp contextv)
		  (inside-interval-p x (bpfn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (bpfn-domain)))
	     (i-close (bpfn-v contextv x)
		      (bpfn-v contextv x1)))
  :hints (("Goal"
           :by (:instance
                (:functional-instance
                 rdfn-continuous
                 (rdfn bpfn-v)
                 (rdfn-domain bpfn-domain))
                (context contextv)))
          ("Subgoal 3"
           :use ((:instance bpfn-v-differentiable
                            (contextv context))))
          ("Subgoal 2"
           :use ((:instance bpfn-domain-non-trivial)))
          )

  )

(defun bpfn-u-plain*v-prime (context x)
  (* (bpfn-u (bpfn-car-context context) x)
     (bpfn-v-prime (bpfn-cdr-context context) x)))


(defun bpfn-u-prime*v-plain (context x)
  (* (bpfn-v (bpfn-cdr-context context) x)
     (bpfn-u-prime (bpfn-car-context context) x)))

(local
 (defthm bpfn-u-plain*v-prime-continuous
     (Implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (bpfn-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (bpfn-domain)))
	      (i-close (bpfn-u-plain*v-prime context x)
		       (bpfn-u-plain*v-prime context x1)))
 :hints (("Goal"
          :use ((:instance
                 (:functional-instance
                  prod-f1*f2-continuous
                  (prod-f1 bpfn-u)
                  (prod-f2 bpfn-v-prime)
                  (prod-f1*f2 bpfn-u-plain*v-prime)
                  (prod-car-context bpfn-car-context)
                  (prod-cdr-context bpfn-cdr-context)
                  (prod-domain bpfn-domain))
                 (y x1))))
         ("Subgoal 4"
          :use ((:instance bpfn-domain-non-trivial)))
         )))

(local
 (defthm bpfn-u-prime*v-plain-continuous
     (Implies (and (standardp x)
                   (standardp context)
		   (inside-interval-p x (bpfn-domain))
		   (i-close x x1)
		   (inside-interval-p x1 (bpfn-domain)))
	      (i-close (bpfn-u-prime*v-plain context x)
		       (bpfn-u-prime*v-plain context x1)))
 :hints (("Goal"
          :use ((:instance
                 (:functional-instance
                  prod-f1*f2-continuous
                  (prod-f1 bpfn-u-prime)
                  (prod-f2 bpfn-v)
                  (prod-f1*f2 bpfn-u-prime*v-plain)
                  (prod-car-context bpfn-car-context)
                  (prod-cdr-context bpfn-cdr-context)
                  (prod-domain bpfn-domain))
                 (y x1))))
         ("Subgoal 4"
          :use ((:instance bpfn-domain-non-trivial)))
         )))

(local
 (defthmd close-sum-components
     (implies (and (i-close x1 x2)
                   (i-close y1 y2))
              (i-close (+ x1 y1)
                       (+ x2 y2)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(defthm bpfn-u*v-prime-continuous
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (bpfn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (bpfn-domain)))
	     (i-close (bpfn-u*v-prime context x)
		      (bpfn-u*v-prime context x1)))
  :hints (("Goal"
           :use ((:instance bpfn-u-prime*v-plain-continuous)
                 (:instance bpfn-u-plain*v-prime-continuous)
                 (:instance CLOSE-SUM-COMPONENTS
                            (x1 (* (BPFN-U-PRIME (bpfn-car-context CONTEXT) X)
                                   (BPFN-V (bpfn-cdr-context CONTEXT) X)))
                            (x2 (* (BPFN-U-PRIME (bpfn-car-context CONTEXT) X1)
                                   (BPFN-V (bpfn-cdr-context CONTEXT) X1)))
                            (y1 (* (BPFN-U (bpfn-car-context CONTEXT) X)
                                   (BPFN-V-PRIME (bpfn-cdr-context CONTEXT) X)))
                            (y2 (* (BPFN-U (bpfn-car-context CONTEXT) X1)
                                   (BPFN-V-PRIME (bpfn-cdr-context CONTEXT) X1))))
                 )))
  )

(defthmd bpfn-u*v-differentiable
    (implies (and (standardp x)
                  (standardp context)
                  (inside-interval-p x (bpfn-domain))
                  (inside-interval-p y1 (bpfn-domain))
                  (inside-interval-p y2 (bpfn-domain))
                  (i-close x y1) (not (= x y1))
                  (i-close x y2) (not (= x y2)))
             (and (i-limited (/ (- (bpfn-u*v context x)
                                   (bpfn-u*v context y1))
                                (- x y1)))
                  (i-close (/ (- (bpfn-u*v context x)
                                 (bpfn-u*v context y1))
                              (- x y1))
                           (/ (- (bpfn-u*v context x)
                                 (bpfn-u*v context y2))
                              (- x y2)))))
  :hints (("Goal"
           :by (:functional-instance dc-fn1*fn2-differentiable
                                     (dc-fn1*fn2 bpfn-u*v)
                                     (dc-fn1 bpfn-u)
                                     (dc-fn2 bpfn-v)
                                     (dc-fnz (lambda (context x) 1))
                                     (dc-fn-domain bpfn-domain)
                                     (dc-car-context bpfn-car-context)
                                     (dc-cdr-context bpfn-cdr-context)
                                     )
           )
          ("Subgoal 4"
           :use ((:instance bpfn-v-differentiable
                            (contextv context2))))
          ("Subgoal 3"
           :use ((:instance bpfn-u-differentiable
                            (contextu context1))))
          ("Subgoal 2"
           :use ((:instance bpfn-domain-non-trivial)))
          ))

(local
 (defthm-std standard-bpfn-u*v-prime
     (implies (and (standardp x)
                   (standardp context))
              (standardp (bpfn-u*v-prime context x)))))


(local
 (defthm-std standard-differential-u*v
     (implies (and (standardp context)
                   (standardp x))
              (standardp (+ (* (BPFN-U (CAR CONTEXT) X)
                               (BPFN-V-PRIME (CADR CONTEXT) X))
                            (* (BPFN-U-PRIME (CAR CONTEXT) X)
                               (BPFN-V (CADR CONTEXT) X)))))))

(local
 (defthm-std standard-bpfn-u-prime
     (implies (and (standardp x)
                   (standardp contextu))
              (standardp (bpfn-u-prime contextu x)))))

(local
 (defthmd bpfn-u-prime-is-standard-part-of-differential-part1
     (implies (and (standardp x)
                   (standardp contextu)
                   (inside-interval-p x (bpfn-domain))
                   (inside-interval-p (+ x (/ (i-large-integer))) (bpfn-domain)))
              (equal (bpfn-u-prime contextu x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-u contextu (+ x (/ (i-large-integer))))
                                (bpfn-u contextu x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (/ (- (bpfn-u contextu (- x (/ (i-large-integer))))
                                   (bpfn-u contextu x))
                                (- (/ (i-large-integer))))
                             'error))))
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part
                             (x (bpfn-u-prime contextu x))
                             (y (/ (- (bpfn-u contextu (+ x (/ (i-large-integer))))
                                      (bpfn-u contextu x))
                                   (/ (i-large-integer)))))
                  ;; (:instance close-x-y->same-standard-part
                  ;;            (x (bpfn-u-prime contextu x))
                  ;;            (y (/ (- (bpfn-u contextu (- x (/ (i-large-integer))))
                  ;;                     (bpfn-u contextu x))
                  ;;                  (- (/ (i-large-integer))))))
                  (:instance BPFN-U-PRIME-IS-DERIVATIVE
                             (x1 (+ x (/ (i-large-integer)))))
                  ;; (:instance BPFN-U-PRIME-IS-DERIVATIVE
                  ;;            (x1 (- x (/ (i-large-integer)))))
                  (:instance inside-interval-x+eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  ;; (:instance inside-interval-x-eps
                  ;;            (eps (/ (i-large-integer)))
                  ;;            (interval (bpfn-domain)))
                  (:INSTANCE bpfn-domain-non-trivial)
                  (:instance i-close-to-small-sum
                             (eps (/ (i-large-integer))))
                  (:instance i-close-symmetric
                             (x (+ (- (* (I-LARGE-INTEGER)
                                         (BPFN-U CONTEXTU X)))
                                   (* (I-LARGE-INTEGER)
                                      (BPFN-U CONTEXTU (+ (/ (I-LARGE-INTEGER)) X)))))
                             (y (BPFN-U-PRIME CONTEXTU X)))
                  (:instance standards-are-limited
                             (x (BPFN-U-PRIME CONTEXTU X)))
                  )
            :in-theory (disable close-x-y->same-standard-part
                                i-close-symmetric
                                )))
   ))

(local
 (defthmd bpfn-u-prime-is-standard-part-of-differential-part2
     (implies (and (standardp x)
                   (standardp contextu)
                   (inside-interval-p x (bpfn-domain))
                   (not (inside-interval-p (+ x (/ (i-large-integer))) (bpfn-domain)))
                   (inside-interval-p (- x (/ (i-large-integer))) (bpfn-domain)))
              (equal (bpfn-u-prime contextu x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-u contextu (+ x (/ (i-large-integer))))
                                (bpfn-u contextu x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (standard-part
                              (/ (- (bpfn-u contextu (- x (/ (i-large-integer))))
                                    (bpfn-u contextu x))
                                 (- (/ (i-large-integer)))))
                             'error))))
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part
                             (x (bpfn-u-prime contextu x))
                             (y (/ (- (bpfn-u contextu (- x (/ (i-large-integer))))
                                      (bpfn-u contextu x))
                                   (- (/ (i-large-integer))))))
                  (:instance BPFN-U-PRIME-IS-DERIVATIVE
                             (x1 (- x (/ (i-large-integer)))))
                  (:instance inside-interval-x-eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  (:INSTANCE bpfn-domain-non-trivial)
                  (:instance i-close-to-small-sum
                             (eps (- (/ (i-large-integer)))))
                  (:instance standards-are-limited
                             (x (BPFN-U-PRIME CONTEXTU X)))
                  )
            :in-theory (disable close-x-y->same-standard-part
                                )))
   ))

(defthm bpfn-domain-not-both-endpoints
    (implies (inside-interval-p x (bpfn-domain))
	     (or (not (equal (interval-left-endpoint (bpfn-domain)) x))
		 (not (equal (interval-right-endpoint (bpfn-domain)) x))))
  :hints (("Goal"
	   :use ((:instance bpfn-domain-non-trivial))))
  :rule-classes nil)

(defthm-std standard-bpfn-domain
    (standardp (bpfn-domain)))

(local
 (defthmd bpfn-u-prime-is-standard-part-of-differential
     (implies (and (standardp x)
                   (standardp contextu)
                   (inside-interval-p x (bpfn-domain)))
              (equal (bpfn-u-prime contextu x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-u contextu (+ x (/ (i-large-integer))))
                                (bpfn-u contextu x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (standard-part
                              (/ (- (bpfn-u contextu (- x (/ (i-large-integer))))
                                    (bpfn-u contextu x))
                                 (- (/ (i-large-integer)))))
                             'error))))
   :hints (("Goal"
            :use ((:instance bpfn-u-prime-is-standard-part-of-differential-part1)
                  (:instance bpfn-u-prime-is-standard-part-of-differential-part2)
                  (:instance bpfn-domain-not-both-endpoints)
                  (:instance inside-interval-x+eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  (:instance inside-interval-x-eps
                             (eps (- (/ (i-large-integer))))
                             (interval (bpfn-domain)))
                  )
            )
           )
   ))

(local
 (defthm-std standard-bpfn-v-prime
     (implies (and (standardp x)
                   (standardp contextv))
              (standardp (bpfn-v-prime contextv x)))))

(local
 (defthmd bpfn-v-prime-is-standard-part-of-differential-part1
     (implies (and (standardp x)
                   (standardp contextv)
                   (inside-interval-p x (bpfn-domain))
                   (inside-interval-p (+ x (/ (i-large-integer))) (bpfn-domain)))
              (equal (bpfn-v-prime contextv x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-v contextv (+ x (/ (i-large-integer))))
                                (bpfn-v contextv x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (/ (- (bpfn-v contextv (- x (/ (i-large-integer))))
                                   (bpfn-v contextv x))
                                (- (/ (i-large-integer))))
                             'error))))
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part
                             (x (bpfn-v-prime contextv x))
                             (y (/ (- (bpfn-v contextv (+ x (/ (i-large-integer))))
                                      (bpfn-v contextv x))
                                   (/ (i-large-integer)))))
                  ;; (:instance close-x-y->same-standard-part
                  ;;            (x (bpfn-v-prime contextv x))
                  ;;            (y (/ (- (bpfn-v contextv (- x (/ (i-large-integer))))
                  ;;                     (bpfn-v contextv x))
                  ;;                  (- (/ (i-large-integer))))))
                  (:instance BPFN-V-PRIME-IS-DERIVATIVE
                             (x1 (+ x (/ (i-large-integer)))))
                  ;; (:instance BPFN-V-PRIME-IS-DERIVATIVE
                  ;;            (x1 (- x (/ (i-large-integer)))))
                  (:instance inside-interval-x+eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  ;; (:instance inside-interval-x-eps
                  ;;            (eps (/ (i-large-integer)))
                  ;;            (interval (bpfn-domain)))
                  (:INSTANCE bpfn-domain-non-trivial)
                  (:instance i-close-to-small-sum
                             (eps (/ (i-large-integer))))
                  (:instance i-close-symmetric
                             (x (+ (- (* (I-LARGE-INTEGER)
                                         (BPFN-V CONTEXTV X)))
                                   (* (I-LARGE-INTEGER)
                                      (BPFN-V CONTEXTV (+ (/ (I-LARGE-INTEGER)) X)))))
                             (y (BPFN-V-PRIME CONTEXTV X)))
                  (:instance standards-are-limited
                             (x (BPFN-V-PRIME CONTEXTV X)))
                  )
            :in-theory (disable close-x-y->same-standard-part
                                i-close-symmetric
                                )))
   ))

(local
 (defthmd bpfn-v-prime-is-standard-part-of-differential-part2
     (implies (and (standardp x)
                   (standardp contextv)
                   (inside-interval-p x (bpfn-domain))
                   (not (inside-interval-p (+ x (/ (i-large-integer))) (bpfn-domain)))
                   (inside-interval-p (- x (/ (i-large-integer))) (bpfn-domain)))
              (equal (bpfn-v-prime contextv x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-v contextv (+ x (/ (i-large-integer))))
                                (bpfn-v contextv x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (standard-part
                              (/ (- (bpfn-v contextv (- x (/ (i-large-integer))))
                                    (bpfn-v contextv x))
                                 (- (/ (i-large-integer)))))
                             'error))))
   :hints (("Goal"
            :use ((:instance close-x-y->same-standard-part
                             (x (bpfn-v-prime contextv x))
                             (y (/ (- (bpfn-v contextv (- x (/ (i-large-integer))))
                                      (bpfn-v contextv x))
                                   (- (/ (i-large-integer))))))
                  (:instance BPFN-V-PRIME-IS-DERIVATIVE
                             (x1 (- x (/ (i-large-integer)))))
                  (:instance inside-interval-x-eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  (:INSTANCE bpfn-domain-non-trivial)
                  (:instance i-close-to-small-sum
                             (eps (- (/ (i-large-integer)))))
                  (:instance standards-are-limited
                             (x (BPFN-V-PRIME CONTEXTV X)))
                  )
            :in-theory (disable close-x-y->same-standard-part
                                )))
   ))

(defthm bpfn-domain-not-both-endpoints
    (implies (inside-interval-p x (bpfn-domain))
	     (or (not (equal (interval-left-endpoint (bpfn-domain)) x))
		 (not (equal (interval-right-endpoint (bpfn-domain)) x))))
  :hints (("Goal"
	   :use ((:instance bpfn-domain-non-trivial))))
  :rule-classes nil)

(defthm-std standard-bpfn-domain
    (standardp (bpfn-domain)))

(local
 (defthmd bpfn-v-prime-is-standard-part-of-differential
     (implies (and (standardp x)
                   (standardp contextv)
                   (inside-interval-p x (bpfn-domain)))
              (equal (bpfn-v-prime contextv x)
                     (if (inside-interval-p (+ x (/ (i-large-integer)))
                                            (bpfn-domain))
                         (standard-part
                          (/ (- (bpfn-v contextv (+ x (/ (i-large-integer))))
                                (bpfn-v contextv x))
                             (/ (i-large-integer))))
                         (if (inside-interval-p (- x (/ (i-large-integer)))
                                                (bpfn-domain))
                             (standard-part
                              (/ (- (bpfn-v contextv (- x (/ (i-large-integer))))
                                    (bpfn-v contextv x))
                                 (- (/ (i-large-integer)))))
                             'error))))
   :hints (("Goal"
            :use ((:instance bpfn-v-prime-is-standard-part-of-differential-part1)
                  (:instance bpfn-v-prime-is-standard-part-of-differential-part2)
                  (:instance bpfn-domain-not-both-endpoints)
                  (:instance inside-interval-x+eps
                             (eps (/ (i-large-integer)))
                             (interval (bpfn-domain)))
                  (:instance inside-interval-x-eps
                             (eps (- (/ (i-large-integer))))
                             (interval (bpfn-domain)))
                  )
            )
           )
   ))

;; (local
;;  (defthm bpfn-u*v-prime-differentiable
;;      (implies (and (standardp x)
;;                    (standardp context)
;;                    (inside-interval-p x (bpfn-domain))
;;                    (inside-interval-p y1 (bpfn-domain))
;;                    (inside-interval-p y2 (bpfn-domain))
;;                    (i-close x y1) (not (= x y1))
;;                    (i-close x y2) (not (= x y2))
;;                    )
;;               (and (i-limited (/ (- (bpfn-u*v context x)
;;                                     (bpfn-u*v context y1))
;;                                  (- x y1)))
;;                    (i-close (/ (- (bpfn-u*v context x)
;;                                   (bpfn-u*v context y1))
;;                                (- x y2))
;;                             (/ (- (bpfn-u*v context x)
;;                                   (bpfn-u*v context y2))
;;                                (- x y2)))))
;;    :hints ((""
;;            ))))

(defun differential-bpfn-u (contextu x eps)
  (/ (- (bpfn-u contextu (+ x eps))
        (bpfn-u contextu x))
     eps))

(defun differential-bpfn-v (contextv x eps)
  (/ (- (bpfn-v contextv (+ x eps))
        (bpfn-v contextv x))
     eps))

(defun differential-bpfn-u*v (context x eps)
  (+ (* (bpfn-u (bpfn-car-context context) (+ x eps))
	(differential-bpfn-v (bpfn-cdr-context context) x eps))
     (* (bpfn-v (bpfn-cdr-context context) x)
	(differential-bpfn-u (bpfn-car-context context) x eps))))

(local
 (defthm-std standard-bpfn-car-context
     (implies (standardp context)
              (standardp (bpfn-car-context context)))))

(local
 (defthm-std standard-bpfn-cdr-context
     (implies (standardp context)
              (standardp (bpfn-cdr-context context)))))

(local
 (defthm differential-bpfn-u*v-close
     (implies (and (inside-interval-p x (bpfn-domain))
                   (standardp x)
                   (standardp context)
                   (i-small eps) (not (= eps 0))
                   (inside-interval-p (+ x eps) (bpfn-domain))
                   )
              (i-close (differential-bpfn-u*v context x eps)
                       (bpfn-u*v-prime context x)))
   :hints (("Goal"
            :use ((:functional-instance
                   differential-dc-fn1*fn2-close
                   (dc-fn-domain bpfn-domain)
                   (dc-fn1 bpfn-u)
                   (dc-fn2 bpfn-v)
                   (dc-car-context bpfn-car-context)
                   (dc-cdr-context bpfn-cdr-context)
                   (dc-fnz (lambda (context x) 1))
                   (differential-dc-fn1*fn2
                    differential-bpfn-u*v)
                   (derivative-dc-fn1*fn2
                    bpfn-u*v-prime)
                   (derivative-dc-fn1 bpfn-u-prime)
                   (derivative-dc-fn2 bpfn-v-prime)
                   (differential-dc-fn1
                    (lambda (context x eps)
                      (/ (- (bpfn-u context (+ x eps)) (bpfn-u context x))
                         eps)))
                   (differential-dc-fn2
                    (lambda (context x eps)
                      (/ (- (bpfn-v context (+ x eps)) (bpfn-v context x))
                         eps)))
                   )
                  (:instance CLOSE-IF-SAME-STANDARD-PART
                             (x (differential-bpfn-u*v context x eps))
                             (y (bpfn-u*v-prime context x)))
                  (:instance bpfn-u*v-differentiable
                             (y1 (+ x eps))
                             (y2 (+ x eps)))
                  (:instance i-close-to-small-sum)
                  (:instance bpfn-u-prime-is-standard-part-of-differential
                             (contextu context))
                  (:instance bpfn-v-prime-is-standard-part-of-differential
                             (contextv context))
                  (:instance standards-are-limited
                             (x (+ (* (BPFN-U (bpfn-car-context CONTEXT) X)
                                      (BPFN-V-PRIME (bpfn-cdr-context CONTEXT) X))
                                   (* (BPFN-U-PRIME (bpfn-car-context CONTEXT) X)
                                      (BPFN-V (bpfn-cdr-context CONTEXT) X)))))
                  )
            )
           ("Subgoal 4"
            :use ((:instance bpfn-u-prime-is-standard-part-of-differential
                             (contextu context1))
                  )
            )
           ("Subgoal 3"
            :use ((:instance bpfn-v-prime-is-standard-part-of-differential
                             (contextv context2))
                  )
            )
           )))

(defun map-bpfn-u*v-prime (context p)
  (if (consp p)
      (cons (bpfn-u*v-prime context (car p))
            (map-bpfn-u*v-prime context (cdr p)))
      nil))

(defun riemann-bpfn-u*v-prime (context p)
  (dotprod (deltas p)
           (map-bpfn-u*v-prime context (cdr p))))


(encapsulate nil

    (defthm limited-riemann-bpfn-u*v-prime-small-partition
     (implies (and (realp a) (standardp a)
		   (realp b) (standardp b)
                   (standardp context)
		   (inside-interval-p a (bpfn-domain))
		   (inside-interval-p b (bpfn-domain))
		   (< a b))
	      (i-limited (riemann-bpfn-u*v-prime context (make-small-partition a b))))
     :hints (("Goal"
	      :by (:functional-instance limited-riemann-rcfn-small-partition
				        (rcfn-domain bpfn-domain)
				        (rcfn bpfn-u*v-prime)
				        (map-rcfn map-bpfn-u*v-prime)
				        (riemann-rcfn riemann-bpfn-u*v-prime)))
             ("Subgoal 4"
              :use ((:instance bpfn-u*v-prime-continuous
                               (x1 y))))
	     ("Subgoal 2"
	      :use ((:instance bpfn-domain-non-trivial)))))

  (local (in-theory (disable riemann-bpfn-u*v-prime)))

  (defun-std strict-int-bpfn-u*v-prime (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (bpfn-domain))
	     (inside-interval-p b (bpfn-domain))
	     (< a b))
        (standard-part (riemann-bpfn-u*v-prime context (make-small-partition a b)))
        0))
  )

(defun int-bpfn-u*v-prime (context a b)
  (if (<= a b)
      (strict-int-bpfn-u*v-prime context a b)
      (- (strict-int-bpfn-u*v-prime context b a))))

(defthm expand-differential-bpfn-u*v
  (implies (and (inside-interval-p x (bpfn-domain))
		(inside-interval-p (+ x eps) (bpfn-domain)))
	   (equal (differential-bpfn-u*v context x eps)
		  (/ (- (bpfn-u*v context (+ x eps))
                        (bpfn-u*v context x))
                     eps)))
  :rule-classes nil)

(local
 (defthmd i-close-small-diff
     (implies (i-close x x1)
              (i-small (- x1 x)))
   :hints (("Goal"
            :use ((:instance I-SMALL-UMINUS
                             (x (- x x1))))
            :in-theory (enable i-close)))))

(encapsulate
    nil

    (local
     (defthmd lemma-1
         (equal (/ (- x1 x))
                (- (/ (- x x1))))
       :hints (("Goal"
                :use ((:instance
                       (:theorem (equal (/ (- x)) (- (/ x))))
                       (x (- x1 x))))))

       ))

  (defthm by-parts-lhs
      (implies (and (inside-interval-p a (bpfn-domain))
		    (inside-interval-p b (bpfn-domain)))
	       (equal (int-bpfn-u*v-prime context a b)
		      (- (bpfn-u*v context b)
		         (bpfn-u*v context a))))
    :hints (("Goal"
             :use ((:instance
                    (:functional-instance
                     ftc-2
                     (rcdfn bpfn-u*v)
                     (rcdfn-prime bpfn-u*v-prime)
                     (rcdfn-domain bpfn-domain)
                     (int-rcdfn-prime int-bpfn-u*v-prime)
                     (strict-int-rcdfn-prime STRICT-INT-bpfn-u*v-PRIME)
                     (MAP-RCDFN-PRIME map-bpfn-u*v-prime)
                     (RIEMANN-RCDFN-PRIME riemann-bpfn-u*v-prime)
                     )
                    )))
            ("Subgoal 10"
             :use ((:instance bpfn-u*v-prime-continuous
                              ))
             )
            ("Subgoal 9"
             :use ((:instance expand-differential-bpfn-u*v
                              (eps (- x1 x))
                              )
                   (:instance differential-bpfn-u*v-close
                              (eps (- x1 x)))
                   (:instance i-close-small-diff)
                   (:instance lemma-1)
                   )
;:in-theory (disable BPFN-U*V-DEFINITION)
             )
            ("Subgoal 6"
             :use ((:instance bpfn-domain-non-trivial)))

            ))
  )

(defun map-bpfn-u-plain*v-prime (context p)
  (if (consp p)
      (cons (bpfn-u-plain*v-prime context (car p))
            (map-bpfn-u-plain*v-prime context (cdr p)))
      nil))

(defun riemann-bpfn-u-plain*v-prime (context p)
  (dotprod (deltas p)
           (map-bpfn-u-plain*v-prime context (cdr p))))


(encapsulate
    nil

    (defthm limited-riemann-bpfn-u-plain*v-prime-small-partition
     (implies (and (realp a) (standardp a)
		   (realp b) (standardp b)
                   (standardp context)
		   (inside-interval-p a (bpfn-domain))
		   (inside-interval-p b (bpfn-domain))
		   (< a b))
	      (i-limited (riemann-bpfn-u-plain*v-prime context (make-small-partition a b))))
     :hints (("Goal"
	      :by (:functional-instance limited-riemann-rcfn-small-partition
				        (rcfn-domain bpfn-domain)
				        (rcfn bpfn-u-plain*v-prime)
				        (map-rcfn map-bpfn-u-plain*v-prime)
				        (riemann-rcfn riemann-bpfn-u-plain*v-prime)))
             ("Subgoal 3"
              :use ((:instance bpfn-u-plain*v-prime-continuous
                               (x1 y))))
	     ("Subgoal 2"
	      :use ((:instance bpfn-domain-non-trivial)))))

  (local (in-theory (disable riemann-bpfn-u-plain*v-prime)))

  (defun-std strict-int-bpfn-u-plain*v-prime (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (bpfn-domain))
	     (inside-interval-p b (bpfn-domain))
	     (< a b))
        (standard-part (riemann-bpfn-u-plain*v-prime context (make-small-partition a b)))
        0))
  )

(defun int-bpfn-u-plain*v-prime (context a b)
  (if (<= a b)
      (strict-int-bpfn-u-plain*v-prime context a b)
      (- (strict-int-bpfn-u-plain*v-prime context b a))))

(defun map-bpfn-u-prime*v-plain (context p)
  (if (consp p)
      (cons (bpfn-u-prime*v-plain context (car p))
            (map-bpfn-u-prime*v-plain context (cdr p)))
      nil))

(defun riemann-bpfn-u-prime*v-plain (context p)
  (dotprod (deltas p)
           (map-bpfn-u-prime*v-plain context (cdr p))))


(encapsulate
    nil

    (defthm limited-riemann-bpfn-u-prime*v-plain-small-partition
     (implies (and (realp a) (standardp a)
		   (realp b) (standardp b)
                   (standardp context)
		   (inside-interval-p a (bpfn-domain))
		   (inside-interval-p b (bpfn-domain))
		   (< a b))
	      (i-limited (riemann-bpfn-u-prime*v-plain context (make-small-partition a b))))
     :hints (("Goal"
	      :by (:functional-instance limited-riemann-rcfn-small-partition
				        (rcfn-domain bpfn-domain)
				        (rcfn bpfn-u-prime*v-plain)
				        (map-rcfn map-bpfn-u-prime*v-plain)
				        (riemann-rcfn riemann-bpfn-u-prime*v-plain)))
             ("Subgoal 3"
              :use ((:instance bpfn-u-prime*v-plain-continuous
                               (x1 y))))
	     ("Subgoal 2"
	      :use ((:instance bpfn-domain-non-trivial)))))

  (local (in-theory (disable riemann-bpfn-u-prime*v-plain)))

  (defun-std strict-int-bpfn-u-prime*v-plain (context a b)
    (if (and (realp a)
	     (realp b)
	     (inside-interval-p a (bpfn-domain))
	     (inside-interval-p b (bpfn-domain))
	     (< a b))
        (standard-part (riemann-bpfn-u-prime*v-plain context (make-small-partition a b)))
        0))
  )

(defun int-bpfn-u-prime*v-plain (context a b)
  (if (<= a b)
      (strict-int-bpfn-u-prime*v-plain context a b)
      (- (strict-int-bpfn-u-prime*v-plain context b a))))


(defthm bpfn-u-plain*v-prime-integral
    (implies (and (standardp a)
                  (standardp b)
                  (standardp context)
                  (<= a b)
                  (inside-interval-p a (bpfn-domain))
                  (inside-interval-p b (bpfn-domain))
                  (partitionp p)
                  (equal (car p) a)
                  (equal (car (last p)) b)
                  (i-small (mesh p)))
             (i-close (riemann-bpfn-u-plain*v-prime context p)
                      (strict-int-bpfn-u-plain*v-prime context a b)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   strict-int-rcfn-is-integral-of-rcfn
                   (rcfn bpfn-u-plain*v-prime)
                   (rcfn-domain bpfn-domain)
                   (riemann-rcfn riemann-bpfn-u-plain*v-prime)
                   (strict-int-rcfn strict-int-bpfn-u-plain*v-prime)
                   (MAP-RCFN map-bpfn-u-plain*v-prime)
                   )
                  )
                 )
           )
          ))

(defthm bpfn-u-prime*v-plain-integral
    (implies (and (standardp a)
                  (standardp b)
                  (standardp context)
                  (<= a b)
                  (inside-interval-p a (bpfn-domain))
                  (inside-interval-p b (bpfn-domain))
                  (partitionp p)
                  (equal (car p) a)
                  (equal (car (last p)) b)
                  (i-small (mesh p)))
             (i-close (riemann-bpfn-u-prime*v-plain context p)
                      (strict-int-bpfn-u-prime*v-plain context a b)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   strict-int-rcfn-is-integral-of-rcfn
                   (rcfn bpfn-u-prime*v-plain)
                   (rcfn-domain bpfn-domain)
                   (riemann-rcfn riemann-bpfn-u-prime*v-plain)
                   (strict-int-rcfn strict-int-bpfn-u-prime*v-plain)
                   (MAP-RCFN map-bpfn-u-prime*v-plain)
                   )
                  )
                 )
           )
          ))



(local
 (defthm realp-RIEMANN-BPFN-U-PRIME*V-PLAIN
     (implies (partitionp p)
              (realp (RIEMANN-BPFN-U-PRIME*V-PLAIN CONTEXT p)))))

(local
 (defthm-std realp-STRICT-INT-BPFN-U-PRIME*V-PLAIN
     (IMPLIES (AND (REALP A) (REALP B))
              (REALP (STRICT-INT-BPFN-U-PRIME*V-PLAIN CONTEXT A B)))
   :hints (("Goal"
            :use ((:instance realp-RIEMANN-BPFN-U-PRIME*V-PLAIN
                             (p (make-small-partition a b))))
            :in-theory (disable RIEMANN-BPFN-U-PRIME*V-PLAIN
                                realp-RIEMANN-BPFN-U-PRIME*V-PLAIN)))
   ))

(local
 (defthm realp-RIEMANN-BPFN-U-plain*V-prime
     (implies (partitionp p)
              (realp (RIEMANN-BPFN-U-plain*V-prime CONTEXT p)))))

(local
 (defthm-std realp-STRICT-INT-BPFN-U-plain*V-prime
     (IMPLIES (AND (REALP A) (REALP B))
              (REALP (STRICT-INT-BPFN-U-plain*V-prime CONTEXT A B)))
   :hints (("Goal"
            :use ((:instance realp-RIEMANN-BPFN-U-plain*V-prime
                             (p (make-small-partition a b))))
            :in-theory (disable RIEMANN-BPFN-U-plain*V-prime
                                realp-RIEMANN-BPFN-U-plain*V-prime)))
   ))

(local
 (defthm by-parts-rhs
     (implies (and (inside-interval-p a (bpfn-domain))
		   (inside-interval-p b (bpfn-domain)))
	      (equal (int-bpfn-u*v-prime context a b)
                     (+ (int-bpfn-u-plain*v-prime context a b)
                        (int-bpfn-u-prime*v-plain context a b))))
   :hints (("Goal"
            :use ((:instance
                   (:functional-instance
                    reduce-integral-rifn-left+right
                    (int-rifn-left+right int-bpfn-u*v-prime)
                    (int-rifn-left int-bpfn-u-plain*v-prime)
                    (int-rifn-right int-bpfn-u-prime*v-plain)
                    (domain-rifn-op bpfn-domain)
                    (strict-int-rifn-left strict-int-bpfn-u-plain*v-prime)
                    (strict-int-rifn-right strict-int-bpfn-u-prime*v-plain)
                    (riemann-rifn-left riemann-bpfn-u-plain*v-prime)
                    (riemann-rifn-right riemann-bpfn-u-prime*v-plain)
                    (map-rifn-right MAP-BPFN-U-PRIME*V-PLAIN)
                    (map-rifn-left MAP-BPFN-U-plain*V-prime)
                    (rifn-left bpfn-u-plain*v-prime)
                    (rifn-right bpfn-u-prime*v-plain)
                    (STRICT-INT-RIFN-LEFT+RIGHT STRICT-INT-BPFN-U*V-PRIME)
                    (MAP-RIFN-LEFT+RIGHT map-BPFN-U*V-PRIME)
                    (RIEMANN-RIFN-LEFT+RIGHT riemann-BPFN-U*V-PRIME)
                    (rifn-left+right BPFN-U*V-PRIME)
                    )
                   )
                  )
            )
           ("Subgoal 13"
            :use ((:instance bpfn-u-prime*v-plain-integral)))
           ("Subgoal 12"
            :use ((:instance bpfn-u-plain*v-prime-integral)))
           ("Subgoal 11"
            :use ((:instance bpfn-domain-non-trivial)))
           )))

(defthm integration-by-parts
    (implies (and (inside-interval-p a (bpfn-domain))
		  (inside-interval-p b (bpfn-domain)))
	     (equal (int-bpfn-u-plain*v-prime context a b)
                    (- (- (bpfn-u*v context b)
		          (bpfn-u*v context a))
                       (int-bpfn-u-prime*v-plain context a b))))
  :hints (("Goal"
           :use ((:instance by-parts-lhs)
                 (:instance by-parts-rhs))
           :in-theory (disable by-parts-lhs by-parts-rhs))))
