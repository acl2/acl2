(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(include-book "nsa")
(include-book "intervals")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)


(encapsulate
    ( ((prod-domain) => *)
      )

    (local (defun prod-domain () (interval 0 1)))

  (defthm intervalp-prod-domain
      (interval-p (prod-domain))
    :rule-classes (:type-prescription :rewrite))

  (defthm prod-domain-real
      (implies (inside-interval-p x (prod-domain))
	       (realp x))
    :rule-classes (:forward-chaining))

  (defthm prod-domain-non-trivial
      (or (null (interval-left-endpoint (prod-domain)))
	  (null (interval-right-endpoint (prod-domain)))
	  (< (interval-left-endpoint (prod-domain))
	     (interval-right-endpoint (prod-domain))))
    :rule-classes nil)

  )

(encapsulate
    ((prod-f1 (context x) t))

    ;; Our witness continuous function is the identity function.

    (local (defun prod-f1 (context x) (declare (ignore context)) x))

  ;; The function returns standard values for standard arguments.

  (defthm prod-f1-standard
      (implies (and (standardp x)
                    (standardp context))
	       (standardp (prod-f1 context x)))
    :rule-classes (:rewrite :type-prescription))

  ;; For real arguments, the function returns real values.

  (defthm prod-f1-real
      (implies (realp x)
	       (realp (prod-f1 context x)))
    :rule-classes (:rewrite :type-prescription))

  ;; If x is a standard real and y is a real close to x, then f1(x)
  ;; is close to f1(y).

  (defthm prod-f1-continuous
      (implies (and (standardp x)
                    (standardp context)
		    (inside-interval-p x (prod-domain))
		    (i-close x y)
                    (inside-interval-p y (prod-domain)))
	       (i-close (prod-f1 context x)
                        (prod-f1 context y))))
  )

(encapsulate
    ((prod-f2 (context x) t))

    ;; Our witness continuous function is the identity function.

    (local (defun prod-f2 (context x) (declare (ignore context)) x))

  ;; The function returns standard values for standard arguments.

  (defthm prod-f2-standard
      (implies (and (standardp x)
                    (standardp context))
	       (standardp (prod-f2 context x)))
    :rule-classes (:rewrite :type-prescription))

  ;; For real arguments, the function returns real values.

  (defthm prod-f2-real
      (implies (realp x)
	       (realp (prod-f2 context x)))
    :rule-classes (:rewrite :type-prescription))

  ;; If x is a standard real and y is a real close to x, then prod-f2(x)
  ;; is close to prod-f2(y).

  (defthm prod-f2-continuous
      (implies (and (standardp x)
                    (standardp context)
		    (inside-interval-p x (prod-domain))
		    (i-close x y)
                    (inside-interval-p y (prod-domain)))
	       (i-close (prod-f2 context x) (prod-f2 context y))))
  )

(encapsulate
    ((prod-car-context (context) t)
     (prod-cdr-context (context) t))

    (local (defun prod-car-context (context) (car context)))
  (local (defun prod-cdr-context (context) (cdr context)))
  )




(defun prod-f1*f2 (context x)
  (* (prod-f1 (prod-car-context context) x)
     (prod-f2 (prod-cdr-context context) x)))

(defthm close-times
    (implies (and (i-close x1 x2)
		  (i-limited y))
	     (i-close (* x1 y) (* x2 y)))
  :hints (("Goal" :in-theory (enable i-close))
	  ("Goal''" :use ((:instance small*limited->small
				     (x (- x1 x2))
				     (y y)))
	            :in-theory (disable small*limited->small))))

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
	   :in-theory (disable close-times i-close-transitive i-close-limited))))

(local
 (defthm-std car-standard
     (implies (standardp context)
              (standardp (prod-car-context context)))))

(local
 (defthm-std cdr-standard
     (implies (standardp context)
              (standardp (prod-cdr-context context)))))

(defthm prod-f1*f2-continuous
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (prod-domain))
		  (i-close x y)
                  (inside-interval-p y (prod-domain)))
	     (i-close (prod-f1*f2 context x)
                      (prod-f1*f2 context y)))
  :hints (("Goal"
           :in-theory (enable standards-are-limited)))
  )
