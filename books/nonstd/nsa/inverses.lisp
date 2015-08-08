(in-package "ACL2")
; cert_param: (uses-acl2r)
; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ;; Constrain the functions ifn, ifn-domain-p, and ifn-range-p
 ;; so that ifn is a 1-1 and onto function from ifn-domain-p to
 ;; ifn-range-p.

 ((ifn (x) t)
  (ifn-domain-p (x) t)
  (ifn-range-p (y) t)
  ;(ifn-is-onto-predicate-witness (y) t)
  )

 (local
  (defun ifn (x) x))

 (local
  (defun ifn-domain-p (x)
    (realp x)))

 (local
  (defun ifn-range-p (x)
    (realp x)))

 ;; We restrict the domain and range to the reals.

 (defthm ifn-domain-real
     (implies (ifn-domain-p x)
	      (realp x)))

 (defthm ifn-range-real
     (implies (ifn-range-p x)
	      (realp x)))

 ;; The function maps the domain into the range.

 (defthm ifn-domain-into-range
     (implies (ifn-domain-p x)
	      (ifn-range-p (ifn x))))

 ;; The function ifn must be 1-1.

 (defthm ifn-is-1-1
   (implies (and (ifn-domain-p x1)
                 (ifn-domain-p x2)
                 (equal (ifn x1) (ifn x2)))
            (equal x1 x2))
   :rule-classes nil)

 ;; The function ifn is onto.

 (defun-sk ifn-is-onto-predicate (y)
     (exists (x)
	     (and (ifn-domain-p x)
		  (equal (ifn x) y))))

 (defthm ifn-is-onto
     (implies (ifn-range-p y)
	      (ifn-is-onto-predicate y))
   :hints (("Goal"
	    :use ((:instance ifn-is-onto-predicate-suff (x y) (y y)))))
   )

)

(defchoose ifn-inverse (x) (y)
  (if (ifn-range-p y)
      (and (ifn-domain-p x)
	   (equal (ifn x) y))
      (realp x)))

(defthm ifn-inverse-exists
    (implies (ifn-range-p y)
	     (and (ifn-domain-p (ifn-inverse y))
		  (equal (ifn (ifn-inverse y)) y)))
  :hints (("Goal"
	   :use ((:instance ifn-inverse (x (ifn-is-onto-predicate-witness y)) (y y))
		 (:instance ifn-is-onto-predicate (y y))))))

(defthm ifn-inverse-is-real
    (realp (ifn-inverse y))
  :hints (("Goal"
	   :cases ((ifn-range-p y)))
	  ("Subgoal 2"
	   :use ((:instance ifn-inverse
			    (x 0)
			    (y y)))))
  :rule-classes (:rewrite :type-prescription)
  )

(defthm ifn-inverse-unique
    (implies (and (ifn-range-p y)
		  (ifn-domain-p x)
		  (equal (ifn x) y))
	     (equal (ifn-inverse y) x))
  :hints (("Goal"
	   :use ((:instance ifn-inverse-exists (y y))
		 (:instance ifn-is-1-1 (x1 x) (x2 (ifn-inverse y)))
		 ))))

(defthm ifn-inverse-inverse-exists
    (implies (ifn-domain-p x)
	     (equal (ifn-inverse (ifn x)) x))
  :hints (("Goal"
	   :use ((:instance ifn-inverse-unique
			    (x x)
			    (y (ifn x))))
	   :in-theory (disable ifn-inverse-unique))))

(defthm ifn-inverse-is-1-to-1
    (implies (and (ifn-range-p y1)
		  (ifn-range-p y2)
		  (equal (ifn-inverse y1)
			 (ifn-inverse y2)))
	     (equal y1 y2))
  :hints (("Goal"
	   :use ((:instance ifn-inverse-exists (y y1))
		 (:instance ifn-inverse-exists (y y2)))
	   :in-theory (disable ifn-inverse-exists)))
  :rule-classes nil)
