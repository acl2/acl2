(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "inverse-monotone")

(defun square (x)
  (realfix (* x x)))

(defun square-interval (y)
  (if (< 1 y)
      (interval 1 y)
      (interval 0 1)))

(defthm square-is-continuous
    (IMPLIES (AND (STANDARDP X1)
		  (realp x1)
		  (I-CLOSE X1 X2)
		  (realp x2))
	     (I-CLOSE (* X1 X1) (* X2 X2)))
  :hints (("Goal"
	   :use ((:instance i-close-to-small-sum
			    (x   (* x1 x1))
			    (eps (+ (* x1 (- x2 x1))
				    (* x1 (- x2 x1))
				    (* (- x2 x1) (- x2 x1)))))
		 (:instance small*limited->small
			    (x (- x2 x1))
			    (y x1))
		 (:instance small*limited->small
			    (x (- x2 x1))
			    (y (- x2 x1)))
		 (:instance i-small-uminus
			    (x (- x2 x1)))
		 (:instance i-small-uminus
			    (x (- (* x2 x2) (* x1 x1))))
		 (:instance i-small-plus
			    (x (+ (* x1 (- x2 x1))
				  (* x1 (- x2 x1))))
			    (y (* (- x2 x1) (- x2 x1))))
		 (:instance i-small-plus
			    (x (* x1 (- x2 x1)))
			    (y (* x1 (- x2 x1))))
		 )
	   :in-theory (disable i-close-to-small-sum small*limited->small i-small-uminus i-small-plus)
	   )
	  ("Subgoal 5"
	   :in-theory (enable i-close))
	  ("Subgoal 4"
	   :in-theory (enable i-close))
	  ("Subgoal 3"
	   :in-theory (enable i-close))
	  ("Subgoal 2"
	   :in-theory (enable i-close))
	  ("Subgoal 1"
	   :in-theory (enable i-close))
	  ))

(local
 (defthm square-lemma-1
     (IMPLIES (INSIDE-INTERVAL-P Y (INTERVAL 0 NIL))
	      (<= 0 Y))
   :hints (("Goal"
	    :use ((:instance inside-interval-p->=-left-endpoint
			     (x y)
			     (interval (interval 0 nil))))
	    :in-theory (disable inside-interval-p->=-left-endpoint)))))

(local
 (defthm square-lemma-2
     (IMPLIES (AND (INSIDE-INTERVAL-P Y (INTERVAL 0 NIL))
              (< 1 Y))
         (SUBINTERVAL-P (INTERVAL 1 Y)
                        (INTERVAL 0 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm square-lemma-3
     (IMPLIES (AND (INSIDE-INTERVAL-P Y (INTERVAL 0 NIL))
		   (<= Y 1))
	      (SUBINTERVAL-P (INTERVAL 0 1)
			     (INTERVAL 0 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)
   ))

(local
 (defthm square-lemma-4
     (IMPLIES (AND (realp x1)
		   (realp x2)
		   (<= 0 x1)
		   (< x1 x2))
	      (< (* X1 X1) (* X2 X2)))
   :hints (("Goal"
	    :cases ((< 0 x1))))))

(local
 (defthm square-lemma-6
     (IMPLIES (AND (inside-interval-p x1 (interval 0 nil))
		   (inside-interval-p x2 (interval 0 nil))
		   (equal (* X1 X1) (* X2 X2)))
	      (equal x1 x2))
   :hints (("Goal"
	    :use ((:instance square-lemma-4
			     (x1 x1)
			     (x2 x2))
		  (:instance square-lemma-4
			     (x1 x2)
			     (x2 x1)))
	    :in-theory (disable square-lemma-4)))
   :rule-classes (:built-in-clause)))

(local
 (defthm square-lemma-7
     (IMPLIES (INSIDE-INTERVAL-P X (INTERVAL 0 NIL))
         (INSIDE-INTERVAL-P (* X X)
                            (INTERVAL 0 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)))

(definv square :domain (interval 0 nil) :range (interval 0 nil) :inverse-interval square-interval)

(include-book "sqrt")

(local
 (defthm rewrite-interval-0-nil
     (equal (inside-interval-p x (interval 0 nil))
	    (and (realp x)
		 (<= 0 x)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(defthm square-inverse->sqrt
    (implies (inside-interval-p y (interval 0 nil))
	     (equal (square-inverse y)
		    (acl2-sqrt y)))
  :hints (("Goal"
	   :use ((:instance sqrt-sqrt (x y))
		 (:instance square-inverse-unique (x (acl2-sqrt y)) (y y)))
	   :in-theory (disable sqrt-sqrt square-inverse-unique))))
