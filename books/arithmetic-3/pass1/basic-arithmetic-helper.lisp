; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;
;; basic-arithmetic-helper.lisp
;;

;; RK 3/15/99 The following is copied from the books of Cowles
;; and adapted to the needs at hand.

(in-package "ACL2")


(encapsulate
 ()

 (local
  (defthm commutativity-2-of-*-lemma
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (acl2-numberp z))
	     (equal (* (* x y) z)
		    (* (* y x) z)))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable associativity-of-*)))))

 (defthm commutativity-2-of-*
   (equal (* x (* y z))
          (* y (* x z)))
   :hints
   (("Goal"
     :use commutativity-2-of-*-lemma)))

)

(encapsulate
 ()

 (local
  (defthm equiv-1-implies-equiv-*
    (implies (equal x1 x2)
	     (equal (* x1 y)
		    (* x2 y)))
    :rule-classes nil))

 (defthm right-cancellation-for-*
   (equal (equal (* x z) (* y z))
	  (or (equal 0 (fix z))
	      (equal (fix x) (fix y))))
    :hints (("Subgoal 9"
             :use (:instance
                   equiv-1-implies-equiv-*
                   (x1 (* x z))
                   (x2 (* y z))
                   (y  (/ z))))))

)

(encapsulate
 ()

 (local
  (defthm uniqueness-of-*-inverses-lemma
    (implies (and (acl2-numberp x)
		  (not (equal x 0))
		  (acl2-numberp y)
		  (equal (* x y)
			 1))
	     (equal (/ x) y))
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   right-cancellation-for-*
		   (x y)
		   (y (/ x))
		   (z x))))))

 (defthm equal-/
   (equal (equal (/ x) y)
	  (if (not (equal (fix x) 0))
	      (equal 1 (* x y))
	      (equal y 0)))
     :hints (("Goal" :use uniqueness-of-*-inverses-lemma)))

)

(defthm functional-self-inversion-of-/
  (equal (/ (/ x)) (fix x)))

(encapsulate
 ()

 (local
  (defthm distributivity-of-/-over-*-lemma
    (implies (and (acl2-numberp x)
		  (not (equal x 0))
		  (acl2-numberp y)
		  (not (equal y 0)))
	     (equal (/ (* x y))
		    (* (/ x) (/ y))))
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   equal-/
		   (x (* x y))
		   (y (* (/ x) (/ y))))))))

 (defthm distributivity-of-/-over-*
   (equal (/ (* x y))
	  (* (/ x) (/ y)))
   :hints (("Goal"
	    :use distributivity-of-/-over-*-lemma)))

)

(encapsulate
 ()

 (local
  (defthm uniqueness-of-+-inverses-lemma
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (equal (+ x y)
			 0))
	     (equal (- x) y))
  :rule-classes nil))

  (defthm functional-commutativity-of-minus-*-right
      (implies (syntaxp (not (quotep y)))
               (equal (* x (- y))
                      (- (* x y))))
    :hints (("Goal"
	     :use ((:instance
		    Uniqueness-of-+-inverses-lemma
		    (x (* x y))
		    (y (* x (- y))))
		   (:instance
		    distributivity
		    (z (- y)))))))
)

(encapsulate
 ()

 (local
  (defthm equal-/-/-lemma
    (implies
     (and (acl2-numberp a)
	  (acl2-numberp b)
	  (not (equal a 0))
	  (not (equal b 0)))
     (equal (equal (/ a) (/ b))
	    (equal a b)))
    :rule-classes nil
    :hints
    (("Goal"
      :use ((:instance
	     (:theorem
	      (implies
	       (and (acl2-numberp a)
		    (acl2-numberp b)
		    (not (equal a 0))
		    (not (equal b 0)))
	       (implies (equal a b)
			(equal (/ a) (/ b)))))
	     (a (/ a)) (b (/ b))))))))

 (defthm equal-/-/
   (equal (equal (/ a) (/ b))
	  (equal (fix a) (fix b)))
   :hints (("Goal" :use equal-/-/-lemma)))

)
