;; This book defines the regular norm on complex numbers.  It also
;; proves some very interesting properties about it.  Besides the
;; usual well-known properties, it establishes that norm preserves the
;; non-standard "magnitude" predicates (i-small, i-limited, and
;; i-large) and so we can reduce the question of when x is i-large to
;; when norm(x) is i-large.  Since many useful results were found for
;; the special case when x is real, asking the magnitude question on a
;; real number is easier than on a complex number -- and this norm
;; lets us do just that.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")
(include-book "sqrt")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; We start by defining the traditional norm and then proving some
;; important properties about it.

(encapsulate
 ()

 ;; The norm(a+bi) = sqrt(a^2 + b^2).  To show that this is a valid
 ;; norm, we need three properties.  norm(x) is real and norm(x)>=0,
 ;; norm(x)=0 iff x=0, and norm(x+y) <= norm(x) + norm(y).

 (defun norm-2C (x)
   (acl2-sqrt (+ (* (realpart x) (realpart x))
		 (* (imagpart x) (imagpart x)))))

 (in-theory (disable (:executable-counterpart norm-2c)))

 ;; Here is the first property, norm(x) is real and norm(x)>=0.

 (defthm norm-2C-non-negative-real
   (and (realp (norm-2C x))
	(<= 0 (norm-2C x)))
   :rule-classes (:rewrite :type-prescription))

 ;; To prove that norm(x)=0 only when x=0, we have to establish this
 ;; simple lemma first, which lets us decide when a term of the form
 ;; a+bi is equal to zero -- namely a=0 and b=0:

 (local
  (defthm equal-complex-0
    (iff (equal (complex r s) 0)
	 (and (equal (realfix r) 0)
	      (equal (realfix s) 0)))))

 ;; So now, we establish the second key property of norm-ness, namely
 ;; that norm(x)=0 if and only if x=0.

 (defthm norm-2C-zero-for-zero-only
   (and (equal (norm-2C 0) 0)
	(iff (equal (norm-2C x) 0)
	     (equal (fix x) 0))))

 ;; It turns out that we want some more values of norm.  We establish,
 ;; for example that norm(1) = 1.  This will become real useful later,
 ;; when we find that norm(x*y) = norm(x)*norm(y).

 (defthm norm-2C-one
   (equal (norm-2C 1) 1))

 ;; We also have that norm(2) = 2.

 (defthm norm-2C-two
   (equal (norm-2C 2) 2))

 ;; The following sequence of theorems indicate how poor ACL2 is in
 ;; reasoning about the complex numbers.  This first one simply says
 ;; how to add complex numbers.

 (local
  (defthm +-complex
    (implies (and (realp i) (realp j) (realp r) (realp s))
	     (equal (+ (complex i j) (complex r s))
		    (complex (+ i r) (+ j s))))
    :hints (("Goal"
	     :use ((:instance complex-definition (x i) (y j))
		   (:instance complex-definition (x r) (y s))
		   (:instance complex-definition (x (+ i r)) (y (+ j s))))))))

 ;; Next, we'll look at multiplying complex numbers.  Here's the first
 ;; step in multiplying (a+bi) * (r+si)....

 (local
  (defthm *-complex-lemma-1
    (implies (and (realp a) (realp b) (realp r) (realp s))
	     (equal (* (complex a b) (complex r s))
		    (* (+ a (* #C(0 1) b)) (+ R (* #C(0 1) S)))))
    :hints (("Goal"
	     :use ((:instance complex-definition (x a) (y b))
		   (:instance complex-definition (x r) (y s)))))))

 ;; ...the next step is to factor everything out, remembering that
 ;; i^2=-1....

 (local
  (defthm *-complex-lemma-2
    (implies (and (realp a) (realp b) (realp r) (realp s))
	     (equal (complex (- (* a r) (* b s))
			     (+ (* a s) (* b r)))
		    (+ (+ (* a R) (- (* b S)))
		       (* #C(0 1) (+ (* a S) (* b R))))))
    :hints (("Goal"
	     :use ((:instance complex-definition
			      (x (- (* a r) (* b s)))
			      (y (+ (* a s) (* b r)))))))))

 ;; And so now we can get a formula for the product of two complex
 ;; numbers.

 (local
  (defthm *-complex
    (implies (and (realp i) (realp j) (realp r) (realp s))
	     (equal (* (complex i j) (complex r s))
		    (complex (- (* i r) (* j s))
			     (+ (* i s) (* j r)))))))

 (local
  (in-theory (disable *-complex-lemma-1 *-complex-lemma-2)))

 ;; Here's a simple theorem.  if a+bi is real, then b is zero and a is
 ;; equal to a+bi.

 (local
  (defthm realpart-imagpart-reals
    (implies (realp x)
	     (and (equal (realpart x) x)
		  (equal (imagpart x) 0)))))

 ;; This simplification let's us get the realpart/imagpart of the sum
 ;; of two complex numbers.

 (local
  (defthm realpart-imagpart-+
    (and
     (equal (realpart (+ x y))
	    (+ (realpart x) (realpart y)))
     (equal (imagpart (+ x y))
	    (+ (imagpart x) (imagpart y))))))

 ;; This is a similar rule for the product of two complex numbers.

 (local
  (defthm realpart-imagpart-*
    (and
     (equal (realpart (* x y))
	    (- (* (realpart x) (realpart y))
	       (* (imagpart x) (imagpart y))))
     (equal (imagpart (* x y))
	    (+ (* (realpart x) (imagpart y))
	       (* (imagpart x) (realpart y)))))))

 ;; Now, we can move more quickly.  We prove that norm is an
 ;; idempotent function; i.e., norm(norm(x)) = norm(x).

 (defthm norm-2C-norm-2C
   (equal (norm-2C (norm-2C x))
	  (norm-2C x)))

 ;; Moreover, norm is monotonic over the reals.

 (defthm norm-2C-preserves-<=-for-reals
   (implies (and (realp x)
		 (realp y)
		 (<= 0 x)
		 (<= x y))
	    (<= (norm-2C x) (norm-2C y))))

 ;; And finally, we can establish that norm(x*y) = norm(x)*norm(y).

 (defthm norm-2C-product
   (equal (norm-2C (* a b))
	  (* (norm-2C a) (norm-2C b)))
   :instructions
   ((:DV 1)
    (:= (ACL2-SQRT (+ (* (REALPART (* A B))
			 (REALPART (* A B)))
		      (* (IMAGPART (* A B))
			 (IMAGPART (* A B))))))
    :NX :UP (:REWRITE SQRT-=-Y)
    :S))

 ;; Next on the agenda are terms of the form norm(ax+bx) where a and b
 ;; are reals.

 (defthm norm-2C-distributivity
   (implies (and (realp a)
		 (<= 0 a)
		 (realp b)
		 (<= 0 b))
	    (equal (norm-2C (+ (* a x) (* b x)))
		   (+ (* (norm-2C a) (norm-2C x))
		      (* (norm-2C b) (norm-2C x))))))

 ;; The term abs(norm(x)) can be simplified to norm(x) since norm is a
 ;; non-negative real.

 (local
  (defthm abs-norm-2c
    (equal (abs (norm-2c x))
	   (norm-2c x))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; Another silly theorem showing how to get the realpart/imagpart of
 ;; the negative of a number.

 (local
  (defthm realpart-imagpart-uminus
    (and (equal (realpart (- x)) (- (realpart x)))
	 (equal (imagpart (- x)) (- (imagpart x))))
    :hints (("Goal" :use ((:instance realpart-imagpart-* (x -1) (y x)))
	     :in-theory (disable realpart-imagpart-*)))))

 ;; That shows that norm(-x) is the same as norm(x).....

 (local
  (defthm norm-2C-uminus
    (equal (norm-2C (- x)) (norm-2C x))))

 ;; And now, we get an important lemma.  The norm(a+bi) cannot be smaller
 ;; than either a or b.  What this will mean later is that if a+bi
 ;; isn't small, then norm(a+bi) can't be small, since one of a or b
 ;; is not small, and norm(a+bi) is at least that large.

 (local
  (defthm realpart-imagpart-<=-norm
    (and (<= (realpart x) (norm-2C x))
	 (<= (imagpart x) (norm-2C x)))
    :hints (("Subgoal 2'"
	     :use ((:instance sqrt-<-y
			      (x (+ (* (imagpart x) (imagpart x))
				    (* (realpart x) (realpart x))))
			      (y (realpart x))))
	     :in-theory (disable sqrt-<-y))
	    ("Subgoal 1'"
	     :use ((:instance sqrt-<-y
			      (x (+ (* (imagpart x) (imagpart x))
				    (* (realpart x) (realpart x))))
			      (y (imagpart x))))
	     :in-theory (disable sqrt-<-y)))))

 ;; Actually, we can prove a stronger result.  Not only is
 ;; a<=norm(a+bi), |a|<=norm(a+bi)....

 (local
  (defthm abs-realpart-imagpart-<=-norm-2c
    (and (<= (abs (realpart x)) (norm-2c x))
	 (<= (abs (imagpart x)) (norm-2c x)))
    :hints (("Goal" :in-theory (enable-disable (abs) (norm-2c)))
	    ("Subgoal 2.2"
	     :use ((:instance realpart-imagpart-<=-norm
			      (x (- x))))
	     :in-theory (disable norm-2c realpart-imagpart-<=-norm))
	    ("Subgoal 1.2"
	     :use ((:instance realpart-imagpart-<=-norm
			      (x (- x))))
	     :in-theory (disable norm-2c realpart-imagpart-<=-norm)))))

 ;; So now, like we argued earlier we see that if norm(a+bi) is small,
 ;; both a and b must be small.

 (local
  (defthm small-norm-2C-lemma-1
    (implies (i-small (norm-2C x))
	     (and (i-small (realpart x))
		  (i-small (imagpart x))))
    :hints (("Goal"
	     :use ((:instance small-if-<-small
			      (x (norm-2C x))
			      (y (realpart x)))
		   (:instance small-if-<-small
			      (x (norm-2C x))
			      (y (imagpart x))))
	     :in-theory (disable abs small-if-<-small norm-2c)))))

 ;; And here's the other half of that important theorem.  We know
 ;; norm(a+bi) must be larger than |a| and |b|, but it can't be too
 ;; much bigger.  In particular,  norm(a+bi) <= |a| + |b|.  What this
 ;; means later is that if norm(a+bi) is large, so must be either a or
 ;; b.

 (local
  (defthm norm-2c-<=-abs-realpart-+-abs-imagpart
    (<= (norm-2c x)
	(+ (abs (realpart x)) (abs (imagpart x))))))

 ;; For now, we content ourselves with completing the proofs for
 ;; i-small.  If x and y are small, so are abs(x) and abs(y), and
 ;; therefore abs(x)+abs(y) is small.

 (local
  (defthm small-abs-x-+-abs-y
    (implies (and (i-small x)
		  (i-small y))
	     (i-small (+ (abs x) (abs y))))))

 ;; Moreover, abs(x)+abs(y) is real, if both x and y are real.

 (local
  (defthm realp-abs-x-+-abs-y
    (implies (and (realp x)
		  (realp y))
	     (realp (+ (abs x) (abs y))))))

 ;; And since we find the term abs(abs(x)+abs(y)) in the proofs to
 ;; follow, we show here that that must equal abs(x)+abs(y).

 (local
  (defthm abs-abs-x-+-abs-y
    (equal (abs (+ (abs x) (abs y)))
	   (+ (abs x) (abs y)))))

 ;; When x isn't a number, its norm is the same as the norm of 0,
 ;; which is 0.

 (local
  (defthm norm-2c-non-numberp
    (implies (not (acl2-numberp x))
	     (equal (norm-2c x) 0))))

 ;; So now we get the converse of our i-small lemma.  We already know
 ;; that when norm(a+bi) is small, both a and b are small.  Now, we
 ;; show that if both a and b are small, norm(a+bi) is small.

 (local
  (defthm small-norm-2C-lemma-2
    (implies (and (i-small (realpart x))
		  (i-small (imagpart x)))
	     (i-small (norm-2C x)))
    :hints (("Goal"
	     :use (:instance small-if-<-small
			     (x (+ (abs (realpart x)) (abs (imagpart x))))
			     (y (norm-2c x)))
	     :in-theory (disable abs small-if-<-small norm-2c)))))

 ;; And that allows us to prove that norm(x) is small precisely when x
 ;; is small.

 (defthm small-norm-2C
   (implies (acl2-numberp x)
	    (equal (i-small (norm-2C x))
		   (i-small x)))
   :hints (("Goal"
	    :use ((:instance complex-small))
	    :in-theory (disable norm-2C complex-small))
	   ("Goal'"
	    :cases ((i-small x)))
	   ("Subgoal 2''"
	    :in-theory (enable norm-2c))
	   ("Subgoal 1'''"
	    :in-theory (enable norm-2c))))

 ;; Similarly, if norm(a+bi) is limited, so must be both a and b,
 ;; since they're both smaller than norm(a+bi).

 (local
  (defthm limited-norm-2C-lemma-1
    (implies (i-limited (norm-2C x))
	     (and (i-limited (realpart x))
		  (i-limited (imagpart x))))
    :hints (("Goal"
	     :use ((:instance large-if->-large
			      (x (realpart x))
			      (y (norm-2C x)))
		   (:instance large-if->-large
			      (x (imagpart x))
			      (y (norm-2C x))))
	     :in-theory (disable large-if->-large norm-2c)))))

 ;; And moreover, if x and y are limited, so is |x|+|y|....

 (local
  (defthm limited-abs-x-+-abs-y
    (implies (and (i-limited x)
		  (i-limited y))
	     (i-limited (+ (abs x) (abs y))))))

 ;; ...and so if a and b are limited, so is norm(a+bi), since that is
 ;; smaller than |a|+|b|.

 (local
  (defthm limited-norm-2C-lemma-2
    (implies (and (i-limited (realpart x))
		  (i-limited (imagpart x)))
	     (i-limited (norm-2C x)))
    :hints (("Goal"
	     :use (:instance large-if->-large
			     (x (norm-2c x))
			     (y (+ (abs (realpart x)) (abs (imagpart x)))))
	     :in-theory (disable abs large-if->-large norm-2c)))))


 ;; We know that a+bi is limited precisely when a is limited and b is
 ;; limited.

 (local
  (defthm complex-limited-strong
    (implies (complexp x)
	     (equal (i-large x)
		    (or (i-large (realpart x))
			(i-large (imagpart x)))))
    :hints (("Goal"
	     :use ((:instance complex-large-1)
		   (:instance complex-large-2))
	     :in-theory (disable complex-large-1)))))

 ;; Therefore, norm(a+bi) is limited precisely when a+bi is limited.

 (defthm limited-norm-2C
   (implies (acl2-numberp x)
	    (equal (i-large (norm-2C x))
		   (i-large x)))
   :hints (("Goal"
	    :use ((:instance complex-limited-strong))
	    :in-theory (disable norm-2C complex-limited-strong
				complex-large-1))
	   ("Goal'"
	    :cases ((i-limited x)))
	   ("Subgoal 2''"
	    :in-theory (enable norm-2c))))

 ;; This simple lemma lets us conclude that a^2+b^2 is limited when
 ;; a+bi is limited.

 (local
  (defthm limited-r*r+s*s
    (implies (and (realp r)
		  (realp s)
		  (i-limited (complex r s)))
	     (i-limited (+ (* r r) (* s s))))
    :hints (("Goal" :cases ((= s 0))))))

 ;; Here's a great theorem!  Standard-part and norm commute!  This is
 ;; actually true of all continuous functions.  I.e.,
 ;; fn(standard-part(x)) is just standard-part(fn(x)).

 (defthm standard-part-norm-2C
   (implies (i-limited x)
	    (equal (standard-part (norm-2C x))
		   (norm-2C (standard-part x))))
   :hints (("Goal" :in-theory (disable acl2-sqrt))
; Matt K. v7-1 mod for ACL2 mod on 2/13/2015: "Goal'5'" changed to "Goal'4'".
	   ("Goal'4'" :cases ((= s 0)))))

 ;; Now, we want to talk about the inverses of complex numbers, so we
 ;; start by defining conjugates.

 (local
  (defun conj (x)
    (complex (realpart x) (- (imagpart x)))))

 ;; We can then give a simpler definition of norm(x) as sqrt(x*x')
 ;; where x' is the conjugate of x.

 (local
  (defthm norm-2c-product-conj
    (equal (norm-2c x)
	   (acl2-sqrt (* x (conj x))))))

 ;; Next, we build up the basic theory of conjugates...the conjugate
 ;; of a sum is the sum of the conjugates...

 (local
  (defthm conj-+
    (equal (conj (+ x y))
	   (+ (conj x) (conj y)))))

 ;; ...and the same holds for products.

 (local
  (defthm conj-*
    (equal (conj (* x y))
	   (* (conj x) (conj y)))))

 ;; Next, we show that realpart(x+x') is just 2*realpart(x).

 (local
  (defthm x-+-conj-x
    (equal (+ x (conj x))
	   (* 2 (realpart x)))))

 ;; An easy lemma is that norm(x') = norm(x)

 (local
  (defthm norm-2C-conj
    (equal (norm-2c (conj x))
	   (norm-2c x))))

 ;; Another one is that x'' = x

 (local
  (defthm conj-conj
    (equal (conj (conj x)) (fix x))))

 ;; So now, we can start considering x*x'.  First, we have that it is
 ;; always real and never negative.

 (local
  (defthm x-*-conj-x-type-prescription
    (and (realp (* x (conj x)))
	 (<= 0 (* x (conj x))))
    :rule-classes (:rewrite :type-prescription)))

 ;; Moreover, if x isn't anumber, then x' is just 0.

 (local
  (defthm conj-completion
    (implies (not (acl2-numberp x))
	     (equal (conj x) 0))))

 ;; Here's another characterization of the conjugate:

 (local
  (defthm realpart-imagpart-conj
    (and (equal (realpart (conj x)) (realpart x))
	 (equal (imagpart (conj x)) (- (imagpart x))))))

 (local (in-theory (disable conj)))

 ;; So now, we can prove that norm(x)*norm(x) = x*x' -- since earlier
 ;; we saw that norm(x)=sqrt(x*x')....

 (local
  (defthm norm-2c-*-norm-2c
    (equal (* (norm-2c x) (norm-2c x))
	   (* x (conj x)))))

 ;; Now, from norm(x+y)*norm(x+y) = (x+y)*(x+y)', we get that is equal
 ;; to xx' + yy' + xy' + x'y = xx' + yy' + xy' + (xy')' =
 ;; norm(x)*norm(x) + norm(y)*norm(y) + 2*realpart(xy')

 (local
  (defthm norm-2c-triangle-inequality-lemma-1
    (equal (* (norm-2c (+ x y)) (norm-2c (+ x y)))
	   (+ (* (norm-2c x) (norm-2c x))
	      (* (norm-2c y) (norm-2c y))
	      (* 2 (realpart (* x (conj y))))))
    :hints (("Goal"
	     :use (:instance x-+-conj-x (x (* x (conj y))))
	     :in-theory (disable x-+-conj-x)))))

 ;; That means we need to find a bound for the 2*realpart(xy') term.
 ;; We know this is smaller than 2*norm(x*y')

 (local
  (defthm norm-2c-triangle-inequality-lemma-key
    (implies (and (realp i) (realp j)
		  (realp r) (realp s))
	     (<= (+ (* 2 i r) (* 2 j s))
		 (* 2 (norm-2c (* (complex i j) (conj (complex r s)))))))
    :hints (("Goal"
	     :use ((:instance realpart-imagpart-<=-norm
			      (x (* (complex i j) (conj (complex r s))))))
	     :in-theory (disable realpart-imagpart-<=-norm)))
    :rule-classes nil))

 ;; We're ready to prove the third law required for norms, namely
 ;; norm(a+b) <= norm(a) + norm(b).  First, we square each side to get
 ;; rid of the sqrt's

 (local
  (defthm norm-2c-triangle-inequality-lemma
    (<= (* (norm-2c (+ x y)) (norm-2c (+ x y)))
	(* (+ (norm-2c x) (norm-2c y))
	   (+ (norm-2c x) (norm-2c y))))
    :hints (("Goal" :in-theory (disable norm-2c
					norm-2c-*-norm-2c
					norm-2c-product-conj))
	    ("Subgoal 2"
	     :in-theory (enable norm-2c-product-conj))
	    ("Subgoal 1.1'"
	     :use ((:instance norm-2c-triangle-inequality-lemma-key))))))

; Added by Matt K., 1/14/2014:
; The following two lemmas are the versions of lemmas that existed though the
; time of the ACL2 6.4 release.  The new versions, whose conclusions are calls
; of equal instead of iff, cause the proof of lemma-1 below to fail; so we
; :use these old ones instead.

  (local
   (defthm <-*-right-cancel-old
     (implies (and (fc (real/rationalp x))
                   (fc (real/rationalp y))
                   (fc (real/rationalp z)))
              (iff (< (* x z) (* y z))
                   (cond ((< 0 z)     (< x y))
                         ((equal z 0) nil)
                         (t           (< y x)))))
     :rule-classes nil))

  (local
   (defthm <-*-left-cancel-old
     (implies (and (fc (real/rationalp x))
                   (fc (real/rationalp y))
                   (fc (real/rationalp z)))
              (iff (< (* z x) (* z y))
                   (cond ((< 0 z)     (< x y))
                         ((equal z 0) nil)
                         (t           (< y x)))))
     :rule-classes nil))

 ;; This is a trivial lemma that we need below.... x<y => x^2 < y^2
 ;; for positive x, y.

 (local
  (defthm obvious-lemma
    (implies (and (realp x)
		  (realp y)
		  (<= 0 x)
		  (<= 0 y)
		  (< x y))
	     (< (* x x) (* y y)))
    :hints (("Goal"
	     :use ((:instance <-*-left-cancel-old (x x) (y y) (z x))
		   (:instance <-*-right-cancel-old (x x) (y y) (z y)))
	     :in-theory (disable <-*-left-cancel <-*-right-cancel)))))

 ;; And finally, we establish the triangle inequality:

 (defthm norm-2c-triangle-inequality
   (<= (norm-2c (+ x y))
       (+ (norm-2c x) (norm-2c y)))
   :hints (("Goal"
	    :use ((:instance obvious-lemma
			     (x (+ (norm-2c x) (norm-2c y)))
			     (y (norm-2c (+ x y)))))
	    :in-theory (disable obvious-lemma
				norm-2c-product-conj
				norm-2c-*-norm-2c))))
 )

;; The next step is to create an abstract "norm", using the specific
;; norm defined above as a witness.  Why?  Well, there's no good
;; reason really, but what we had in mind was that you could swap in a
;; different norm later.  Unfortunately, we needed so many theorems
;; about the norm, that it's hard to think of another function with
;; these same properties.

(encapsulate
 ((norm (x) t))

 ;; Use the norm defined above as the witness function, and turn off
 ;; its definition, so we are left only with the theorems exported
 ;; above.

 (local
  (defun norm (x)
    (norm-2C x)))

 (local (in-theory (disable norm-2C
			    (:executable-counterpart norm)
			    (:executable-counterpart norm-2C))))

 ;; The norm is a real >= 0....

 (defthm norm-non-negative-real
   (and (realp (norm x))
	(<= 0 (norm x)))
   :rule-classes (:rewrite :type-prescription))

 ;; ...and norm(x) is equal to zero only when x is zero.

 (defthm norm-zero-for-zero-only
   (and (equal (norm 0) 0)
	(iff (equal (norm x) 0)
	     (equal (fix x) 0))))

 ;; norm(1) = 1 and norm(2) = 2....

 (defthm norm-one
   (equal (norm 1) 1))

 (defthm norm-two
   (equal (norm 2) 2))

 ;; norm is idempotent.

 (defthm norm-norm
   (equal (norm (norm x))
	  (norm x)))

 ;; norm(a+b) <= norm(a)+norm(b)

 (defthm norm-triangle-inequality
   (<= (norm (+ a b))
       (+ (norm a) (norm b))))

 ;; if x,y are reals and x<=y, then norm(x)<=norm(y)

 (defthm norm-preserves-<=-for-reals
   (implies (and (realp x)
		 (realp y)
		 (<= 0 x)
		 (<= x y))
	    (<= (norm x) (norm y))))

 ;; norm(x*y) = norm(x)*norm(y)

 (defthm norm-product
   (equal (norm (* a b))
	  (* (norm a) (norm b))))

 ;; norm(ax+bx) = norm(a)*norm(x) + norm(b)*norm(x)

 (defthm norm-distributivity
   (implies (and (realp a)
		 (<= 0 a)
		 (realp b)
		 (<= 0 b))
	    (equal (norm (+ (* a x) (* b x)))
		   (+ (* (norm a) (norm x))
		      (* (norm b) (norm x))))))

 ;; These are important properties for non-standard analysis.  norm(x)
 ;; is small precisely when x is small.

 (defthm small-norm
   (implies (acl2-numberp x)
	    (equal (i-small (norm x))
		   (i-small x))))

 ;; Similarly, norm(x) is limited precisely when x is limited.

 (defthm limited-norm
   (implies (acl2-numberp x)
	    (equal (i-large (norm x))
		   (i-large x))))

 ;; And, the standard-part of norm(x) is the same as the norm of
 ;; stadard-part(x).

 (defthm standard-part-norm
   (implies (i-limited x)
	    (equal (standard-part (norm x))
		   (norm (standard-part x)))))
 )
