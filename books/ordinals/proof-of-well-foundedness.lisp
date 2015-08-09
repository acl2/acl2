#|
We perform the proofs in another package, so that o< and o-p as
defined in ACL2 won't interfere.

To certify this book:

(in-package "ACL2")

(defpkg "ORD" (set-difference-eq *acl2-exports*
				 '(o< o<= o-p)))

(certify-book "proof-of-well-foundedness" 1)
|#

(in-package "ORD")

#|

Since ACL2's sense of well-foundedness is based on o<, we need to
prove that we can embed the natural numbers into the ordinals.
This is trivial since all natural numbers are ordinals.

Proving we can embed the natural numbers in the ordinals allows
us to set ACL2's well-founded relation to be <. Thus all
termination proofs will be done using < on the natural numbers,
instead of o<. Thus, none of our proof will depend on the
well-foundedness of o<.

|#

(defun id (x) x)

(defthm well-foundedness-of-natural-numbers
  (and (implies (natp x) (ACL2::o-p (id x)))
       (implies (and (natp x)
                     (natp y)
                     (< x y))
                (ACL2::o< (id x) (id y))))
  :rule-classes :well-founded-relation)

(set-well-founded-relation <)

#|

The following definitions of o< and o-p are identical to those in
ACL2. We redefine them here to show that ACL2 can admit them and
prove that they terminate using only < over the natural numbers.

|#

(defun o< (x y)
  (cond ((o-finp x)
         (or (o-infp y) (< x y)))
        ((o-finp y) nil)
        ((not (equal (o-first-expt x) (o-first-expt y)))
         (o< (o-first-expt x) (o-first-expt y)))
        ((not (= (o-first-coeff x) (o-first-coeff y)))
         (< (o-first-coeff x) (o-first-coeff y)))
        (t (o< (o-rst x) (o-rst y)))))

(defun o-p (x)
  (if (o-finp x)
      (natp x)
    (and (consp (car x))
         (o-p (o-first-expt x))
         (not (eql 0 (o-first-expt x)))
         (posp (o-first-coeff x))
         (o-p (o-rst x))
	 (o< (o-first-expt (o-rst x))
	     (o-first-expt x)))))

#|

The following are lemmas that help us prove the main results of
the theorem.

|#

(defthm |~(a < a)|
  (not (o< a a)))

(defthm |~(a < b) & ~(a = b)  =>  a < b|
  (implies (and (not (equal a b))
		(not (o< b a))
		(o-p a)
		(o-p b))
	   (o< a b))
  :rule-classes :forward-chaining)

(defthm |a < b  =>  ~(b < a) & ~(a = b)|
  (implies (o< a b)
           (and (not (o< b a))
                (not (equal a b))))
  :rule-classes :forward-chaining)

(defthm o-infp-o-finp-not-o<
  (implies (and (o-infp a)
		(o-finp b))
	   (not (o< a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

#|

Now we can prove the theorems that appear in the proof of well-foundedness:

|#

(defthm transitivity-of-o<
  (implies (and (o< x y)
                (o< y z))
           (o< x z))
  :rule-classes nil)

(defthm non-circularity-of-o<
  (implies (o< x y)
           (not (o< y x)))
  :rule-classes nil)

(defthm trichotomy-of-o<
  (implies (and (o-p x)
                (o-p y))
           (or (equal x y)
               (o< x y)
               (o< y x)))
  :rule-classes nil)

#|

These three properties establish that o< orders the o-ps. To put
such a statement in the most standard mathematical nomenclature,
we can define the macro:

|#

(defmacro o<= (x y)
  `(not (o< ,y ,x)))

#|

and then establish that o<= is a relation that is a simple,
complete (i.e., total) order on ordinals by the following three
lemmas:

|#

(defthm antisymmetry-of-o<=
  (implies (and (o-p x)
                (o-p y)
                (o<= x y)
                (o<= y x))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use non-circularity-of-o<)))

(defthm transitivity-of-o<=
  (implies (and (o-p x)
                (o-p y)
                (o<= x y)
                (o<= y z))
           (o<= x z))
  :rule-classes nil
  :hints (("Goal" :use transitivity-of-o<)))

(defthm trichotomy-of-o<=
  (implies (and (o-p x)
                (o-p y))
           (or (o<= x y) (o<= y x)))
  :rule-classes nil
  :hints (("Goal" :use trichotomy-of-o<)))

#|

Crucially important to the proof of the well-foundedness of o< on
o-ps is the concept of ordinal-depth, abbreviated od:

|#

(defun od (l)
  (if (o-finp l)
      0
    (1+ (od (o-first-expt l)))))

#|

If the od of an o-p x is smaller than that of an o-p y, then x is o< y:

|#

(defun od-1 (x y)
  (if (o-finp x)
      y
    (od-1 (o-first-expt x) (o-first-expt y))))

(defthm od-implies-ordlessp
  (implies (and (o-p x)
                (< (od x) (od y)))
           (o< x y)))

; To see the proof of well-foundedness, see the documentation topic
; proof-of-well-foundedness.
