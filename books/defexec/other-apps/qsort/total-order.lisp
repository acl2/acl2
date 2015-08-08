(in-package "ACL2")

#|
  total-order.lisp
  ~~~~~~~~~~~~~~~~
Here we define a non-strict total order, <<=, that corresponds to the strict
total order in books/misc/total-order.lisp.
|#

(defun <<= (x y)
  (declare (xargs :guard t))
  (lexorder x y))

(defthm <<=-reflexive
  (<<= x x))

(defthm <<=-anti-symmetric
  (implies (and (<<= x y)
                (<<= y x))
           (equal x y))
  :rule-classes :forward-chaining)

(defthm <<=-transitive
  (implies (and (<<= x y)
                (<<= y z))
           (<<= x z)))


(defthm <<=-total
  (implies (not (<<= x y))
           (<<= y x))
  :rule-classes :forward-chaining)

(in-theory (disable <<=))

(defun << (x y)
  (and (<<= x y)
       (not (equal x y))))

(defthm <<-irreflexive
  (not (<< x x)))

(defthm <<-transitive
  (implies (and (<< x y)
                (<< y z))
           (<< x z))
  :hints (("Goal"
           :do-not-induct t)
          ("Subgoal 2"
           :use <<=-transitive)
          ("Subgoal 1"
           :use <<=-anti-symmetric)))

(defthm <<-asymmetric
  (implies (<< x y)
           (not (<< y x)))
  :hints (("Goal"
           :use <<=-anti-symmetric)))

(defthm <<-trichotomy
  (implies (not (<< y x))
           (equal (<< x y)
		  (not (equal x y))))
  :hints (("Goal"
           :use <<=-total))
  :rule-classes :forward-chaining)

(defthm <<-anti-symmetric
  (implies (<< x y)
           (not (<<= y x)))
  :hints (("Goal"
           :use <<=-anti-symmetric))
  :rule-classes :forward-chaining)

(defthm <<-total
  (implies (not (<<= x y))
           (<< y x))
  :hints (("Goal"
           :use (<<=-total <<=-anti-symmetric)))
  :rule-classes :forward-chaining)


(in-theory (disable <<))

