;; total-order.lisp

(in-package "ACL2")

(defun << (x y)
  (and (lexorder x y)
       (not (equal x y))))

(defthm <<-irreflexive
  (not (<< x x)))

(defthm <<-transitive
  (implies (and (<< x y)
                (<< y z))
           (<< x z)))

(defthm <<-asymmetric
  (implies (<< x y)
           (not (<< y x))))

(defthm <<-trichotomy
  (implies (and (not (<< y x))
                (not (equal x y)))
           (<< x y)))

(defthm <<-implies-lexorder
  (implies (<< x y)
	   (lexorder x y)))

(in-theory (disable <<))
