; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;
;; top.lisp
;;

;;
;; This book gathers together all the other books in one easy to
;; include package.
;;

(in-package "ACL2")

(include-book "basic-arithmetic")

(include-book "inequalities")

(include-book "expt")

(include-book "prefer-times")

(include-book "mini-theories")

(include-book "numerator-and-denominator")

#| ???
(defthm three
  (implies (rationalp x)
	   (rationalp (expt x y)))
  :rule-classes :type-prescription)

#+:non-standard-analysis
(defthm three-realp
  (implies (realp x)
	   (realp (expt x y)))
  :rule-classes :type-prescription)

(defthm four
  (equal (* x (expt x -1))
	 (if (equal (fix x) 0)
	     0
	     1)))

(defthm five
  (equal (* y x (expt y -1))
	 (if (equal (fix y) 0)
	     0
	     (fix x))))

(defthm six
  (equal (/ x)
	 (expt x -1))
  :hints (("Goal" :expand (expt x -1))))
|#
#| !!!
(defthm seven
  (implies (not (acl2-numberp x))
	   (equal (expt x y)
		  (if (equal (ifix y) 0)
		      1
		      0))))
|#
#| ???
(in-theory (disable expt))
|#
