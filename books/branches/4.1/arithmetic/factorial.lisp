;;; Contributed by Ruben A. Gamboa

;;; This book includes many useful theorems about the factorial
;;; function.

(in-package "ACL2")

;;; We start with a definition of the factorial function.  This can be
;;; found in almost all LISP books!

(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (1- n)))))

;;; It is a (surprisingly) non-obvious fact that factorial returns a
;;; non-zero integer.  The default type heuristics of ACL2 simply
;;; conclude that it is a number!

(defthm factorial-positive-integer
  (and (integerp (factorial n))
       (< 0 (factorial n)))
  :rule-classes (:rewrite :type-prescription))

;;; Factorial is not just positive, it is at least 1.

(defthm factorial-non-negative
  (<= 1 (factorial n))
  :rule-classes (:rewrite :linear))

;;; Since it's always positive, |n!| = n!.

(defthm abs-factorial
  (equal (abs (factorial x))
	 (factorial x)))

;;; I prefer to disable the definition by default, and simply enable
;;; it where I need it.  This has worked well for me.
(in-theory (disable factorial))

