(in-package "ACL2")

;;; Surprisingly, ACL2 knows very little about the rational numbers.
;;; Even though its type system knows that x*y is rational when x and
;;; y are rational, it gets confused when a theorem has that as a
;;; hypothesis, because the crucial fact is needed by the rewriter,
;;; not the type-system.  Sad, really.

;;; The arithmetic books solve this problem for the rationals.  The
;;; same problems apply to ACL2(r) with the reals, so we include those
;;; simple theorems here.

(defthm realp-+
  (implies (and (realp x) (realp y))
	   (realp (+ x y))))

(defthm realp-uminus
  (implies (realp x)
	   (realp (- x))))

(defthm realp-*
  (implies (and (realp x) (realp y))
	   (realp (* x y))))

(defthm realp-udiv
  (implies (realp x)
	   (realp (/ x))))
