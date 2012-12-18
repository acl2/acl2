; This example is essentially due to Vernon Austel.

(in-package "ACL2")

(defun eqv (x y)
  (equal x y))

(defequiv eqv)

(in-theory (disable eqv))

(encapsulate
 (((prop * *) => *)
  ((fn1 *) => *))

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)

 (local (defun prop (x y) t))
 (local (defun fn1 (x) x))

 (defthm booleanp-prop
   (booleanp (prop x y))
   :rule-classes (:rewrite :type-prescription))

 (defthm eqv-fn-prop
   (eqv (fn1 x) x)) ; Double-rewrite warning for x on rhs

 (defthm prop-thm
   (implies (eqv (double-rewrite x) y) ; Double-rewrite warning for y
	    (prop x y)))
 )

(defthm prop-fn1
  (prop (fn1 x) x))

; Theorem prop-fn1-fails below is the same as prop-fn1 just above, but fails
; because the double-rewrite call is missing on x in prop-thm-bad.

(defthm prop-thm-bad
   (implies (eqv x y) ; Double-rewrite warning for x and y
	    (prop x y)))

(in-theory (disable prop-fn1 prop-thm))

; See comment above.
; (defthm prop-fn1-fails
;   (prop (fn1 x) x))

; The following eliminates all warnings for the rule.

(defthm prop-thm-overkill
   (implies (eqv (double-rewrite x) (double-rewrite y))
	    (prop x y)))
