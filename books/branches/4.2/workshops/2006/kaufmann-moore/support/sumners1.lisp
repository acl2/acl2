; The following is a variant of something we created based on something Rob Sumners
; created.  It fails in v2-8 but passes in v2-9 and beyond, because of our
; special handling of iff.

(in-package "ACL2")

(defun f (x) (not (not x)))

(defthm f-x-iff-x
  (iff (f x) x)) ; Double-rewrite warning for x on right-hand side

(in-theory (disable f))

(defun g (x) x)

(defthm g-x-if-x
  (implies x (g x))) ; no double-rewrite warning because of special handling

(in-theory (disable g))

(defthm g-f
  (implies x (g (f x))))
