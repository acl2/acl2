; This book contains truly miscellaneous facts.  We have started it as a place
; to put facts that justify claims made in the ACL2 sources.

(in-package "ACL2")

; Justification for using floor to compute nonnegative-integer-quotient in raw
; Lisp:

(local (include-book "rtl/rel9/arithmetic/top" :dir :system))

(defun nonnegative-integer-quotient-as-floor-test (i j)
; Guard is from nonnegative-integer-quotient.
  (declare (xargs :guard (and (integerp i)
                              (not (< i 0))
                              (integerp j)
                              (< 0 j))))
  (mbe :logic (nonnegative-integer-quotient i j)
       :exec (floor i j)))

