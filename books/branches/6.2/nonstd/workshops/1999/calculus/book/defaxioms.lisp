(in-package "ACL2")

; These events were axioms, or related to axioms, at one time, but are all now
; provable in ACL2(r).

(defthm standard-part-is-i-close
  (implies (realp x)
           (i-close (standard-part x) x)))

(defthm i-close-standard-part-2
  (implies (and (realp x)
                (realp y))
           (equal (i-close x (standard-part y))
                  (i-close x y))))
