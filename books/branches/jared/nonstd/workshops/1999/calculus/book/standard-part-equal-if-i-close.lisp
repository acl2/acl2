(in-package "ACL2")

(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.
(include-book "defaxioms")

(defthm standard-part-equal-if-i-close
  (implies (and (realp x)
                (realp y)
                (realp z))
           (equal (equal (standard-part x)
                         (+ (standard-part y) (standard-part z)))
                  (i-close (standard-part x) (+ y z))))
  :hints (("Goal" :in-theory (enable i-close i-small))))
