(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "integral-rcfn")
(include-book "riemann-lemmas")
(include-book "integral-rcfn-lemmas")

(encapsulate
 ()
 (local (include-book "standard-part-equal-if-i-close"))
 (defthm standard-part-equal-if-i-close
   (implies (and (realp x)
                 (realp y)
                 (realp z))
            (equal (equal (standard-part x)
                          (+ (standard-part y) (standard-part z)))
                   (i-close (standard-part x) (+ y z))))))

(defthm integral-rcfn-equal-if-i-close
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< a b)
                (realp y)
                (realp z))
           (equal (equal (integral-rcfn a b)
                         (+ (standard-part y) (standard-part z)))
                  (i-close (integral-rcfn a b) (+ y z))))
  :hints (("Goal" :in-theory (disable riemann-rcfn make-partition i-close))))
