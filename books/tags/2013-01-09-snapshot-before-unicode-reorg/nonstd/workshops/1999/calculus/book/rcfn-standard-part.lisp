(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "nsa-lemmas")
(include-book "defaxioms") ; needed for rcfn-standard-part-i-close

(defthm rcfn-standard-part-i-close
  (implies (and (i-limited x)
                (realp x))
           (i-close (rcfn (standard-part x))
                    (standard-part (rcfn x)))))

(local
 (defthm i-close-and-standard-implies-equal
   (implies (and (realp x)
                 (realp y)
                 (i-close x y)
                 (standard-numberp x)
                 (standard-numberp y))
            (equal (equal x y)
                   t))
   :hints (("Goal"
            :use
            ((:instance standard-small-is-zero
                        (x (- y x))))
            :in-theory (enable i-close i-small)))))

(encapsulate
 ()
 (local (include-book "i-limited-rcfn"))

 (defthm i-limited-rcfn
   (implies (and (realp x)
                 (i-limited x))
            (i-limited (rcfn x)))))

(defthm rcfn-standard-part
   (implies (and (i-limited x)
                 (realp x))
            (equal (rcfn (standard-part x))
                   (standard-part (rcfn x)))))
