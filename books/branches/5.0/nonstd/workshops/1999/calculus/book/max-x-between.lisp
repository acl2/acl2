(in-package "ACL2")

(include-book "max-and-min-attained")

(encapsulate
 ()
 (local (include-book "standard-part-preserves-between"))

 (defthm standard-part-preserves-between
   (implies (and (realp x)
                 (realp y)
                 (realp z)
                 (between z x y))
            (between (standard-part z)
                     (standard-part x)
                     (standard-part y)))
   :rule-classes nil))

(in-theory (disable between))

(defthm max-x-rec-between-rewrite
  (implies (and (partitionp p)
                (equal a (car p))
                (equal b (car (last p))))
           (between (max-x-rec p)
                    a
                    b)))

(defthm-std max-x-between
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (between (max-x x y) x y))
   :rule-classes nil
   :hints (("Goal"
            :use
            ((:instance
              standard-part-preserves-between
              (z (max-x-rec (make-partition x y (i-large-integer)))))))))
