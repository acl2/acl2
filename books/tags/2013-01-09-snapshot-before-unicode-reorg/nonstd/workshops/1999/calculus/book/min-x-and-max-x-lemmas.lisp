(in-package "ACL2")

(include-book "max-and-min-attained")

(defthm-std realp-min-x
  (implies (and (realp a)
                (realp b))
           (realp (min-x a b)))
  :rule-classes (:type-prescription :rewrite))

(defthm-std realp-max-x
  (implies (and (realp a)
                (realp b))
           (realp (max-x a b)))
  :rule-classes (:type-prescription :rewrite))

(local
 (encapsulate
  ()
  (local (include-book "between-i-close-implies-i-close"))

  (defthm i-close-squeeze-1
    (implies (and (between z x y)
                  (realp z)
                  (realp x)
                  (realp y)
                  (i-close x y))
             (i-close x z))
    :hints (("Goal" :in-theory (enable i-close)))
    :rule-classes :forward-chaining)

(defthm i-close-squeeze-2
   (implies (and (between z x y)
                 (realp z)
                 (realp x)
                 (realp y)
                 (i-close x y))
            (i-close y z))
   :rule-classes :forward-chaining)
))

(local (in-theory (disable between)))

(encapsulate
 ()
 (local (include-book "min-x-between"))

 (defthm min-x-between
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (between (min-x x y) x y))
   :rule-classes nil))

(in-theory (enable i-close-symmetric))

(defthm i-close-min-x-commuted
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close x (min-x x y)))
  :hints (("Goal" :use min-x-between)))

(defthm i-close-min-x
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close (min-x x y) x)))

(encapsulate
 ()
 (local (include-book "max-x-between"))

 (defthm max-x-between
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (between (max-x x y) x y))
   :rule-classes nil))

(defthm i-close-max-x-commuted
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close x (max-x x y)))
  :hints (("Goal" :use max-x-between)))

(defthm i-close-max-x
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close (max-x x y) x)))

(defthm i-close-min-x-alt-commuted
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close y (min-x x y)))
  :hints (("Goal" :use min-x-between)))

(defthm i-close-min-x-alt
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close (min-x x y) y))
  :hints (("Goal" :use min-x-between)))

(defthm i-close-max-x-alt-commuted
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close (max-x x y) y))
  :hints (("Goal" :use max-x-between)))

(defthm i-close-max-x-alt
  (implies (and (realp x)
                (realp y)
                (< x y)
                (i-close x y))
           (i-close (max-x x y) y))
  :hints (("Goal" :use max-x-between)))
