(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "nsa-lemmas")
(include-book "defaxioms")

(local
 (defthm i-large-in-terms-of-standard-numberp-standard-part-lemma-lemma
   (implies (and (realp x)
                 (i-large x))
            (i-large (standard-part x)))
   :rule-classes nil))

(local
 (defthm i-large-in-terms-of-standard-numberp-standard-part-lemma
   (implies (and (realp x)
                 (i-large x))
            (not (standardp (standard-part x))))
   :hints (("Goal"
            :use
            i-large-in-terms-of-standard-numberp-standard-part-lemma-lemma))))

(local
 (defthm i-large-in-terms-of-standard-numberp-standard-part
   (implies (realp x)
            (iff (i-large x)
                 (not (standardp (standard-part x)))))))

(defthm i-limited-rcfn
  (implies (and (realp x)
                (i-limited x))
           (i-limited (rcfn x)))
  :hints (("Goal"
           :in-theory
           (disable rcfn-continuous i-close-limited)
           :use
           ((:instance
             rcfn-continuous
             (x (standard-part x))
             (y x))
            (:instance
             i-close-limited
             (x (rcfn (standard-part x)))
             (y (rcfn x)))))))
