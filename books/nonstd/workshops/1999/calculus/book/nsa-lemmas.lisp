(in-package "ACL2")

(include-book "nsa")

;;; The following lemmas were found during the course of the proof of
;;; sum-of-integrals.lisp and its sub-goals.

(defthm standard-part-preserves-nonnegative
  (implies (and (realp x)
                (<= 0 x))
           (<= 0 (standard-part x))))

;;; Originally proved in i-small-maxlist-abslist-difflist-maps:
(defthm standard-part-0-implies-i-small
  (implies (and (acl2-numberp x)
                (equal (standard-part x) 0))
           (i-small x))
  :hints (("Goal" :expand (i-small x))))

(defthm i-close-to-standard-part
  (implies (and (acl2-numberp x)
                (i-limited x))
           (i-close x (standard-part x)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm standard-part-preserves-i-close-1
  (implies (and (acl2-numberp x)
                (i-limited x)
                (acl2-numberp y)
                (i-close x y))
           (i-close (standard-part x) y))
  :hints (("Goal"
           :use (:instance
                 i-close-transitive
                 (x (standard-part x))
                 (y x)
                 (z y))
           :in-theory (enable i-close-symmetric))))
