(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "nsa-lemmas")
;;; Needed for very last proof, of rcfn-next-gte-close:
(include-book "riemann-lemmas")

(encapsulate
 ()
 (local (include-book "next-gte-close"))
 (defthm next-gte-close
   (implies (and (partitionp p2)
                 (standard-numberp (car p2))
                 (standard-numberp (car (last p2)))
                 (i-small (mesh p2))
                 (<= (car p2) x)
                 (<= x (car (last p2)))
                 (realp x))
            (i-close x (next-gte x p2)))))

(defthm rcfn-continuous-alternate
  (implies (and (standard-numberp y)
                (realp x)
                (i-close x y)
                (realp y))
           (i-close (rcfn x) (rcfn y)))
  :hints (("Goal" :in-theory (enable i-close-symmetric))))

(defthm rcfn-continuous-property
  (implies (and (realp x)
                (i-limited x)
                (realp y)
                (i-close x y))
           (i-close (rcfn x) (rcfn y)))
  :hints (("Goal"
           :use
           ((:instance i-close-transitive
                       (x (rcfn x))
                       (y (rcfn (standard-part x)))
                       (z (rcfn y))))
           :in-theory (disable i-close-transitive))))

;;; This is a general lemma from non-standard analysis, but we leave
;;; it here rather than moving it (say, to riemann-lemmas.lisp)
;;; because it has two free variables and hence seems rather
;;; specialized.
(defthm i-limited-when-between-standard-reals
  (implies (and (<= x big)
                (<= small x)
                (realp small)
                (realp big)
                (standard-numberp small)
                (standard-numberp big)
                (realp x))
           (i-limited x))
  :hints (("Goal"
           :use (:instance
                 large-if->-large
                 (y (max (abs small) (abs big)))
                 (x x))
           :in-theory (disable large-if->-large))))

(defthm rcfn-next-gte-close
  (implies (and (partitionp p2)
                (standard-numberp (car p2))
                (standard-numberp (car (last p2)))
                (i-small (mesh p2))
                (<= (car p2) x)
                (<= x (car (last p2)))
                (realp x))
           (i-close (rcfn x) (rcfn (next-gte x p2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable next-gte partitionp2 mesh))))
