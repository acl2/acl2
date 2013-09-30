(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "nsa-lemmas")

;;; Amazing.  I've finally gotten it down to this final lemma (after
;;; proving everything later in this file), and was expecting to have
;;; to push its proof into another file.  But it went through
;;; automatically!
(defthm next-gte-is-within-mesh
  (implies (and (partitionp p)
                (<= (car p) x)
                (<= x (car (last p)))
                (realp x))
           (<= (abs (- x (next-gte x p)))
               (mesh p)))
  :rule-classes (:linear :rewrite))

(defthm realp-next-gte-type-prescription
  (implies (and (partitionp p)
                (<= a (car (last p))))
           (realp (next-gte a p)))
  :rule-classes :type-prescription)

(defthm next-gte-close
  (implies (and (partitionp p2)
                (standard-numberp (car p2))
                (standard-numberp (car (last p2)))
                (i-small (mesh p2))
                (<= (car p2) x)
                (<= x (car (last p2)))
                (realp x))
           (i-close x (next-gte x p2)))
  :hints (("Goal"
           :use (:instance small-if-<-small (x (mesh p2))
                           (y (- x (next-gte x p2))))
           :in-theory
           (union-theories '(i-small i-close)
                           (disable abs mesh small-if-<-small)))))
