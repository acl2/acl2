#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "ifixequiv")

(defthm natp-implies-nfix-reduction
  (implies
   (natp x)
   (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix))))

(defun nfixequiv (x y)
  (declare (type t x y))
  (equal (nfix x) (nfix y)))

(defequiv nfixequiv)

(defrefinement ifixequiv nfixequiv
  :hints (("Goal" :in-theory (e/d (ifix ifixequiv)
                                  (equal-ifix)))))

(defthm nfixequiv-nfix
  (nfixequiv (nfix x) x))

(defcong nfixequiv equal (nfix x) 1)

(defthmd equal-nfix
  (equal (equal (nfix x) y)
         (and (natp y)
              (nfixequiv x y))))

(in-theory (disable nfixequiv))

(theory-invariant 
 (incompatible
  (:rewrite equal-nfix)
  (:definition nfixequiv)))

(in-theory (disable nfix))
