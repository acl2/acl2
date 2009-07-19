#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "ifixequiv")

(defun nfixequiv (x y)
  (equal (nfix x) (nfix y)))

(defequiv nfixequiv)

(defrefinement ifixequiv nfixequiv
  :hints (("Goal" :in-theory (e/d (ifix ifixequiv)
                                  (equal-ifix)))))

(defthm nfixequiv-nfix
  (nfixequiv (nfix x) x))



#+joe
(defthm default-nfix
  (implies
   (not (natp x))
   (nfixequiv x 0)))

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
