#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "fixequiv")

(defun ifixequiv (x y)
  (equal (ifix x) (ifix y)))

(defequiv ifixequiv)

(defrefinement fixequiv ifixequiv
  :hints (("Goal" :in-theory (e/d (fix fixequiv)
                                  (equal-fix)))))

(defthm ifixequiv-ifix
  (ifixequiv (ifix x) x))



#+joe
(defthm default-ifix
  (implies
   (not (integerp x))
   (ifixequiv x 0)))

(defcong ifixequiv equal (ifix x) 1)

(defthmd equal-ifix
  (equal (equal (ifix x) y)
         (and (integerp y)
              (ifixequiv x y))))

(in-theory (disable ifixequiv))

(theory-invariant 
 (incompatible
  (:rewrite equal-ifix)
  (:definition ifixequiv)))

(in-theory (disable ifix))
