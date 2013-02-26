#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "fixequiv")

(defthm integerp-implies-ifix-reduction
  (implies
   (integerp x)
   (equal (ifix x) x))
  :hints (("Goal" :in-theory (enable ifix))))

(defun ifixequiv (x y)
  (declare (type t x y))
  (equal (ifix x) (ifix y)))

(defequiv ifixequiv)

(defrefinement fixequiv ifixequiv
  :hints (("Goal" :in-theory (e/d (fix fixequiv)
                                  (equal-fix)))))

(defthm ifixequiv-ifix
  (ifixequiv (ifix x) x))

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
