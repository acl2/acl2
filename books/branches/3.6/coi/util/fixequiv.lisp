#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

;; This library should be used more extensively , for example IHS.

;;
;; fixequiv is an equivalence relation for "fix"
;;

(defun fixequiv (x y)
  (equal (fix x) (fix y)))

(defthm acl2-numberp-fix
  (acl2-numberp (fix x)))

(defthm acl2-numberp-implies-fix-reduction
  (implies
   (acl2-numberp x)
   (equal (fix x) x))
  :hints (("Goal" :in-theory (enable fix))))

(defequiv fixequiv)

(defthm fixequiv-fix
  (fixequiv (fix x) x))

;; Which other functions would benefit from this ?

(defcong fixequiv equal (unary-- x) 1
  :hints (("Goal" :in-theory (enable fix))))

(defcong fixequiv equal (+ x y) 1
  :hints (("Goal" :in-theory (enable fix))))

(defcong fixequiv equal (+ x y) 2
  :hints (("Goal" :in-theory (enable fix))))

(defcong fixequiv equal (< x y) 1
  :hints (("Goal" :in-theory (enable fix))))

(defcong fixequiv equal (< x y) 2
  :hints (("Goal" :in-theory (enable fix))))

(defthmd equal-fix
  (and
   (equal (equal (fix x) y)
          (and
           (acl2-numberp y)
           (fixequiv x y)))
   (equal (equal y (fix x))
          (and
           (acl2-numberp y)
           (fixequiv y x)))))

(defthm <=-commute-implies-fixequiv
  (implies
   (and
    (<= a x)
    (<= x a))
   (fixequiv a x))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (fix fixequiv)
                                  (equal-fix)))))

(defthm <-from-<=-not-fixequiv-implies-<
  (implies
   (and
    (<= a x)
    (not (fixequiv a x)))
   (< a x)))

(defcong fixequiv equal (fix x) 1)

(in-theory (disable fixequiv))
(in-theory (disable fix))

(theory-invariant 
 (incompatible
  (:rewrite equal-fix)
  (:definition fixequiv)))

;;
;; fixlist-equiv
;;

(defun fixlist (list)
  (if (consp list)
      (cons (fix (car list))
            (fixlist (cdr list)))
    nil))

(defun acl2-number-listp (list)
  (if (consp list)
      (and (acl2-numberp (car list))
           (acl2-number-listp (cdr list)))
    (null list)))

(defthm acl2-number-listp-fixlist
  (acl2-number-listp (fixlist list)))

(defthm acl2-number-listp-fixlist-reduction
  (implies
   (acl2-number-listp list)
   (equal (fixlist list) list)))

(defun fixlist-equiv (x y)
  (equal (fixlist x)
         (fixlist y)))

(defequiv fixlist-equiv)

(defthm fixlist-equiv-definition
  (equal (fixlist-equiv x y)
         (if (consp x)
             (and (consp y)
                  (fixequiv (car x) (car y))
                  (fixlist-equiv (cdr x) (cdr y)))
           (not (consp y))))
  :hints (("Goal" :in-theory (enable equal-fix)))
  :rule-classes (:definition))

(defthm fixlist-equiv-fixlist-reduction
  (fixlist-equiv (fixlist x) x))

(in-theory (disable fixlist-equiv))
