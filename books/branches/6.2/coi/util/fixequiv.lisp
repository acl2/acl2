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
  (declare (type t x y))
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
;; It would be nice to have more list facts in place before doing this.
;;
;; In particular, it would be nice to assert that list::equiv refines
;; this equivalence.

(defun fixlist (list)
  (declare (type t list))
  (if (consp list)
      (cons (fix (car list))
            (fixlist (cdr list)))
    nil))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defun acl2-number-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (acl2-numberp (car l))
                (acl2-number-listp (cdr l))))))

(defthm acl2-number-listp-fixlist
  (acl2-number-listp (fixlist list)))

(defthm acl2-number-listp-fixlist-reduction
  (implies
   (acl2-number-listp list)
   (equal (fixlist list) list)))

(defun fixlist-equiv (x y)
  (declare (type t x y))
  (if (consp x)
      (and (consp y)
	   (fixequiv (car x) (car y))
	   (fixlist-equiv (cdr x) (cdr y)))
    (not (consp y))))

(defun fixlist-equiv-alt (x y)
  (declare (type t x y))
  (equal (fixlist x)
         (fixlist y)))

(defthmd fixlist-equiv-to-fixlist-equiv-alt
  (equal (fixlist-equiv x y)
	 (fixlist-equiv-alt x y))
  :hints (("Goal" :induct (fixlist-equiv x y)
	   :in-theory (enable fixequiv))))

(local (in-theory (enable fixlist-equiv-to-fixlist-equiv-alt)))

(defequiv fixlist-equiv)

(defthm fixlist-equiv-fixlist-reduction
  (implies
   (acl2-number-listp x)
   (equal (fixlist x) x)))

(defthmd equal-fixlist
  (equal (equal x (fixlist y))
	 (and (acl2-number-listp x)
	      (fixlist-equiv x y))))

(theory-invariant 
 (incompatible
  (:rewrite equal-fixlist)
  (:definition fixlist-equiv)))

(theory-invariant 
 (incompatible
  (:rewrite equal-fixlist)
  (:definition fixlist-equiv-to-fixlist-equiv-alt)))

(defcong fixlist-equiv fixlist-equiv (cons a x) 2)

(defcong fixequiv fixlist-equiv (cons a x) 1)

(defcong fixlist-equiv fixlist-equiv (append x y) 1
  :hints (("Goal" :in-theory (disable fixlist-equiv-to-fixlist-equiv-alt))))

(defcong fixlist-equiv fixlist-equiv (append x y) 2
  :hints (("Goal" :induct (append x y)
	   :in-theory (enable append))))

(in-theory (disable fixlist-equiv-to-fixlist-equiv-alt))
