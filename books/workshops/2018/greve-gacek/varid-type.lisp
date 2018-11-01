;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

(include-book "types")
(include-book "sets")

;; ------------------------------------------------------------

(defcong nat-equiv equal (zp x) 1)
(in-theory (disable zp))

;; ------------------------------------------------------------

(set-tau-auto-mode nil)
(defun varid-p (x)
  (declare (type t x))
  (natp x))

(def::type-properties+ varid-p (x)
  (declare (xargs :type-witness 0
                  :type-name varid))
  (natp x))

(defthmd varid-p-implies
  (implies
   (varid-p x)
   (natp x))
  :rule-classes (:forward-chaining))

(defthmd implies-varid-p
  (implies
   (natp x)
   (varid-p x)))

(set-tau-auto-mode t)
(in-theory (disable (:type-prescription varid-p) varid-p (varid-p)))
;; We don't really wnat to know anything about it ..
(in-theory (disable 
            DEFTYPE-PROPERTIES-VARID-P-IMPLIES-BODY
            BODY-IMPLIES-DEFTYPE-PROPERTIES-VARID-P
            NOT-DEFTYPE-PROPERTIES-VARID-P-IMPLIES-NOT-BODY
            NOT-BODY-IMPLIES-NOT-DEFTYPE-PROPERTIES-VARID-P
            ))

;; (defun varid-fix (x)
;;   (declare (type t x))
;;   (rfix x))

;; (def::signature varid-fix (t) varid-p)

;; (defun varid-equiv (x y)
;;   (declare (type t x y))
;;   (rfix-equiv x y))

;; (defthm varid-equiv-type-reduction
;;   (implies
;;    (and
;;     (varid-p x)
;;     (varid-p y))
;;    (iff (varid-equiv x y)
;;         (equal x y))))

;; (defthm varid-fix-varid-p
;;   (implies
;;    (varid-p x)
;;    (equal (varid-fix x) x)))

;; (defequiv varid-equiv)

;; (defcong varid-equiv equal (varid-fix x) 1)

;; (defthm varid-equiv-varid-fix
;;   (varid-equiv (varid-fix x) x))

;; (defthmd equal-varid-fix
;;   (iff (equal (varid-fix x) y)
;;        (and (varid-p y)
;;             (varid-equiv x y))))


;; ------------------------------------------------------------

(fty::deflist varid-list
  :elt-type varid-p
  :pred varid-listp
  :fix  varid-list-fix
  :true-listp t
  )

(defthm memberp-in-varid-listp-implies-varid-p
  (implies
   (and
    (list::memberp a list)
    (varid-listp list))
   (varid-p a))
  :hints (("Goal" :in-theory (enable list::memberp varid-listp)))
  :rule-classes (:forward-chaining))

(defun varid-list-fix! (x)
  (declare (type t x))
  (with-guard-checking :none (ec-call (varid-list-fix x))))

(in-theory (disable VARID-LIST-EQUIV-OF-VARID-LIST-FIX-2-FORWARD
                    VARID-LIST-EQUIV-OF-VARID-LIST-FIX-1-FORWARD))

(defrefinement varid-list-equiv consp-equiv
  :hints (("Goal" :in-theory (enable varid-list-fix))))

(defthm open-varid-list-equiv-on-consp
  (implies
   (consp x)
   (iff (varid-list-equiv x y)
        (and (consp y)
             (equal (varid-fix (car x)) (varid-fix (car y)))
             (varid-list-equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable varid-list-fix))))

(defthm equal-varid-list-fix-to-varid-list-equiv
  (iff (equal (varid-list-fix x) y)
       (and (varid-listp y)
            (varid-list-equiv x y))))

(in-theory (disable varid-list-equiv$inline))

;; (def::signature append (varid-listp varid-listp) varid-listp)

;; ------------------------------------------------------------

#+joe
(encapsulate
    ()

  (local (in-theory (enable varid-witness varid-fix varid-p)))
  
  (def::und new-varid (lower upper)
    (declare (xargs :signature ((t t) varid-p)
                    :guard (and (varid-p lower) (varid-p upper))
                    :congruence ((varid-equiv varid-equiv) equal)))
    (/ (+ (varid-fix lower) (varid-fix upper)) 2))
  
  (defthm new-varid-order
    (implies
     (and
      (varid-p lower)
      (varid-p upper)
      (< lower upper))
     (and (< (new-varid lower upper) upper)
          (< lower (new-varid lower upper))))
    :hints (("Goal" :in-theory (enable new-varid)))
    :rule-classes (:rewrite
                   :linear 
                   (:forward-chaining :trigger-terms ((new-varid lower upper)))))
  
)
