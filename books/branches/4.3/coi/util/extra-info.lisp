#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "in-conclusion")

;; extra-info

(defund extra-info (x y)
  (declare (xargs :guard t)
	   (ignore x y))
  t)

(local (in-theory (enable extra-info)))

(defthm no-extra-info
  (implies
   (not (extra-info x y))
   nil)
  :rule-classes (:forward-chaining))

(in-theory 
 (disable (:type-prescription extra-info)
	  (extra-info)))

;; rule-info

(defund rule-info (x y b)
  (declare (type t x y b))
  (and (extra-info x y) b t))

(local (in-theory (enable rule-info)))

(defcong iff equal (rule-info x y b) 3)

;; driver rules ..

(defthm open-rule-info-backchain
  (implies
   (not-in-conclusion)
   (equal (rule-info x y b) (and b t))))

(defthm open-rule-info-positive
  (implies
   (in-conclusion-check (rule-info x y b) :top t)
   (equal (rule-info x y b)
	  (and (extra-info x y) b t))))

(defthm open-rule-info-negated
  (implies
   (in-conclusion-check (rule-info x y b) :top :negated)
   (equal (rule-info x y b)
	  (implies (extra-info x y) b))))

