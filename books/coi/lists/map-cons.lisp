#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; map-cons.lisp
;; Definition of map-cons and theorems about it.

(in-package "LIST")
(include-book "basic")
(include-book "memberp")
(local (include-book "iff" :dir :util))

(defund map-cons (a x)
  (declare (type t a x))
  (if (consp x)
      (cons (cons a (car x))
            (map-cons a (cdr x)))
    nil))

(local (encapsulate
        ()
        (local
         (defthm test-for-type-prescription-of-map-cons
           (true-listp (map-cons n l))
           :rule-classes nil
           :hints(("Goal" 
                   :in-theory (union-theories '((:type-prescription map-cons))
                                              (theory 'minimal-theory))))))))


(defthm map-cons-type-1
  (implies (consp x)
           (consp (map-cons a x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm map-cons-type-2
  (implies (not (consp x))
           (equal (map-cons a x) 
                  nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm consp-of-map-cons
  (equal (consp (map-cons a x))
         (consp x)))

(defthm map-cons-of-non-consp-two
  (implies (not (consp x))
           (equal (map-cons a x)
                  nil)))

(defthm map-cons-of-cons
  (equal (map-cons a (cons b x))
         (cons (cons a b) 
               (map-cons a x)))
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm car-of-map-cons
  (equal (car (map-cons a x))
         (if (consp x)
             (cons a (car x))
           nil)))

(defthm cdr-of-map-cons
  (equal (cdr (map-cons a x))
         (map-cons a (cdr x))))

(defthm len-of-map-cons
  (equal (len (map-cons a x))
         (len x)))

(defcong equiv equal (map-cons a x) 2
  :hints(("Goal" :induct (len-len-induction x x-equiv))))

(defthm map-cons-of-append
  (equal (map-cons a (append x y))
         (append (map-cons a x)
                 (map-cons a y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm firstn-of-map-cons
  (equal (firstn n (map-cons a x))
         (map-cons a (firstn n x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm nthcdr-of-map-cons
  (equal (nthcdr i (map-cons a x))
         (map-cons a (nthcdr i x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-of-map-cons
  (equal (memberp a (map-cons b x))
         (and (consp a)
              (equal (car a) b)
              (memberp (cdr a) x)))
  :hints(("Goal" :in-theory (enable map-cons))))

(defthm alistp-of-map-cons
  (alistp (map-cons a x))
  :hints(("Goal" :in-theory (enable map-cons))))


;; Note that we are using acl2::member here instead of list::memberp

(defthm member-append
  (iff (member x (append y z))
       (or (member x y)
	   (member x z)))
  :hints (("Goal" :in-theory (enable member append))))

(defthm member-map-cons
  (iff (member x (map-cons y list))
       (and (consp x)
	    (equal (car x) y)
	    (member (cdr x) list)))
  :hints (("goal" :in-theory (enable member map-cons))))

