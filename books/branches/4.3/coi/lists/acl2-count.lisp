#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; acl2-count.lisp
;; Jared and Eric are trying to make the perfect acl2-count book.  Send us feedback!

(in-package "ACL2")

(local (in-theory (disable acl2-count))) ;bzo would like this to be non-local?

(defthm acl2-count-of-cons
  (equal (acl2-count (cons x y))
         (+ 1 (acl2-count x) (acl2-count y)))
  :hints (("Goal" :in-theory (enable acl2-count))))

(defthm acl2-count-when-consp-linear
  (implies (consp x)
           (equal (acl2-count x) 
                  (+ 1 
                     (acl2-count (car x))
                     (acl2-count (cdr x)))))
  :rule-classes :linear)

;; ACL2-COUNT of CAR

(defthm acl2-count-of-car-bound-weak-linear
  (<= (acl2-count (car x)) 
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-car-bound-weak
  (equal (< (acl2-count x) (acl2-count (car x)))
         nil))

(defthm acl2-count-of-car-bound-tight
  (equal (< (acl2-count (car x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))

;; ACL2-COUNT of CDR

(defthm acl2-count-of-cdr-bound-weak-linear
  (<= (acl2-count (cdr x)) 
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-cdr-bound-weak
  (equal (< (acl2-count x) (acl2-count (cdr x)))
         nil))

(defthm acl2-count-of-cdr-bound-tight
  (equal (< (acl2-count (cdr x)) (acl2-count x))
         (or (consp x)
             (< 0 (acl2-count x)))))


;; ACL2-COUNT of NTH

(defthm acl2-count-of-nth-bound-weak-linear
  (<= (acl2-count (nth n l)) 
      (acl2-count l))
  :rule-classes :linear)

(defthm acl2-count-of-nth-bound-weak
  (equal (< (acl2-count l) (acl2-count (nth n l)))
         nil))

(defthm acl2-count-of-nth-bound-tight
  (equal (< (acl2-count (nth n l)) (acl2-count l))
         (or (consp l)
             (< 0 (acl2-count l)))))

(defthm acl2-count-of-nth-bound-tight-linear
  (implies (consp l)
           (< (acl2-count (nth n l)) (acl2-count l)))
  :rule-classes :linear)
