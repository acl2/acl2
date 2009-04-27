#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; deshadow.lisp
;; Introduces the deshadow function and some theorems about it.
;;
;; A "shadowed pair" is any cons in an alist whose key duplicates a key which
;; appears in an earlier cons.  In other words, shadowed pairs are those which
;; would not be accessible through "assoc", because they would be blocked by
;; earlier entries.  
;;
;; We provide a function, deshadow, which removes the shadowed pairs from an
;; alist but leaves the other pairs untouched (modulo consfixing) in the same
;; order.
;;
;; Historic note (jcd): I changed this function slightly, in the spirit of
;; clearkey, so that it consfixes the car of the alist each time it recurs.
;; This ensures that remove-shadowed-pairs always creates an alist, essentially
;; it alistfixes x for us.

(in-package "ALIST")
(include-book "strip")
(include-book "clearkey")
(include-book "../bags/basic")
(local (include-book "../util/iff"))

;; bzo move to bags library
(defthm count-of-remove-all-diff
  (implies (not (equal a b))
           (equal (BAG::count a (BAG::remove-all b x))
                  (BAG::count a x)))
  :hints(("Goal" :in-theory (enable BAG::remove-all))))

(defund deshadow (x)
  (declare (xargs :guard (alistp x)
                  :measure (len x)))
  (if (consp x)
      (cons (consfix (car x))
            (deshadow (clearkey (caar x) (cdr x))))
    nil))

(defthm deshadow-type-1
  (implies (not (consp x))
           (equal (deshadow x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-type-2
  (implies (consp x)
           (consp (deshadow x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-of-non-consp
  (implies (not (consp x))
           (equal (deshadow x) 
                  nil)))

(defthm consp-of-deshadow
  (equal (consp (deshadow x))
         (consp x)))

(defthm deshadow-of-cons
  (equal (deshadow (cons x y))
         (cons (consfix x) 
               (deshadow (clearkey (car x) y))))
  :hints(("Goal" :in-theory (enable deshadow clearkey))))

(defthm car-of-deshadow
  (equal (car (deshadow x))
         (if (consp x)
             (consfix (car x))
           nil))
  :hints (("Goal" :in-theory (disable EQUAL-CONSFIX-TO-CONS-EQUIV))))

;; no rules about cdr-of-deshadow, it is weird



(defthm len-of-deshadow-weak
  (<= (len (deshadow x))
      (len x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-weak-rewrite
  (equal (< (len x) (len (deshadow x)))
         nil))

;; Even though we will shortly prove deshadow-when-strip-cars-unique, we will
;; go ahead and prove both :linear rules below, so that we can backchain to
;; the unique of strip cars hypothesis when necessary.

(defthm len-of-deshadow-when-strip-cars-not-unique
  (implies (not (BAG::unique (strip-cars x)))
           (< (len (deshadow x))
              (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-when-strip-cars-unique
  (implies (BAG::unique (strip-cars x))
           (equal (len (deshadow x))
                  (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-decreases-rewrite
  (equal (< (len (deshadow x)) (len x))
         (not (BAG::unique (strip-cars x)))))



(encapsulate
 ()
 
 (local (defun my-induction (a b)
          (declare (xargs :measure (len a)))
          (if (atom a)
              (list a b)
            (my-induction
             (clearkey (caar a) (cdr a))
             (clearkey (caar b) (cdr b))))))

 (defcong alist-equiv equal (deshadow x) 1
   :hints(("Goal" 
           :in-theory (enable deshadow)
           :induct (my-induction x x-equiv))))
)



(defthm alistp-of-deshadow
  (alistp (deshadow x))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-of-clearkey
  (equal (deshadow (clearkey key x))
         (clearkey key (deshadow x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm unique-of-strip-cars-of-deshadow
  (BAG::unique (strip-cars (deshadow x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-when-strip-cars-unique
  (implies (BAG::unique (strip-cars x))
           (equal (deshadow x)
                  (alistfix x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-idempotent
  (equal (deshadow (deshadow x))
         (deshadow x)))



(defthm memberp-of-strip-cars-of-deshadow
  (equal (memberp key (strip-cars (deshadow x)))
         (memberp key (strip-cars x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm count-of-strip-cars-of-deshadow
  (<= (BAG::count key (strip-cars (deshadow x)))
      (BAG::count key (strip-cars x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(encapsulate
 ()
 (local (include-book "../bags/pick-a-point"))

 (defthm subbagp-strip-cars-of-deshadow
   (BAG::subbagp (strip-cars (deshadow x)) 
                 (strip-cars x)))
)



;; There is probably an equivalent rule for strip-cdrs, but I haven't tried
;; to prove it yet.

(defthm not-memberp-of-strip-cdrs-of-deshadow
  (implies (not (memberp val (strip-cdrs x)))
           (equal (memberp val (strip-cdrs (deshadow x)))
                  nil))
  :hints(("Goal" :in-theory (enable deshadow))))


;; bzo - it seems like we set up this whole deshadow thing thinking about 
;; assoc, and then we never prove any rules about assoc?  
;;
;; Furthermore, it seems like (equal (deshadow x) (deshadow y)) would be a very
;; natural equivalence relation for talking about assoc's.  Perhaps we should
;; try to provide it in the future and some congruence rules about it.  It
;; should be a nice refinement of alist-equal.
