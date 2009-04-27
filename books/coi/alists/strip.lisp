#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; strip.lisp
;; Theorems about strip-cars and strip-cdrs. (a.k.a., keys and vals)
;;
;; Usually alists are interpreted as finite functions or mappings that bind
;; some domain elements (keys) to values.  The typical interpretation of an
;; alist is that the car of each pair is a key, and the cdr of each pair is a
;; value.  The functions strip-cars and strip-cdrs return the list of all cars
;; and cdrs of the alist, respectively.
;;
;; These functions do not return sets, and they maintain the order of keys and
;; values in the alist.  They also return shadowed pairs (see deshadow.lisp).
;; In a sense, these functions are like alist-equiv, which also considers the
;; shadowed pairs to be relevant.

(in-package "ALIST")
(include-book "equiv")
(include-book "../lists/memberp")
(local (include-book "../util/iff"))

(in-theory (disable strip-cars strip-cdrs))


;; STRIP-CARS

(defcong alist-equiv equal (strip-cars x) 1
  :hints(("Goal" 
          :in-theory (enable strip-cars)
          :induct (len-len-induction x x-equiv))))

(defthm strip-cars-type-consp
  (implies (consp x)
           (consp (strip-cars x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-type-non-consp
  (implies (not (consp x))
           (not (consp (strip-cars x))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm consp-strip-cars
  (equal (consp (strip-cars x))
         (consp x)))

(defthm strip-cars-of-non-consp
  (implies (not (consp x))
           (equal (strip-cars x)
                  nil))
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-of-cons
  (equal (strip-cars (cons x y))
         (cons (car x) 
               (strip-cars y)))
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm car-of-strip-cars
  (equal (car (strip-cars x))
         (car (car x))))

(defthm strip-cars-of-cdr
  (equal (strip-cars (cdr x))
         (cdr (strip-cars x))))

(defthm len-of-strip-cars
  (equal (len (strip-cars x))
         (len x))
  :hints(("Goal" :in-theory (enable len))))

(defthm strip-cars-of-append
  (equal (strip-cars (append x y))
         (append (strip-cars x) 
                 (strip-cars y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm strip-cars-of-firstn
  (equal (strip-cars (firstn n x))
         (firstn n (strip-cars x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm strip-cars-of-nthcdr
  (equal (strip-cars (nthcdr n x))
         (nthcdr n (strip-cars x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-caar-strip-cars
  (equal (memberp (caar x) (strip-cars x))
         (consp x)))



;; STRIP-CDRS

(defcong alist-equiv equal (strip-cdrs x) 1
  :hints(("Goal" 
          :in-theory (enable strip-cdrs)
          :induct (len-len-induction x x-equiv))))

(defthm strip-cdrs-type-consp
  (implies (consp x)
           (consp (strip-cdrs x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-type-non-consp
  (implies (not (consp x))
           (not (consp (strip-cdrs x))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm consp-strip-cdrs
  (equal (consp (strip-cdrs x))
         (consp x)))

(defthm strip-cdrs-of-non-consp
  (implies (not (consp x))
           (equal (strip-cdrs x) 
                  nil))
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons x y))
         (cons (cdr x) 
               (strip-cdrs y)))
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm car-of-strip-cdrs
  (equal (car (strip-cdrs x))
         (cdr (car x))))

(defthm strip-cdrs-of-cdr
  (equal (strip-cdrs (cdr x))
         (cdr (strip-cdrs x))))

(defthm len-of-strip-cdrs
  (equal (len (strip-cdrs x))
         (len x))
  :hints(("Goal" :in-theory (enable len))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append x y))
         (append (strip-cdrs x) 
                 (strip-cdrs y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm strip-cdrs-of-firstn
  (equal (strip-cdrs (firstn n x))
         (firstn n (strip-cdrs x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm strip-cdrs-of-nthcdr
  (equal (strip-cdrs (nthcdr n x))
         (nthcdr n (strip-cdrs x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-cdar-strip-cdrs
  (equal (memberp (cdar x) (strip-cdrs x))
         (consp x)))

