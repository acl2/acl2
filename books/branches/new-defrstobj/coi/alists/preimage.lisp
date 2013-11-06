#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; preimage.lisp
;;
;; In an alist, we say that the preimage of some value, val, is the set of all
;; keys which are bound to val in that alist.  Our preimage function actually
;; returns a list of such keys, which happen to be unique, but which are not 
;; necessarily a set (at least, not in the :osets sense).

(in-package "ALIST")
(include-book "deshadow")
(include-book "strip")

;; Preimage-aux scans the list looking for our value, and collects any keys it
;; finds along the way.  Note that it will collect shadowed pairs if they are
;; bound to our value.

(defund preimage-aux (val x)
  (declare (xargs :guard (alistp x)))
  (if (consp x)
      (if (equal (cdar x) val)
          (cons (caar x) 
                (preimage-aux val (cdr x)))
        (preimage-aux val (cdr x)))
    nil))

(defcong alist-equiv equal (preimage-aux val x) 2
  :hints(("Goal" 
          :in-theory (enable preimage-aux)
          :induct (len-len-induction x x-equiv))))

(defthm preimage-aux-when-value-missing
  (implies (not (memberp val (strip-cdrs x)))
           (equal (preimage-aux val x)
                  nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm not-memberp-of-preimage-aux
  (implies (not (memberp key (strip-cars x)))
           (equal (memberp key (preimage-aux val x))
                  nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm unique-of-preimage-aux-when-unique-of-strip-cdrs
  (implies (BAG::unique (strip-cdrs x))
           (BAG::unique (preimage-aux val x)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm unique-of-preimage-aux-when-unique-of-strip-cars
  (implies (BAG::unique (strip-cars x))
           (BAG::unique (preimage-aux val x)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm memberp-of-caar-in-preimage-aux
  (implies (BAG::unique (strip-cars x))
           (equal (memberp (caar x) (preimage-aux a x))
                  (and (consp x)
                       (equal (cdar x) a))))
  :hints(("goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-when-not-member-of-cdr-of-strip-cdrs
  (implies (not (memberp a (cdr (strip-cdrs x))))
           (equal (preimage-aux a x)
                  (if (and (consp x)
                           (equal a (cdar x)))
                      (list (caar x))
                    nil)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-of-cdar-with-self
  (equal (preimage-aux (cdar x) x)
         (if (consp x)
             (cons (caar x) (preimage-aux (cdar x) (cdr x)))
           nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-of-cdr-when-not-cdar
  (implies (not (equal (cdar x) a))
           (equal (preimage-aux a (cdr x))
                  (if (consp x)
                      (preimage-aux a x)
                    nil)))
  :hints(("Goal" :in-theory (enable preimage-aux))))




;; Preimage simply calls Preimage-aux after deshadowing x.  This produces a
;; list of keys that would actually map to the desired value when given to
;; assoc.

(defund preimage (val x)
  (declare (xargs :guard (alistp x)))
  (preimage-aux val (deshadow x)))

(defcong alist-equiv equal (preimage val x) 2
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-when-value-missing
  (implies (not (memberp val (strip-cdrs x)))
           (equal (preimage val x)
                  nil))
  :hints(("Goal" :in-theory (enable preimage))))                
  
(defthm not-memberp-of-preimage
  (implies (not (memberp key (strip-cars x)))
           (equal (memberp key (preimage val x))
                  nil))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm unique-preimage
  (BAG::unique (preimage val x))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-deshadow
  (equal (preimage val (deshadow x))
         (preimage val x))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm memberp-of-caar-in-preimage
  (equal (memberp (caar x) (preimage a x))
         (and (consp x)
              (equal (cdar x) a)))
  :hints(("Goal" :in-theory (enable preimage)
          :use (:instance memberp-of-caar-in-preimage-aux
                          (x (deshadow x))))))

(defthm preimage-when-not-member-of-cdr-of-strip-cdrs
  (implies (not (memberp a (cdr (strip-cdrs x))))
           (equal (preimage a x)
                  (if (and (consp x)
                           (equal a (cdar x)))
                      (list (caar x))
                    nil)))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-cdar-with-self
  (equal (preimage (cdar x) x)
         (if (consp x)
             (cons (caar x) 
                   (preimage (cdar x) 
                             (clearkey (caar x) (cdr x))))
           nil))
  :hints(("Goal" :in-theory (e/d (preimage) 
                                 (preimage-aux-of-cdar-with-self))
          :use (:instance preimage-aux-of-cdar-with-self
                          (x (deshadow x))))))
         
(defthm preimage-of-cdr-when-not-cdar-and-unique
  (implies (and (not (equal (cdar x) a))
                (BAG::unique (strip-cars x)))
           (equal (preimage a (cdr x))
                  (if (consp x)
                      (preimage a x)
                    nil)))
  :hints(("Goal" :in-theory (enable preimage))))
