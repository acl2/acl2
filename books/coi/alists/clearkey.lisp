#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; clearkey.lisp
;; Introduces the clearkey function and some theorems about it
;;
;; The function clearkey removes from an alist all pairs whose strip-cars are
;; the same as k.
;;
;; Note (jcd): originally clearkey operated by consing the car of the alist
;; onto the recursive call.  Now, we consfix this element before consing it
;; onto the recursive call, so that we always create an alist.  Essentially,
;; this "alist-fixes" the result for us.

(in-package "ALIST")
(include-book "equiv")
(include-book "basic" :dir :bags)

(defund clearkey (k x)
  (declare (xargs :guard (alistp x)))
  (if (consp x)
      (if (equal k (caar x))
          (clearkey k (cdr x))
        (cons (consfix (car x))
              (clearkey k (cdr x))))
    nil))

(defcong alist-equiv equal (clearkey k x) 2
  :hints(("Goal" 
          :in-theory (enable clearkey)
          :induct (LIST::len-len-induction x x-equiv))))

(defthm alistp-of-clearkey
  (alistp (clearkey k x))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-of-cons
  (equal (clearkey k (cons a x))
         (if (equal k (car a))
             (clearkey k x)
           (cons (consfix a) (clearkey k x))))
  :hints(("Goal" :in-theory (enable clearkey))))

; no theorem about car-of-clearkey, too hard to describe
; no theorem about cdr-of-clearkey, too hard to describe

(defthm len-of-clearkey-bound-tight
  (implies (memberp k (strip-cars x))
           (< (len (clearkey k x))
              (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm len-of-clearkey-bound-tight-rewrite
  (implies (memberp k (strip-cars x))
           (equal (< (len (clearkey k x)) (len x))
                  t)))

(defthm len-of-clearkey-bound-weak
  (<= (len (clearkey k x))
      (len x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm len-of-clearkey-bound-weak-rewrite
  (equal (< (len x) (len (clearkey k x)))
         nil))

;; no theorem about clearkey-of-firstn, too awkward to describe
;; no theorem about clearkey-of-nthcdr, too awkward to describe

(defthm clearkey-of-append
  (equal (clearkey k (append x y))
         (append (clearkey k x)
                 (clearkey k y)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-reorder
  (equal (clearkey k1 (clearkey k2 r))
         (clearkey k2 (clearkey k1 r)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-when-non-memberp
  (implies (not (memberp key (strip-cars x)))
           (equal (clearkey key x)
                  (alistfix x)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-caar-when-unique
  (implies (and (consp x)
                (BAG::unique (strip-cars x)))
           (equal (clearkey (caar x) (cdr x))
                  (alistfix (cdr x)))))

(defthm strip-cars-of-clearkey
  (equal (strip-cars (clearkey k x))
         (BAG::remove-all k (strip-cars x)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-idempotent
  (equal (clearkey k (clearkey k r))
         (clearkey k r)))

(defthm not-memberp-of-strip-cdrs-of-clearkey
  (implies (not (memberp val (strip-cdrs x)))
           (not (memberp val (strip-cdrs (clearkey key x)))))
  :hints(("Goal" :in-theory (enable clearkey))))

