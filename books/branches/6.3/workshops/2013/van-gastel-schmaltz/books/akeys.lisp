#|$ACL2s-Preamble$;
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

;; also look into books/data-structures/alist-defthms.lisp


(include-book "data-structures/alist-defthms" :dir :system)

;; comon alist stuff, about assoc, acons, etc
(defthm not-assoc-implies-not-member-alist
  (implies (and (alistp alist)
                (not (assoc key alist)))
           (not (member-equal (cons key value) alist))))

(defthm acons-implies-alist
  (implies (alistp tail)
           (alistp (acons a b tail))))

(defthm cdr-acons-is-tail
  (equal (cdr (acons a b tail))
         tail)
  :hints (("Goal" :in-theory (enable acons))))
(defthm caar-acons-is-a
  (equal (caar (acons a b tail))
         a)
  :hints (("Goal" :in-theory (enable acons))))
(defthm caar-acons-is-b
  (equal (cdar (acons a b tail))
         b)
  :hints (("Goal" :in-theory (enable acons))))

(defthm acons-implies-consp-of-car
  (implies (and (consp alist)
                (alistp alist))
           (consp (car alist))))

(defthm alist-of-acons-implies-alist-of-tail
  (equal (alistp (acons a b tail))
         (alistp tail))
  :hints (("Goal" :in-theory (enable acons))))

(defthm alistp-stable-under-swap-of-arguments
  (equal (alistp (acons a b (acons c d tail)))
         (alistp (acons c d (acons a b tail)))))

;; stuff about strip-cars
(defthm strip-cars-preserves-consp
  (implies (alistp alist)
           (equal (consp (strip-cars alist))
                  (consp alist))))

(defthm strip-cars-preserves-subset-member-equal
  (implies (and (subsetp (strip-cars alist) aset)
                (assoc x alist))
           (member-equal x aset)))

(defthm assoc-equals-member-of-strip-cars
  (implies (alistp alist)
           (equal (not (member-equal x (strip-cars alist)))
                  (not (assoc x alist)))))

(defthm strip-cars-append-is-append-strip-cars
  (equal
   (strip-cars (binary-append a b))
   (binary-append (strip-cars a) (strip-cars b))))

(defthm not-member-strip-cars-implies-not-member-alist
  (implies (not (member-equal key (strip-cars alist)))
           (not (member-equal (cons key value) alist))))

(defthm strip-cars-is-a-truelistp
  (implies (alistp alist)
           (true-listp (strip-cars alist))))

(defthm not-member-strip-cars-implies-not-member-alist
  (implies (not (member-equal key (strip-cars alist)))
           (not (member-equal (cons key value) alist))))

(defthm member-cars
  (implies (and (member-equal a x)
                (subsetp (strip-cars x) y))
           (member-equal (car a) y)))

(defthm alist-implies-truelistp
  (implies (alistp x)
           (true-listp x)))#|ACL2s-ToDo-Line|#


;; OLD STUFF
#|


(defthm akeys-is-a-truelistp
  (implies (alistp alist)
           (true-listp (akeys alist))))

(defthm avalues-is-a-truelistp
  (implies (alistp alist)
           (true-listp (avalues alist))))

(defthm avalues-preserves-not-member
  (implies (and (alistp alist)
                (not (rassoc x alist)))
           (not (member-equal x (avalues alist)))))

(defthm avalues-preserves-consp
  (implies (and (alistp alist)
                (consp alist))
           (consp (avalues alist))))
|#

