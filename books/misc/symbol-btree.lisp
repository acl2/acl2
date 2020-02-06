; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; Original author: Matt Kaufmann
;; Updated June 29, 2008 by Jared Davis to bring everything into logic mode.

;; A symbol-btree is a data structure of the form (symbol value left . right)
;; where left and right are symbol-btrees.

;; Example use:
#|
ACL2 !>(assign btree (symbol-alist-to-btree '((c . 3) (a . 1) (b . 2) (d . 4))))
(C 3 (B 2 (A 1 NIL)) D 4)
ACL2 !>(symbol-btree-lookup 'd (@ btree))
4
ACL2 !>(symbol-btree-lookup 'e (@ btree))
NIL
ACL2 !>(symbol-btree-lookup 'c (@ btree))
3
ACL2 !>
|#

;; This book is not very complete.  There are tons of obvious theorems to prove,
;; like lookup of update, etc., and the equivalence of lookups after
;; rebalancing.  But I (Jared) am too lazy to do this, and only wanted to bring
;; these functions into :logic mode.  Also, I tried to maintain total
;; compatibility with the previous version, except for local events and the new
;; :logic mode functions.

(in-package "ACL2")



(defun symbol-btreep (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (listp (cdr x))
         (symbol-btreep (cadr x))
         (symbol-btreep (cddr x)))))


(defun symbol-btree-update (key val btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((endp btree)
    (list (cons key val)))
   ((and (mbt (consp (car btree)))
         (eq key (caar btree)))
    (list* (cons key val) (cadr btree) (cddr btree)))
   ((symbol-< key (caar btree))
    (list* (car btree)
           (symbol-btree-update key val (cadr btree))
           (cddr btree)))
   (t
    (list* (car btree)
           (cadr btree)
           (symbol-btree-update key val (cddr btree))))))

(defthm symbol-btreep-symbol-btree-update
  (implies (and (symbol-btreep x)
                (symbolp key))
           (symbol-btreep (symbol-btree-update key val x))))


(defun symbol-btree-find (key btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond ((atom btree)
         nil)
        ((and (mbt (consp (car btree)))
              (eq key (caar btree)))
         (car btree))
        ((symbol-< key (caar btree))
         (symbol-btree-find key (cadr btree)))
        (t
         (symbol-btree-find key (cddr btree)))))

(defun symbol-btree-lookup (key btree)
  (declare (xargs :guard (and (symbolp key) (symbol-btreep btree))))
  (cdr (symbol-btree-find key btree)))



(defthm symbol-btree-find-symbol-btree-update
  (equal (symbol-btree-find k1 (symbol-btree-update k2 val x))
         (if (equal k1 k2)
             (cons k1 val)
           (symbol-btree-find k1 x)))
  :hints(("Goal" :in-theory (disable symbol-<-transitive
                                     symbol-<-trichotomy
                                     symbol-<-asymmetric))))






(defun symbol-btree-to-alist-aux (x acc)
  (declare (Xargs :guard (symbol-btreep x)))
  (if (consp x)
      (symbol-btree-to-alist-aux
       (cadr x)
       (if (mbt (consp (car x)))
           (cons (car x)
                 (symbol-btree-to-alist-aux (cddr x) acc))
         (symbol-btree-to-alist-aux (cddr x) acc)))
    acc))

(defun symbol-btree-to-alist (x)
  (declare (xargs :guard (symbol-btreep x)
                  :verify-guards nil))
  (mbe :logic
       (if (consp x)
           (append (symbol-btree-to-alist (cadr x))
                   (if (mbt (consp (car x)))
                       (cons (car x)
                             (symbol-btree-to-alist (cddr x)))
                     (symbol-btree-to-alist (cddr x))))
         nil)
       :exec (symbol-btree-to-alist-aux x nil)))


(defthm symbol-btree-to-alist-aux-is-symbol-btree-to-alist
  (equal (symbol-btree-to-alist-aux x acc)
         (append (symbol-btree-to-alist x) acc)))

(defthm true-listp-symbol-btree-to-alist
  (true-listp (symbol-btree-to-alist btree))
  :rule-classes :type-prescription)

(defthm symbol-alistp-symbol-btree-to-alist
  (implies (symbol-btreep x)
           (symbol-alistp (symbol-btree-to-alist x))))

(defthm alistp-symbol-btree-to-alist
  (implies (symbol-btreep x)
           (alistp (symbol-btree-to-alist x))))

(verify-guards symbol-btree-to-alist)






(defun symbol-alist-sortedp (x)
  (declare (xargs :guard (symbol-alistp x)))
  (if (atom (cdr x))
      t
    (and (symbol-< (caar x) (caadr x))
         (symbol-alist-sortedp (cdr x)))))



(local
 (progn

   (defthm symbol-btree-find-thm-car
     (equal (car (symbol-btree-find key x))
            (and (symbol-btree-find key x)
                 key)))

   (defthm assoc-equal-of-append
     (implies (alistp a)
              (equal (assoc key (append a b))
                     (or (assoc key a)
                         (assoc key b)))))


   (local (defthmd equal-of-booleans
            (implies (and (booleanp a) (booleanp b))
                     (equal (equal a b) (iff a b)))))

   (defthm symbol-alist-sortedp-append
     (equal (symbol-alist-sortedp (append a b))
            (and (symbol-alist-sortedp a)
                 (symbol-alist-sortedp b)
                 (or (atom a) (atom b)
                     (and (symbol-< (caar (last a)) (caar b)) t))))
     :hints(("Goal" :in-theory
             (e/d (equal-of-booleans)
                  (true-listp-append
                   true-listp
                   (:type-prescription symbol-<)
                   symbol-<-transitive
                   symbol-<-trichotomy
                   symbol-<-asymmetric)))))


   (defthm symbol-alist-sortedp-and-symbol-<-last-implies-not-assoc
     (implies (and (symbol-alistp x)
                   (symbol-alist-sortedp x)
                   (symbol-< (caar (last x)) key))
              (not (assoc key x))))

   (defthm symbol-alist-sortedp-and-symbol-<-first-implies-not-assoc
     (implies (and (symbol-alistp x)
                   (symbol-alist-sortedp x)
                   (symbol-< key (caar x)))
              (not (assoc key x))))

   (defthm symbolp-caar-last-of-symbol-alistp
     (implies (symbol-alistp x)
              (symbolp (caar (last x)))))))

(local
 (defthm assoc-when-not-symbolp-key
   (implies (and (not (symbolp key))
                 (symbol-alistp x))
            (equal (assoc key x) nil))))

(local
 (defthm symbol-btree-find-when-not-symbolp-key
   (implies (and (not (symbolp key))
                 (symbol-btreep x))
            (equal (symbol-btree-find key x) nil))))

(local (defthm assoc-in-symbol-btree-to-alist-when-symbolp-key
         (implies (and (symbol-btreep x)
                       (symbol-alist-sortedp (symbol-btree-to-alist x))
                       (symbolp key))
                  (equal (assoc key (symbol-btree-to-alist x))
                         (symbol-btree-find key x)))
         :hints(("Goal" :in-theory (disable default-car default-cdr alistp
                                            true-listp-symbol-btree-to-alist
                                            true-listp-append)
                 :induct (symbol-btree-find key x)
                 :expand ((symbol-btree-find key x))))))

(defthm assoc-in-symbol-btree-to-alist
  (implies (and (symbol-btreep x)
                (symbol-alist-sortedp (symbol-btree-to-alist x)))
           (equal (assoc key (symbol-btree-to-alist x))
                  (symbol-btree-find key x)))
  :hints(("Goal" :cases ((symbolp key)))))




(local
 (progn
   (defthm consp-symbol-btree-to-alist
     (implies (symbol-btreep x)
              (iff (consp (symbol-btree-to-alist x))
                   (consp x))))

   (defthm car-append
     (equal (car (append a b))
            (if (consp a) (car a) (car b))))

   (defthm not-symbol-<-transitive1
     (implies (and (not (symbol-< x y))
                   (not (symbol-< y z))
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< x z)))
     :hints (("goal" :use (:instance symbol-<-transitive
                           (x z) (y y) (z x)))))

   (defthm not-symbol-<-transitive2
     (implies (and (not (symbol-< y z))
                   (not (symbol-< x y))
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< x z)))
     :hints (("goal" :use (:instance symbol-<-transitive
                           (x z) (y y) (z x)))))

   (defthm symbol-<-transitive1
     (implies (and (symbol-< x y)
                   (symbol-< y z)
                   (symbolp x) (symbolp y) (symbolp z))
              (symbol-< x z)))

   (defthm symbol-<-transitive2
     (implies (and (symbol-< y z)
                   (symbol-< x y)
                   (symbolp x) (symbolp y) (symbolp z))
              (symbol-< x z)))


   (defthm symbol-<=/<-transitive2
     (implies (and (symbol-< y z)
                   (not (symbol-< y x))
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< z x))))

   (defthm symbol-</<=-transitive1
     (implies (and (symbol-< x y)
                   (not (symbol-< z y))
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< z x))))

   (defthm symbol-</<=-transitive2
     (implies (and (not (symbol-< z y))
                   (symbol-< x y)
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< z x))))

   (defthm symbol-<=/<-transitive1
     (implies (and (not (symbol-< y x))
                   (symbol-< y z)
                   (symbolp x) (symbolp y) (symbolp z))
              (not (symbol-< z x))))



   (local (in-theory (disable symbol-<-transitive)))

   (deftheory symbol-<-transitivity
     '(symbol-<-transitive1
       symbol-<-transitive2
       not-symbol-<-transitive1
       not-symbol-<-transitive2
       symbol-</<=-transitive1
       symbol-</<=-transitive2
       symbol-<=/<-transitive1
       symbol-<=/<-transitive2))

   (in-theory (disable symbol-<-transitivity))

   (defthm symbolp-caar-symbol-btree-to-alist
     (implies (symbol-btreep x)
              (symbolp (caar (symbol-btree-to-alist x)))))

   (defthm not-symbol-<-last-sorted
     (implies (and (symbol-alistp x)
                   (symbol-alist-sortedp x))
              (not (symbol-< (caar (last x)) (caar x))))
     :hints(("Goal" :in-theory (enable symbol-<-transitive1))))

   (defthm caar-symbol-btree-update-to-alist-sorted
     (implies (and (symbol-btreep x)
                   (symbol-alist-sortedp (symbol-btree-to-alist x))
                   (symbolp key))
              (equal (caar (symbol-btree-to-alist (symbol-btree-update
                                                   key val x)))
                     (if (and x (symbol-< (caar (symbol-btree-to-alist x)) key))
                         (caar (symbol-btree-to-alist x))
                       key)))
     :hints(("Goal" :in-theory (e/d (symbol-<-transitivity)
                                    (default-car default-cdr
                                      true-listp-symbol-btree-to-alist
                                      alistp
                                      symbol-</<=-transitive2
                                      not-symbol-<-transitive1
                                      symbol-<-transitive1
                                      symbol-</<=-transitive1
                                      symbol-<=/<-transitive1
                                      (:type-prescription
                                       symbol-btree-to-alist))))))

   (defthm last-append
     (equal (car (last (append a b)))
            (if (consp b)
                (car (last b))
              (car (last a)))))

   (defthm caar-last-symbol-btree-update-to-alist-sorted
     (implies (and (symbol-btreep x)
                   (symbol-alist-sortedp (symbol-btree-to-alist x))
                   (symbolp key))
              (equal (caar (last (symbol-btree-to-alist (symbol-btree-update
                                                         key val x))))
                     (if (and x (symbol-< key (caar (last (symbol-btree-to-alist x)))))
                         (caar (last (symbol-btree-to-alist x)))
                       key)))
     :hints(("Goal" :in-theory (e/d (symbol-<-transitivity)
                                    (default-car default-cdr
                                      true-listp-symbol-btree-to-alist
                                      alistp
                                      symbol-</<=-transitive2
                                      symbol-<-transitive1
                                      (:type-prescription last)
                                      (:type-prescription symbol-btree-to-alist))))))))

(defthm symbol-alist-sortedp-symbol-btree-update
  (implies (and (symbol-btreep x)
                (symbol-alist-sortedp (symbol-btree-to-alist x))
                (symbolp key))
           (symbol-alist-sortedp (symbol-btree-to-alist (symbol-btree-update
                                                         key val x))))
  :hints(("Goal" :in-theory (disable symbol-alist-sortedp
                                     symbol-btree-to-alist
                                     (:definition symbol-btree-update))
          :induct t
          :expand ((:free (x y) (symbol-alist-sortedp (cons x y)))
                   (:free (x y) (symbol-btree-to-alist (cons x y)))
                   (symbol-btree-to-alist x)
                   (symbol-btree-to-alist nil)
                   (:free (key) (symbol-btree-update key val x))
                   (:free (key) (symbol-btree-update key val nil))))))


(local
 (encapsulate nil
   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (in-theory (disable floor))
   (defthm floor-x-2-natp
     (implies (natp x)
              (natp (floor x 2)))
     :rule-classes :type-prescription)
   (defthm floor-x-2-<=-x
     (implies (natp x)
              (<= (floor x 2) x))
     :rule-classes :linear)
   (defthm floor-x-2-<-x
     (implies (and (integerp x)
                   (< 0 x))
              (< (floor x 2) x))
     :rule-classes :linear)))


(defun symbol-alist-to-btree-aux (x n)
  ;; Return 2 values:
  ;;   (1) the symbol-btree corresponding to first n entries of x; and
  ;;   (2) the rest of x.
  (declare (xargs :guard (and (natp n)
                              (alistp x))
                  :verify-guards nil))
  (cond ((zp n)
         (mv nil x))
        ((eql n 1)
         (mv (list (car x)) (cdr x)))
        (t
         (let ((n2 (floor n 2)))
           (mv-let (left restx)
                   (symbol-alist-to-btree-aux x n2)
                   (mv-let (right restx2)
                           (symbol-alist-to-btree-aux (cdr restx) (- n (1+ n2)))
                           (mv (cons (car restx)
                                     (cons left right))
                               restx2)))))))




(local
 (encapsulate nil
   (local (include-book "arithmetic/top" :dir :system))
   (defthmd nthcdr-cdr
     (equal (nthcdr n (cdr x))
            (nthcdr (+ 1 (nfix n)) x)))

   (defthmd cdr-nthcdr
     (equal (cdr (nthcdr n x))
            (nthcdr (+ 1 (nfix n)) x)))

   (defthmd car-nthcdr
     (equal (car (nthcdr n x))
            (nth n x)))

   (defthm nthcdr-nthcdr
     (equal (nthcdr n (nthcdr m x))
            (nthcdr (+ (nfix n) (nfix m)) x)))

   (local (defthmd nthcdr-fudge
            (implies (and (not (zp n))
                          (atom x))
                     (not (nthcdr n x)))))

   (defthm symbol-alist-to-btree-aux-is-nthcdr
     (equal (mv-nth 1 (symbol-alist-to-btree-aux x n))
            (nthcdr n x))
     :hints (("goal" :induct t
              :in-theory (enable nthcdr-fudge nthcdr-cdr))
             (and stable-under-simplificationp
                  '(:expand ((nthcdr n x))
                    :in-theory (disable nthcdr-cdr)))))



   (defthm symbol-alistp-nthcdr
     (implies (symbol-alistp x)
              (symbol-alistp (nthcdr n x))))

   (defthm alistp-nthcdr
     (implies (alistp x)
              (alistp (nthcdr n x))))


   (defthm len-nthcdr
     (equal (len (nthcdr n x))
            (nfix (- (len x) (nfix n))))
     :hints(("Goal" :in-theory (enable nthcdr-cdr))))

   (defthm symbol-alist-sortedp-nthcdr
     (implies (symbol-alist-sortedp x)
              (symbol-alist-sortedp
               (nthcdr n x))))))

(encapsulate nil
  (local (defthm consp-nthcdr-when-alistp
           (implies (alistp x)
                    (iff (consp (nthcdr n x))
                         (nthcdr n x)))))

  (local (defthm consp-car-nthcdr-when-alistp
           (implies (alistp x)
                    (iff (consp (car (nthcdr n x)))
                         (car (nthcdr n x))))))

  (verify-guards symbol-alist-to-btree-aux
    :hints(("Goal" :in-theory (e/d (cdr-nthcdr))))))



(local
 (encapsulate nil
   (defthm symbolp-car-nth-of-symbol-alist
     (implies (symbol-alistp x)
              (symbolp (car (nth n x)))))
   (local (defthm consp-nth-of-symbol-alist
            (implies (and (symbol-alistp x)
                          (< (nfix n) (len x)))
                     (consp (nth n x)))))
   (defthm symbol-btreep-symbol-alist-to-btree-aux
     (implies (and (symbol-alistp x)
                   (<= n (len x)))
              (symbol-btreep (car (symbol-alist-to-btree-aux x n))))
     :hints(("Goal" :in-theory (e/d (car-nthcdr cdr-nthcdr)
                                    (symbol-btreep
                                     (:definition symbol-alist-to-btree-aux)
                                     default-+-2 default-+-1
                                     ;; floor-type-1 floor-type-2 floor-type-3
                                     ;; floor-=-x/y
                                     default-car default-cdr))
             :induct t
             :expand ((:free (x y) (symbol-btreep (cons x y)))
                      (symbol-btreep nil)
                      (symbol-alist-to-btree-aux x n)
                      (symbol-alist-to-btree-aux x 1)))))))





(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local
 (encapsulate nil
   (local (include-book "arithmetic/top" :dir :system))
   (defthm cons-nth-take-nthcdr
     (implies (and (integerp n)
                   (integerp k)
                   (<= 0 n)
                   (<= 0 k)
                   (<= n (len x))
                   (equal m (+ 1 n)))
              (equal (cons (nth n x)
                           (take k (nthcdr m x)))
                     (take (+ 1 k) (nthcdr n x))))
     :hints (("goal"
              :expand ((:free (x) (take (+ 1 k) x))))))

   (defthm take-append
     (implies (and (natp n) (natp k))
              (equal (append (take n x)
                             (take k (nthcdr n x)))
                     (take (+ n k) x)))
     :hints (("goal" :induct (take n x)
              :in-theory (enable take))))

   (defthm consp-nth-symbol-alist
     (implies (and (symbol-alistp x)
                   (< (nfix n) (len x)))
              (consp (nth n x))))

   (defthm consp-nth-alist
     (implies (and (alistp x)
                   (< (nfix n) (len x)))
              (consp (nth n x))))

   (defthm
     symbol-btree-to-alist-of-symbol-alist-to-btree-aux
     (implies (and (alistp x)
                   (<= (nfix n) (len x)))
              (equal
               (symbol-btree-to-alist
                ;; (mv-nth 0, ugh
                (car (symbol-alist-to-btree-aux x n)))
               (take n x)))
     :hints (("goal" :induct (symbol-alist-to-btree-aux x n)
              :in-theory (e/d (cdr-nthcdr car-nthcdr)
                              ((:definition symbol-alist-to-btree-aux)
                               default-car default-cdr zp-open default-+-2
                               |x < y  =>  0 < -x+y|
                               |x < y  =>  0 < y-x|
                               symbol-btree-to-alist
                               ;; floor-type-1 floor-type-2
                               ;; floor-type-3 floor-type-4
                               ;; floor-=-x/y
                               default-+-1 default-<-1 default-<-2
                               true-listp-symbol-btree-to-alist
                               (:type-prescription take)
                               (:type-prescription symbol-btree-to-alist)
                               (:type-prescription symbol-alist-sortedp)
                               (:type-prescription symbol-alistp)
                               true-listp-append
                               (:type-prescription symbol-<)
                               (:type-prescription eqlable-alistp)
                               (:type-prescription alistp)
                               (:type-prescription binary-append)
                               nthcdr))
              :expand ((symbol-alist-to-btree-aux x n)
                       (symbol-alist-to-btree-aux x 1)
                       (:free (a b)
                              (symbol-btree-to-alist (cons a b)))))
             (and stable-under-simplificationp
                  '(:expand ((take n x))))))))


(local (defthm len-evens-<
         (implies (consp (cdr x))
                  (< (len (evens x))
                     (len x)))
         :hints (("Goal" :induct (evens x)))
         :rule-classes :linear))

(local (defthm len-evens-<=
         (<= (len (evens x))
             (len x))
         :hints (("Goal" :induct (evens x)))
         :rule-classes :linear))





(defun merge-symbol-alist-< (l1 l2 acc)
  (declare (xargs :guard (and (symbol-alistp l1)
                              (symbol-alistp l2)
                              (true-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((symbol-< (caar l1) (caar l2))
         (merge-symbol-alist-< (cdr l1) l2 (cons (car l1) acc)))
        (t (merge-symbol-alist-< l1 (cdr l2) (cons (car l2) acc)))))

(defun merge-sort-symbol-alist-< (l)
  (declare (xargs :guard (symbol-alistp l)
                  :verify-guards nil
                  :measure (len l)))
  (cond ((endp (cdr l)) l)
        (t (merge-symbol-alist-< (merge-sort-symbol-alist-< (evens l))
                                 (merge-sort-symbol-alist-< (odds l))
                                 nil))))

(defthm symbol-alistp-merge-symbol-alist-<
  (implies (and (symbol-alistp x)
                (symbol-alistp y)
                (symbol-alistp acc))
           (symbol-alistp (merge-symbol-alist-< x y acc))))

(defthm symbol-alistp-evens
  (implies (symbol-alistp x)
           (symbol-alistp (evens x)))
  :hints (("Goal" :induct (evens x))))

(defthm symbol-alistp-merge-sort-symbol-alist-<
  (implies (symbol-alistp x)
           (symbol-alistp (merge-sort-symbol-alist-< x))))

(verify-guards merge-sort-symbol-alist-<)


(local (defthmd alistp-when-symbol-alistp
         (implies (symbol-alistp x)
                  (alistp x))))

(defun symbol-alist-to-btree (alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :guard-hints
                  (("Goal" :in-theory
                    (enable alistp-when-symbol-alistp)))))
  (let ((n (length alist))
        (sorted-alist (merge-sort-symbol-alist-< alist)))
    (mv-let (ans empty)
      (symbol-alist-to-btree-aux sorted-alist n)
      (declare (ignore empty))
      ans)))





(defun rebalance-symbol-btree (btree)
  (declare (xargs :guard (symbol-btreep btree)))
  (let ((alist (symbol-btree-to-alist btree)))
    (mv-let (btree empty)
      (symbol-alist-to-btree-aux alist (length alist))
      (declare (ignore empty))
      btree)))

(defthm symbol-btreep-rebalance
  (implies (symbol-btreep x)
           (symbol-btreep (rebalance-symbol-btree x))))


(local (encapsulate nil
         (local (include-book "arithmetic/top" :dir :system))
         (defthm take-of-own-len
           (implies (true-listp x)
                    (equal (take (len x) x)
                           x)))))
(defthm symbol-btree-to-alist-of-rebalance-symbol-btree
  (implies (symbol-btreep x)
           (equal (symbol-btree-to-alist (rebalance-symbol-btree x))
                  (symbol-btree-to-alist x))))


(defthm symbol-btree-find-rebalance
  (implies (and (symbol-btreep x)
                (symbol-alist-sortedp
                 (symbol-btree-to-alist x)))
           (equal (symbol-btree-find key (rebalance-symbol-btree x))
                  (symbol-btree-find key x)))
  :hints(("Goal" :in-theory (disable assoc-in-symbol-btree-to-alist
                                     rebalance-symbol-btree)
          :use ((:instance assoc-in-symbol-btree-to-alist
                 (x (rebalance-symbol-btree x)))
                (:instance assoc-in-symbol-btree-to-alist
                 (x x)))
          :do-not-induct t)))

(in-theory (disable rebalance-symbol-btree))


(defun symbol-btree-key-depth (key btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((or (endp btree)
        (and (mbt (consp (car btree)))
              (eq key (caar btree)))) 0)
   ((symbol-< key (caar btree))
    (+ 1 (symbol-btree-key-depth key (cadr btree))))
   (t
    (+ 1 (symbol-btree-key-depth key (cddr btree))))))



(defun symbol-btree-find/depth-aux (key btree depth)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree)
                              (natp depth))))
  (cond ((atom btree) (mv nil (+ 0 depth)))
        ((and (mbt (consp (car btree)))
              (eq key (caar btree)))
         (mv (car btree) (+ 0 depth)))
        ((symbol-< key (caar btree))
         (symbol-btree-find/depth-aux key (cadr btree) (+ 1 depth)))
        (t
         (symbol-btree-find/depth-aux key (cddr btree) (+ 1 depth)))))

(defthm symbol-btree-find/depth-aux-redef
  (equal (symbol-btree-find/depth-aux key btree depth)
         (mv (symbol-btree-find key btree)
             (+ depth (symbol-btree-key-depth key btree)))))

(defun symbol-btree-find/depth (key btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (mbe :logic
       (cond ((atom btree) (mv nil 0))
             ((and (mbt (consp (car btree)))
                   (eq key (caar btree)))
              (mv (car btree) 0))
             ((symbol-< key (caar btree))
              (mv-let (pair depth)
                (symbol-btree-find/depth key (cadr btree))
                (mv pair (+ 1 depth))))
             (t
              (mv-let (pair depth)
                (symbol-btree-find/depth key (cddr btree))
                (mv pair (+ 1 depth)))))
       :exec (symbol-btree-find/depth-aux key btree 0)))

(defthm symbol-btree-find/depth-redef
  (equal (symbol-btree-find/depth key btree)
         (mv (symbol-btree-find key btree)
             (symbol-btree-key-depth key btree))))



(defun symbol-btree-update/depth (key val btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((endp btree)
    (mv (list (cons key val)) 0))
   ((and (mbt (consp (car btree)))
         (eq key (caar btree)))
    (mv (list* (cons key val) (cadr btree) (cddr btree))
        0))
   ((symbol-< key (caar btree))
    (mv-let (sub depth)
      (symbol-btree-update/depth key val (cadr btree))
      (mv (list* (car btree)
                 sub
                 (cddr btree))
          (+ 1 depth))))
   (t
    (mv-let (sub depth)
      (symbol-btree-update/depth key val (cddr btree))
      (mv (list* (car btree)
                 (cadr btree)
                 sub)
          (+ 1 depth))))))

(defthm symbol-btree-update/depth-redef
  (equal (symbol-btree-update/depth key val btree)
         (mv (symbol-btree-update key val btree)
             (symbol-btree-key-depth key btree))))


(defun symbol-btree-update/find/depth (key val btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((endp btree)
    (mv (list (cons key val)) nil 0))
   ((and (mbt (consp (car btree)))
         (eq key (caar btree)))
    (mv (list* (cons key val) (cadr btree) (cddr btree))
        (car btree)
        0))
   ((symbol-< key (caar btree))
    (mv-let (sub pair depth)
      (symbol-btree-update/find/depth key val (cadr btree))
      (mv (list* (car btree)
                 sub
                 (cddr btree))
          pair
          (+ 1 depth))))
   (t
    (mv-let (sub pair depth)
      (symbol-btree-update/find/depth key val (cddr btree))
      (mv (list* (car btree)
                 (cadr btree)
                 sub)
          pair
          (+ 1 depth))))))

(defthm symbol-btree-update/find/depth-redef
  (equal (symbol-btree-update/find/depth key val btree)
         (mv (symbol-btree-update key val btree)
             (symbol-btree-find key btree)
             (symbol-btree-key-depth key btree))))
