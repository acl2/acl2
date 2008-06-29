;; Original author: ???
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

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

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

(local (defthm alistp-of-cdr
         (implies (alistp x)
                  (alistp (cdr x)))))

(local (defthm true-listp-when-alistp
         (implies (alistp x)
                  (true-listp x))))

(local (defthm consp-under-iff-when-true-listp
         (implies (true-listp x)
                  (iff (consp x)
                       x))))

(local (defthm consp-of-car-when-alistp
         (implies (alistp x)
                  (equal (consp (car x))
                         (consp x)))))

(local (defthm symbol-alistp-of-append
         (implies (and (symbol-alistp x)
                       (symbol-alistp y))
                  (symbol-alistp (append x y)))))

(local (defthm alistp-when-symbol-alistp
         (implies (symbol-alistp x)
                  (alistp x))))



(defun symbol-btreep (x)
  (declare (xargs :guard t))
  (or (not x)
      (and (true-listp x)
           (symbolp (car x))
           (or (null (caddr x))
               (and (symbol-btreep (caddr x))
                    (symbol-< (car (caddr x))
                              (car x))))
           (or (null (cdddr x))
               (and (symbol-btreep (cdddr x))
                    (symbol-< (car x)
                              (car (cdddr x))))))))

(defun symbol-btree-lookup (key btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond ((atom btree)
         nil)
        ((eq key (car btree))
         (cadr btree))
        ((symbol-< key (car btree))
         (symbol-btree-lookup key (caddr btree)))
        (t
         (symbol-btree-lookup key (cdddr btree)))))

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





(defun sorted-symbol-alist-to-symbol-btree (x n)
  ;; Return 2 values:
  ;;   (1) the symbol-btree corresponding to first n entries of x; and
  ;;   (2) the rest of x.
  (declare (xargs :guard (and (natp n)
                              (alistp x))
                  :verify-guards nil))
  (cond ((zp n)
         (mv nil x))
        ((endp (cdr x))
         (mv (list (caar x) (cdar x))
             (cdr x)))
        (t
         (let ((n2 (floor n 2)))
           (mv-let (left restx)
                   (sorted-symbol-alist-to-symbol-btree x n2)
                   (mv-let (right restx2)
                           (sorted-symbol-alist-to-symbol-btree (cdr restx) (- n (1+ n2)))
                           (mv (list* (caar restx)
                                      (cdar restx)
                                      left
                                      right)
                               restx2)))))))

(local (defthm alistp-of-mv-nth-1-of-sorted-symbol-alist-to-symbol-btree
         (implies (alistp x)
                  (equal (alistp (mv-nth 1 (sorted-symbol-alist-to-symbol-btree x n)))
                         t))))

(local (defthm consp-of-mv-nth-1-of-sorted-symbol-alist-to-symbol-btree
         (implies (alistp x)
                  (equal (consp (mv-nth 1 (sorted-symbol-alist-to-symbol-btree x n)))
                         (if (mv-nth 1 (sorted-symbol-alist-to-symbol-btree x n))
                             t
                           nil)))))

(verify-guards sorted-symbol-alist-to-symbol-btree
               :hints(("Goal" 
                       :do-not '(generalize fertilize eliminate-destructors)
                       :in-theory (disable alistp)
                       )))





(defun symbol-alist-to-btree (alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :verify-guards nil))
  (let ((n (length alist))
        (sorted-alist (merge-sort-symbol-alist-< alist)))
    (mv-let (ans empty)
            (sorted-symbol-alist-to-symbol-btree sorted-alist n)
            (declare (ignore empty))
            ans)))

(verify-guards symbol-alist-to-btree)




(defun symbol-btree-update (key val btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((endp btree)
    (list* key val nil nil))
   ((eq key (car btree))
    (list* key val (caddr btree) (cdddr btree)))
   ((symbol-< key (car btree))
    (list* (car btree) (cadr btree)
           (symbol-btree-update key val (caddr btree))
           (cdddr btree)))
   (t
    (list* (car btree) (cadr btree)
           (caddr btree)
           (symbol-btree-update key val (cdddr btree))))))

(defun symbol-btree-to-alist (x)
  (declare (xargs :guard (symbol-btreep x)
                  :verify-guards nil))
  (if (consp x)
      (cons (cons (car x) (cadr x))
            (append (symbol-btree-to-alist (caddr x))
                    (symbol-btree-to-alist (cdddr x))))
    nil))

(defthm true-listp-symbol-btree-to-alist
  (true-listp (symbol-btree-to-alist btree))
  :rule-classes :type-prescription)

(verify-guards symbol-btree-to-alist)



(defun rebalance-symbol-btree (btree)
  (declare (xargs :guard (symbol-btreep btree)))
  (symbol-alist-to-btree
   (symbol-btree-to-alist btree)))

