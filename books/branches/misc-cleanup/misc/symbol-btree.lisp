(in-package "ACL2")

; CHALLENGE:  Get rid of ":mode :program: on the last two functions!

; A symbol-btree is a data structure of the form
; (symbol value left . right)
; where left and right are symbol-btrees.

; Example use:
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

; It would be interesting to prove the following theorem:

; (implies (symbol-alistp x)
;          (equal (symbol-btree-lookup key (symbol-alist-to-btree x))
;                 (assoc-eq key x)))

(defun symbol-btreep (x)
  (declare (xargs :guard t))
  (if x
      (and (true-listp x)
           (symbolp (car x))
           (or (null (caddr x))
               (and (symbol-btreep (caddr x))
                    (symbol-< (car (caddr x))
                              (car x))))
           (or (null (cdddr x))
               (and (symbol-btreep (cdddr x))
                    (symbol-< (car x)
                              (car (cdddr x))))))
    (null x)))

(defun symbol-btree-lookup (key btree)
  (declare (xargs :guard (and (symbolp key)
                              (symbol-btreep btree))))
  (cond
   ((endp btree)
    nil)
   ((eq key (car btree))
    (cadr btree))
   ((symbol-< key (car btree))
    (symbol-btree-lookup key (caddr btree)))
   (t
    (symbol-btree-lookup key (cdddr btree)))))

; Now, based on merge-sort-symbol-<:

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

(local
 (defthm len-evens-<
  (implies (consp (cdr x))
           (< (len (evens x))
              (len x)))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear))

(local
 (defthm len-evens-<=
   (<= (len (evens x))
       (len x))
   :hints (("Goal" :induct (evens x)))
   :rule-classes :linear))

(defun merge-sort-symbol-alist-< (l)
  (declare (xargs :guard (symbol-alistp l)
                  :verify-guards nil
                  :measure (len l)))
  (cond ((endp (cdr l)) l)
        (t (merge-symbol-alist-< (merge-sort-symbol-alist-< (evens l))
                                 (merge-sort-symbol-alist-< (odds l))
                                 nil))))

; Start guard proof for merge-sort-symbol-alist-<.

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

#|
(skip-proofs
 (defthm floor-2-<
   (implies (not (zp n))
            (< (floor n 2) n))
   :rule-classes :linear))

(skip-proofs
 (defthm floor-2-nonnegative
   (implies (and (integerp n) (<= 0 n))
            (<= 0 (floor n 2)))
   :rule-classes :type-prescription))

(local (in-theory (disable floor)))
|#

(defun sorted-symbol-alist-to-symbol-btree (x n)
  ;; Return 2 values:
  ;; symbol-btree corresponding to first n entries of x;
  ;; the rest of x.
  (declare (xargs :guard (and (integerp n) (<= 0 n)
                              (true-listp x))
                  :mode :program))
  (cond
   ((zp n)
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

(defun symbol-alist-to-btree (alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :mode :program))
  (let ((n (length alist))
        (sorted-alist (merge-sort-symbol-alist-< alist)))
    (mv-let (ans empty)
            (sorted-symbol-alist-to-symbol-btree sorted-alist n)
            (declare (ignore empty))
            ans)))

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
  (declare (xargs :mode :program))
  (symbol-alist-to-btree
   (symbol-btree-to-alist btree)))

