(in-package "ACL2")
(include-book "extra")

(defun number-to-element (l pos)
  (declare (xargs :guard (acl2-numberp pos)))
  (if (atom l)
      nil
    (cons (cons pos (car l))
          (number-to-element (cdr l) (1+ pos)))))

(defthm number-to-element-when-not-consp
  (implies (not (consp l))
           (equal (number-to-element l pos)
                  nil)))

(defthm number-to-element-of-consp
  (equal (number-to-element (cons first rest) pos)
         (cons (cons pos first)
               (number-to-element rest (1+ pos)))))

(dis+ind number-to-element)

(defthm alistp-number-to-element
  (alistp-gen (number-to-element l pos)))

(defun taxa-list-to-index-taxon (taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Creates a mapping of unique integers to members of taxa-list.~/
;  ~/
;  Arguments:
;     (1) taxa-list - a list of taxa names

;  "
  (declare (xargs :guard t))
  (build-fast-alist-from-alist
   (number-to-element taxa-list 0)
   'index-taxon))

(in-theory (disable taxa-list-to-index-taxon))

(defthm alistp-taxa-list-to-index-taxon
  (alistp-gen (taxa-list-to-index-taxon taxa-list))
  :hints (("Goal" :in-theory (enable taxa-list-to-index-taxon))))

(defun element-to-number (l pos)
  (declare (xargs :guard (acl2-numberp pos)))
  (if (atom l)
      nil
    (cons (cons (car l) pos)
          (element-to-number (cdr l) (1+ pos)))))

(defthm element-to-number-when-not-consp
  (implies (not (consp l))
           (equal (element-to-number l pos)
                  nil)))

(defthm element-to-number-of-consp
  (equal (element-to-number (cons first rest) pos)
         (cons (cons first pos)
               (element-to-number rest (1+ pos)))))

(dis+ind element-to-number)

(defthm alistp-element-to-number
  (alistp-gen (element-to-number l pos)))

(defun taxa-list-to-taxon-index (taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Creates a mapping from each member of taxa-list to a unique integer.~/
;  ~/
;  Arguments:
;     (1) taxa-list - a list of taxa names

;  "
  (declare (xargs :guard t))
  (build-fast-alist-from-alist
   (element-to-number taxa-list 0)
   'taxon-index))

(in-theory (disable taxa-list-to-taxon-index))

(defun good-taxon-index-halist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (or (integerp (caar x))
               (and (symbolp (caar x))
                    (not (equal (caar x) nil))))
           (integerp (cdar x))
           (good-taxon-index-halist (cdr x)))
    t))

(defthm good-taxon-index-halist-when-not-consp
  (implies (not (consp x))
           (equal (good-taxon-index-halist x)
                  t)))

(defthm good-taxon-index-halist-of-consp
  (equal (good-taxon-index-halist (cons first rest))
         (and (consp first)
              (or (integerp (car first))
                  (and (symbolp (car first))
                       (not (equal (car first) nil))))
              (integerp (cdr first))
              (good-taxon-index-halist rest))))

(dis+ind good-taxon-index-halist)

(defthm good-taxon-integer-listp-alistp-gen
  (implies (good-taxon-index-halist x)
           (alistp-gen x)))

(defun get-taxa-from-taxon-index (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the taxa names from a mapping of taxa names to integers.~/
;  ~/
;  Arguments:
;     (1) x - a mapping of taxa names to integers.

;  "
  (declare (xargs :guard (alistp-gen x)))
  (if (consp x)
      (cons (caar x)
            (get-taxa-from-taxon-index (cdr x)))
    nil))

(defthm get-taxa-from-taxon-index-when-not-consp
  (implies (not (consp x))
           (equal (get-taxa-from-taxon-index x)
                  nil)))

(defthm get-taxa-from-taxon-index-of-consp
  (equal (get-taxa-from-taxon-index (cons first rest))
         (cons (car first)
               (get-taxa-from-taxon-index rest))))

(dis+ind get-taxa-from-taxon-index)

(defthm assoc-hqual-rationalp-cdr
  (implies (and (good-taxon-index-halist order)
                (assoc-hqual x order))
           (rationalp (cdr (assoc-hqual x order)))))

(defthm not-consp-assoc-not-assoc-hqual
  (implies (and (good-taxon-index-halist order)
                (not (consp (assoc-hqual x order))))
           (not (assoc-hqual x order))))

(defun int-symlist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (integerp (car x))
               (and (symbolp (car x))
                    (not (equal (car x) nil))))
           (int-symlist (cdr x)))
    t))

(defthm int-symlist-when-not-consp
  (implies (not (consp x))
           (equal (int-symlist x)
                  t)))

(defthm int-symlist-of-consp
  (equal (int-symlist (cons first rest))
         (and (or (integerp first)
                  (and (symbolp first)
                       (not (equal first nil))))
              (int-symlist rest))))

(dis+ind int-symlist)

(defun new-ind (list p acc)
  (declare (xargs :guard (rationalp p)))
  (if (consp list)
      (list (car list) p
            (new-ind (cdr list) (1+ p)
                     (cons (cons (car list)
                                 p)
                           acc)))
    (list list p acc)))

(defthm good-taxon-index-halist-of-build-fast-element-to-number
  (implies (and (int-symlist taxa-list)
                (integerp p)
                (good-taxon-index-halist acc))
           (good-taxon-index-halist
            (build-fast-alist-from-alist
             (element-to-number taxa-list p)
             acc))))

(defthm good-taxon-list-taxon-index
  (implies (int-symlist taxa-list)
           (good-taxon-index-halist (taxa-list-to-taxon-index
                                     taxa-list)))
  :hints (("Goal" :in-theory (enable taxa-list-to-taxon-index))))

(defun good-index-taxon-halist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (or (integerp (cdar x))
               (and (symbolp (cdar x))
                    (not (equal (cdar x) nil))))
           (integerp (caar x))
           (good-index-taxon-halist (cdr x)))
    t))

(defthm good-index-taxon-halist-when-not-consp
  (implies (not (consp x))
           (equal (good-index-taxon-halist x)
                  t)))

(defthm good-index-taxon-halist-of-consp
  (equal (good-index-taxon-halist (cons first rest))
         (and (consp first)
              (or (integerp (cdr first))
                  (and (symbolp (cdr first))
                       (not (equal (cdr first) nil))))
              (integerp (car first))
              (good-index-taxon-halist rest))))

(dis+ind good-index-taxon-halist)

;; An alist where every bound value is a natural number;
;; in our case resulting from a frequency count.
(defun integer-halistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (symbolp x)
    (and (consp (car x))
         (integerp (cdar x))
         (integer-halistp (cdr x)))))

(defthm atom-cdr-assoc-good-taxon-list
  (implies (good-index-taxon-halist y)
           (not (consp (cdr (hons-assoc-equal pos y))))))

(defun new-ind2 (list p acc)
  (declare (xargs :guard (rationalp p)))
  (if (consp list)
      (list (car list) p
            (new-ind2 (cdr list) (1+ p)
                     (cons (cons p (car list))
                           acc)))
    (list list p acc)))

(defthm good-index-taxon-halist-of-build-fast-number-to-element
  (implies (and (int-symlist taxa-list)
                (integerp p)
                (good-index-taxon-halist acc))
           (good-index-taxon-halist
            (build-fast-alist-from-alist
             (number-to-element taxa-list p)
             acc))))

(defthm good-index-taxon-halist-of-taxa-list-to-index-taxon
  (implies (int-symlist taxa-list)
           (good-index-taxon-halist
            (taxa-list-to-index-taxon taxa-list)))
  :hints (("Goal" :in-theory (enable taxa-list-to-index-taxon))))

(defun get-taxa-from-index-taxon (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the list of taxa names from a mapping of integers to taxa names.~/
;  ~/
;  Arguments:
;     (1) x - a mapping of integers to taxa names.

;  "
  (declare (xargs :guard (alistp-gen x)))
  (if (consp x)
      (cons (cdar x)
            (get-taxa-from-index-taxon (cdr x)))
    nil))

(defthm get-taxa-from-index-taxon-when-not-consp
  (implies (not (consp x))
           (equal (get-taxa-from-index-taxon x)
                  nil)))

(defthm get-taxa-from-index-taxon-of-consp
  (equal (get-taxa-from-index-taxon (cons first rest))
         (cons (cdr first)
               (get-taxa-from-index-taxon rest))))

(dis+ind get-taxa-from-index-taxon)

(defthm integer-halistp-halistp
  (implies (integer-halistp x)
           (alistp-gen x)))

(defthm integer-assoc-hqual-integer-halistp
  (implies (and (integer-halistp al)
                (assoc-hqual x al))
           (integerp (cdr (assoc-hqual x al))))
  :rule-classes :type-prescription)

(defthm hshrink-alist-halistp
  (implies (alistp-gen ans)
           (alistp-gen (hshrink-alist alst ans))))

(defthm hhshrink-alist-halistp
  (implies (alistp-gen ans)
           (alistp-gen (hhshrink-alist alst ans))))

(defthm alistp-through-shrink
  (implies (and (alistp-gen x)
                (alistp-gen acc))
           (alistp-gen (hons-shrink-alist x acc))))

; don't know why this one was around yet.
;(defthm equal-len
;  (implies (integerp p)
;           (equal (len (build-fast-alist-from-alist-acc
;                        (number-to-element taxa-list p)
;                        acc))
;                  (+ (len taxa-list) (len acc))))
;  :hints (("Goal" :induct (new-ind2 taxa-list p acc))))

;; Checks whether db is an alist such that db(x) is an integer if x is a
;; member of l.
(defun bound-to-nat-list (l db)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (and (implies (assoc-hqual (car l) db)
                  (natp (cdr (assoc-hqual (car l) db))))
         (bound-to-nat-list (cdr l) db))))

(defthm bound-to-nat-list-when-not-consp
  (implies (not (consp l))
           (equal (bound-to-nat-list l db)
                  t)))

(defthm bound-to-nat-list-of-consp
  (equal (bound-to-nat-list (cons first rest) db)
         (and (implies (assoc-hqual first db)
                       (and (integerp (cdr (assoc-hqual first db)))
                            (<= 0 (cdr (assoc-hqual first db)))))
              (bound-to-nat-list rest db))))

(dis+ind bound-to-nat-list)

(defthm bound-to-nat-het-number
  (implies (and (consp l)
                (assoc-hqual (car l) db)
                (bound-to-nat-list l db))
           (and (integerp (cdr (assoc-hqual (car l) db)))
                (<= 0 (cdr (assoc-hqual (car l) db)))
                (acl2-numberp (cdr (assoc-hqual (car l) db)))))
  :rule-classes (:rewrite :type-prescription))

(defthm bound-to-nat-list-acons-nat
  (implies (and (bound-to-nat-list a db)
                (integerp y)
                (<= 0 y))
           (bound-to-nat-list a (cons (cons x y) db))))

(defthm bound-to-nat-atom-db
  (implies (not (consp x))
           (bound-to-nat-list l x)))

(defmacro make-tia (tl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  Builds a mapping from taxa names to integers.~/
;  ~/
;  Arguments:
;     (1) x - a list of taxa names

;  Details: Same as taxa-list-to-taxon-index, but shorter name.
;  "
  `(build-fast-alist-from-alist
    (element-to-number ,tl 0) 'taxon-index))
