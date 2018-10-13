;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; September 2018

(in-package "ADE")

(include-book "std/lists/take" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; ======================================================================

;; BINARY-AND*

(defun binary-and* (x y)
  (declare (xargs :guard t))
  (if x y nil))

(defthm booleanp-binary-and*
  (implies (booleanp y)
           (booleanp (binary-and* x y)))
  :rule-classes :type-prescription)

(in-theory (disable binary-and*))

(defund and*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-and* ,(car x)
                       ,(and*-macro (cdr x))))))

(defmacro and* (&rest args)
  (and*-macro args))

;; BINARY-OR*

(defun binary-or* (x y)
  (declare (xargs :guard t))
  (if x x y))

(defthm booleanp-binary-or*
  (implies (and (booleanp x)
                (booleanp y))
           (booleanp (binary-or* x y)))
  :rule-classes :type-prescription)

(in-theory (disable binary-or*))

(defund or*-macro (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (car x))
        (t
         `(binary-or* ,(car x)
                      ,(or*-macro (cdr x))))))

(defmacro or* (&rest args)
  (or*-macro args))

;; NOT*

(defun not* (x)
  (declare (xargs :guard t))
  (not x))

(defthm booleanp-not*
  (booleanp (not* x))
  :rule-classes :type-prescription)

(in-theory (disable not*))

;; ======================================================================

;; Shuffle two lists

(defun insert (x i l)
  (declare (xargs :guard (natp i)))
  (cond
   ((atom l)
    (list x))
   ((zp i)
    (cons x l))
   (t (cons (car l)
            (insert x (1- i) (cdr l))))))

(defthm true-listp-insert
  (implies (true-listp l)
           (true-listp (insert x i l)))
  :rule-classes :type-prescription)

(in-theory (disable insert))

(defun insert-up-to-i (x i l)
  (declare (xargs :guard (natp i)))
  (if (zp i)
      (list (insert x i l))
    (cons (insert x i l)
          (insert-up-to-i x (1- i) l))))

(defthm true-list-listp-insert-up-to-i
  (implies (true-listp l)
           (true-list-listp (insert-up-to-i x i l)))
  :rule-classes :type-prescription)

(in-theory (disable insert-up-to-i))

(defund cons-or-append (x y)
  (declare (xargs :guard t))
  (if (atom x)
      (if (atom y)
          (cons x (list y))
        (cons x y))
    (if (atom y)
        (append (list-fix x) (list y))
      (append (list-fix x) y))))

(defun cons-or-append-at-i (x i l)
  (declare (xargs :guard (integerp i)))
  (cond
   ((atom l)
    (list x))
   ((= i 0)
    (cons (cons-or-append x (car l))
          (cdr l)))
   ((not (natp i)) nil)
   (t (cons (car l)
            (cons-or-append-at-i x (1- i) (cdr l))))))

(defthm true-listp-cons-or-append-at-i
  (implies (true-listp l)
           (true-listp (cons-or-append-at-i x i l)))
  :rule-classes :type-prescription)

(in-theory (disable cons-or-append-at-i))

(defun cons-or-append-up-to-i (x i l)
  (declare (xargs :measure (acl2-count (1+ i))
                  :guard (integerp i)))
  (if (not (natp i))
      nil
    (cons (cons-or-append-at-i x i l)
          (cons-or-append-up-to-i x (1- i) l))))

(defthm true-list-listp-cons-or-append-up-to-i
  (implies (true-listp l)
           (true-list-listp (cons-or-append-up-to-i x i l)))
  :rule-classes :type-prescription)

(in-theory (disable cons-or-append-up-to-i))

(defund index-of-nested (k x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((equal k (car x)) 0)
        ((atom (car x))
         (b* ((res (index-of-nested k (cdr x))))
           (and res (1+ res))))
        (t (b* ((res1 (index-of-nested k (car x))))
             (if res1
                 0
               (b* ((res (index-of-nested k (cdr x))))
                 (and res (1+ res))))))))

(defun insert-up-to-rec (x y l)
  (declare (xargs :guard (true-list-listp l)))
  (if (atom l)
      nil
    (b* ((i (index-of-nested y (car l)))
         (i (if (natp i) i (len (car l)))))
      (append (append (insert-up-to-i x i (car l))
                      (cons-or-append-up-to-i x (1- i) (car l)))
              (insert-up-to-rec x y (cdr l))))))

(defthm true-list-listp-of-append
  (implies (and (true-list-listp x)
                (true-list-listp y))
           (true-list-listp (append x y)))
  :rule-classes :type-prescription)

(defthm true-list-listp-insert-up-to-rec
  (implies (true-list-listp l)
           (true-list-listp (insert-up-to-rec x y l)))
  :rule-classes :type-prescription)

(in-theory (disable insert-up-to-rec))

(defun shuffle (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (if (atom l1)
      (list l2)
    (insert-up-to-rec (car l1) (cadr l1)
                      (shuffle (cdr l1) l2))))

(defthm true-list-listp-shuffle
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-list-listp (shuffle l1 l2)))
  :rule-classes :type-prescription)

(in-theory (disable shuffle))

(defun shuffle-rec1 (x y)
  (declare (xargs :guard (and (true-list-listp x)
                              (true-listp y))))
  (if (atom x)
      nil
    (append (shuffle (car x) y)
            (shuffle-rec1 (cdr x) y))))

(defun shuffle-rec2 (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-list-listp y))))
  (if (atom y)
      nil
    (append (shuffle x (car y))
            (shuffle-rec2 x (cdr y)))))

;; Compute a powerset

(defund combine (x y)
  (declare (xargs :guard t))
  (list y (cons x y)))

(defund combine-rec (x y)
  (declare (xargs :guard (true-listp y)))
  (if (atom y)
      (list (list x))
    (append (combine x (car y))
            (combine-rec x (cdr y)))))

(defund no-empty-powerset (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (combine-rec (car x)
                 (no-empty-powerset (cdr x)))))

(defund powerset (x)
  (declare (xargs :guard t))
  (cons nil (no-empty-powerset x)))


