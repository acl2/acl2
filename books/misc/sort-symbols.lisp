; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (original date July, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Proof of correctness of reasonably efficient symbol sorting function,
; sort-symbol<.  This function is included in :program mode in the ACL2 source
; code, and is used by defpkg.

(in-package "ACL2")

; Added October, 2012: Parts of this file have been incorporated into the ACL2
; sources, so that now strict-merge-symbol<, strict-merge-sort-symbol<,
; strict-symbol<-sortedp, and sort-symbol-listp are guard-verified when ACL2
; starts up.  So I'm commenting them out here with #+skip readtime
; conditionals.

#+skip
(defun strict-merge-symbol< (l1 l2 acc)
  (declare (xargs :guard (and (symbol-listp l1)
                              (symbol-listp l2)
                              (true-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((eq (car l1) (car l2))
         (strict-merge-symbol< (cdr l1) (cdr l2) (cons (car l1) acc)))
        ((symbol< (car l1) (car l2))
         (strict-merge-symbol< (cdr l1) l2 (cons (car l1) acc)))
        (t (strict-merge-symbol< l1 (cdr l2) (cons (car l2) acc)))))

(local
 (defthm len-strict-merge-symbol<
   (<= (len (strict-merge-symbol< l1 l2 acc))
       (+ (len l1) (len l2) (len acc)))
   :rule-classes :linear))

(local
 (defthm len-evens
   (equal (len l)
          (+ (len (evens l))
             (len (odds l))))
   :rule-classes :linear))

(local
 (defthm symbol-listp-evens
   (implies (symbol-listp x)
            (symbol-listp (evens x)))
   :hints (("Goal" :induct (evens x)))))

(local
 (defthm symbol-listp-odds
   (implies (symbol-listp x)
            (symbol-listp (odds x)))))

(local
 (defthm symbol-listp-strict-merge-symbol<
   (implies (and (symbol-listp l1)
                 (symbol-listp l2)
                 (symbol-listp acc))
            (symbol-listp (strict-merge-symbol< l1 l2 acc)))))

#+skip
(defun strict-merge-sort-symbol< (l)
  (declare (xargs :guard (symbol-listp l)
                  :measure (len l)
                  :verify-guards nil))
  (cond ((endp (cdr l)) l)
        (t (strict-merge-symbol<
            (strict-merge-sort-symbol< (evens l))
            (strict-merge-sort-symbol< (odds l))
            nil))))

(local
 (defthm symbol-listp-strict-merge-sort-symbol<
   (implies (symbol-listp x)
            (symbol-listp (strict-merge-sort-symbol< x)))))

#+skip
(verify-guards strict-merge-sort-symbol<)

#+skip
(defun strict-symbol<-sortedp (x)
  (declare (xargs :guard (symbol-listp x)))
  (cond ((or (endp x) (null (cdr x)))
         t)
        (t (and (symbol< (car x) (cadr x))
                (strict-symbol<-sortedp (cdr x))))))

#+skip
(defun sort-symbol-listp (x)
  (declare (xargs :guard (symbol-listp x)))
  (cond ((strict-symbol<-sortedp x)
         x)
        (t (strict-merge-sort-symbol< x))))

(local
 (defthm member-eq-revappend-lemma
   (implies (member-eq a y)
            (member-eq a (revappend x y)))))

(local
 (defthm member-eq-revappend
   (iff (member-eq a (revappend x y))
        (or (member-eq a x)
            (member-eq a y)))))

(local
 (defthm member-eq-strict-merge-symbol<
   (iff (member-eq a (strict-merge-symbol< x y z))
        (or (member-eq a x)
            (member-eq a y)
            (member-eq a z)))))

(local
 (defthm member-eq-evens
   (implies (syntaxp (symbolp x))
            (iff (member-eq a x)
                 (or (member-eq a (evens x))
                     (member-eq a (evens (cdr x))))))))

(defthm member-eq-strict-merge-sort-symbol<
  (iff (member-eq a (strict-merge-sort-symbol< x))
       (member-eq a x)))

(defthm member-eq-sort-symbol-listp
  (iff (member-eq a (sort-symbol-listp x))
       (member-eq a x)))

; Start proof of sorted property.

(local
 (defun strict-symbol->-sortedp (x)
   (declare (xargs :guard (symbol-listp x)))
   (cond ((or (endp x) (null (cdr x)))
          t)
         (t (and (symbol< (cadr x) (car x))
                 (strict-symbol->-sortedp (cdr x)))))))

(local
 (defun sorted-lists-symbol-> (x y)

; Here x is sorted by symbol< and y is sorted by symbol->.  We return true if
; every element of x is symbol-> every element of y.

   (or (atom x)
       (atom y)
       (symbol< (car y) (car x)))))

(local
 (defthm strict-symbol<-revappend
   (implies (and (symbol-listp x)
                 (strict-symbol->-sortedp x)
                 (symbol-listp y)
                 (strict-symbol<-sortedp y)
                 (sorted-lists-symbol-> y x))
            (strict-symbol<-sortedp (revappend x y)))))

(local
 (defthm strict-symbol<-sortedp-strict-merge-symbol<
   (implies (and (symbol-listp x)
                 (symbol-listp y)
                 (symbol-listp acc)
                 (strict-symbol<-sortedp x)
                 (strict-symbol<-sortedp y)
                 (strict-symbol->-sortedp acc)
                 (sorted-lists-symbol-> x acc)
                 (sorted-lists-symbol-> y acc))
            (strict-symbol<-sortedp
             (strict-merge-symbol< x y acc)))))

(defthm strict-symbol<-sortedp-strict-merge-sort-symbol<
  (implies (symbol-listp x)
           (strict-symbol<-sortedp
            (strict-merge-sort-symbol< x))))

(defthm strict-symbol<-sortedp-sort-symbol-listp
  (implies (symbol-listp x)
           (strict-symbol<-sortedp
            (sort-symbol-listp x))))
