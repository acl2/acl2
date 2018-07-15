; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; This little book, and in particular strict-merge-sort-<, was developed in
; support of termination-database.lisp.  I considered using defsort, but it
; seemed simpler to develop this from scratch and, perhaps more important, I
; was put off by the following from :doc defsort:

;   NOTE: Defsort's interface has a greater than average likelihood of
;   changing incompatibly in the future.

(include-book "xdoc/top" :dir :system)

(defun strict-merge-< (l1 l2 acc)
; Adapted from ACL2 definition of merge-lexorder
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2)
                              (rational-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((= (car l1) (car l2))
         (strict-merge-< (cdr l1) (cdr l2) (cons (car l1) acc)))
        ((< (car l1) (car l2))
         (strict-merge-< (cdr l1) l2 (cons (car l1) acc)))
        (t
         (strict-merge-< l1 (cdr l2) (cons (car l2) acc)))))

(local
 (defthm <=-len-evens
   (<= (len (evens l))
       (len l))
   :rule-classes :linear
   :hints (("Goal" :induct (evens l)))))

(local
 (defthm <-len-evens
   (implies (consp (cdr l))
            (< (len (evens l))
               (len l)))
   :rule-classes :linear))

(defthm rational-listp-strict-merge-<
  (implies (and (rational-listp l1)
                (rational-listp l2)
                (rational-listp acc))
           (rational-listp (strict-merge-< l1 l2 acc))))

(defun strict-merge-sort-< (l)
  (declare (xargs :guard (rational-listp l)
                  :verify-guards nil
                  :measure (len l)))
  (cond ((endp (cdr l)) l)
        (t (strict-merge-< (strict-merge-sort-< (evens l))
                           (strict-merge-sort-< (odds l))
                           nil))))

(defthm rational-listp-evens
  (implies (rational-listp x)
           (rational-listp (evens x)))
  :hints (("Goal" :induct (evens x))))

(defthm rational-listp-strict-merge-sort-<
  (implies (rational-listp x)
           (rational-listp (strict-merge-sort-< x))))

(verify-guards strict-merge-sort-<)

(defxdoc strict-merge-sort-<
  :parents (kestrel-utilities)
  :short "Sort a list of rational numbers into @('<')-increasing order"
  :long "
 @({
 General Form:

 (strict-merge-sort-< lst)
 })

 <p>where the @(see guard) specifies @('(rational-listp lst)').  The result is
 a list in strictly increasing order (with respect to the @('<') relation) that
 contains the same elements as @('lst').</p>")
