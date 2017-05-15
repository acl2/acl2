; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann, May 2017
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Challenge problem
; Matt Kaufmann, May 2017

; The challenge is to prove sort-by-car<-preserves-assoc below.  That theorem
; states that for an alist with rational keys, with no duplicate keys, assoc is
; preserved by sorting the alist by key.  More specifically, the challenge is
; to create and certify a book sort-by-car-support.lisp that allows the present
; book, sort-by-car.lisp, to certify.  To start, copy sort-by-car.lisp to
; sort-by-car-support.lisp and remove the form below, (local (include-book
; "sort-by-car-support")), from sort-by-car-support.lisp.

; NOTE: The solution in sort-by-car-support.lisp could probably be improved.
; It can be challenging (at least, for me) to carry out an ACL2 proof in a
; manner that exhibits the thought process when complete.  It probably would
; have been better for me to include more encapsulate events, with some of the
; lemmas in that book occurring only locally in such encapsulates.  I'll leave
; that as a challenge for someone else to clean up, if desired.

; Portcullis command:
#||
(defpkg "SORT-BY-CAR"
  (union$
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   :test 'eq))
||#

(in-package "SORT-BY-CAR")

(local (include-book "sort-by-car-support"))

(set-enforce-redundancy t)

(include-book "defsort/defsort" :dir :system)

(encapsulate
  ( ((valp *) => *) )
  (local (defun valp (x) (consp x)))
  (defthm booleanp-valp
    (booleanp (valp x))
    :rule-classes :type-prescription))

(encapsulate
  ( ((indexp *) => *) )
  (local (defun indexp (x) (rationalp x)))
  (defthm indexp-implies-rationalp
    (implies (indexp x)
             (rationalp x))
    :rule-classes :compound-recognizer))

(defun indexed-pair-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (indexp (car x))
       (valp (cdr x))))

(defun car< (x y)
  (declare (xargs :guard (and (indexed-pair-p x)
                              (indexed-pair-p y))))
  (< (car x) (car y)))

(acl2::defsort sort-by-car<
  :compare< car<
  :comparablep indexed-pair-p
  :true-listp t
  :weak t)

(defthm sort-by-car<-preserves-assoc
  (implies (and (alistp alist)
                (no-duplicatesp (strip-cars alist)))
           (equal (assoc index (sort-by-car< alist))
                  (assoc index alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Example application to specific defsort:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-enforce-redundancy nil)

(local
 (progn

   (defun my-valp (x)
     (declare (xargs :guard t))
     (symbol-listp x))

   (defun my-indexed-pair-p (x)
     (declare (xargs :guard t))
     (and (consp x)
          (posp (car x))
          (my-valp (cdr x))))

   (defun my-car< (x y)
     (declare (xargs :guard (and (my-indexed-pair-p x)
                                 (my-indexed-pair-p y))))
     (< (car x) (car y)))

   (acl2::defsort sort-by-my-car<
                  :compare< my-car<
                  :comparablep my-indexed-pair-p
                  :true-listp t
                  :weak t)

   (defthm sort-by-my-car<-preserves-assoc
     (implies (and (alistp alist)
                   (no-duplicatesp (strip-cars alist)))
              (equal (assoc index (sort-by-my-car< alist))
                     (assoc index alist)))
     :otf-flg t
     :hints (("Goal"
              :in-theory (enable sort-by-car<-merge-tr
                                 sort-by-car<-merge
                                 sort-by-my-car<-merge
                                 sort-by-my-car<)
              :do-not-induct t
              :by (:functional-instance
                   sort-by-car<-preserves-assoc
                   (valp my-valp)
                   (indexp posp)
                   (indexed-pair-p my-indexed-pair-p)
                   (car< my-car<)
                   (sort-by-car< sort-by-my-car<)
                   (sort-by-car<-merge sort-by-my-car<-merge)
                   (sort-by-car<-list-p sort-by-my-car<-list-p)
                   (sort-by-car<-ordered-p sort-by-my-car<-ordered-p)))))))

