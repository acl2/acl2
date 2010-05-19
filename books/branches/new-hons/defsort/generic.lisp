; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(local (include-book "generic-impl"))
(set-enforce-redundancy t)

(defund duplicity (a x)
  (declare (xargs :guard t))
  (cond ((atom x)
         0)
        ((equal (car x) a)
         (+ 1 (duplicity a (cdr x))))
        (t
         (duplicity a (cdr x)))))

(defthm duplicity-when-not-consp
  (implies (not (consp x))
           (equal (duplicity a x)
                  0)))

(defthm duplicity-of-cons
  (equal (duplicity a (cons b x))
         (if (equal a b)
             (+ 1 (duplicity a x))
           (duplicity a x))))



(encapsulate
 (((comparablep *) => *)
  ((compare< * *) => *))

 (local (defun comparablep (x)
          (declare (xargs :guard t))
          (natp x)))

 (local (defun compare< (x y)
          (declare (xargs :guard (and (comparablep x)
                                      (comparablep y))))
          (< x y)))

 (defthm type-of-comparablep
   (or (equal (comparablep x) t)
       (equal (comparablep x) nil))
   :rule-classes :type-prescription)

 (defthm type-of-compare<
   (or (equal (compare< x y) t)
       (equal (compare< x y) nil))
   :rule-classes :type-prescription)

 (defthm compare<-transitive
   (implies (and (comparablep x)
                 (comparablep y)
                 (comparablep z)
                 (compare< x y)
                 (compare< y z))
            (compare< x z))))



(defund comparable-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (comparablep (car x))
           (comparable-listp (cdr x)))
    t))


(defund comparable-orderedp (x)
  (declare (xargs :guard (comparable-listp x)))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         t)
        ((compare< (first x) (second x))
         (comparable-orderedp (cdr x)))
        (t
         (and (not (compare< (cadr x) (car x)))
              (comparable-orderedp (cdr x))))))


(defund comparable-merge (x y)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))))
  (cond ((atom x)
         y)
        ((atom y)
         x)
        ((compare< (car y) (car x))
         (cons (car y) (comparable-merge x (cdr y))))
        (t
         (cons (car x) (comparable-merge (cdr x) y)))))

(defthm comparable-listp-of-comparable-merge
  (implies (and (force (comparable-listp x))
                (force (comparable-listp y)))
           (equal (comparable-listp (comparable-merge x y))
                  t))
  :hints(("Goal" :in-theory (enable comparable-merge))))


(defconst *mergesort-fixnum-threshold* 536870912)

(defund fast-comparable-mergesort-fixnums (x len)
   (declare (xargs :guard (and (true-listp x)
                               (comparable-listp x)
                               (natp len)
                               (<= len (len x)))
                   :measure (nfix len))
            (type (signed-byte 30) len))
   (cond ((mbe :logic (zp len)
               :exec (= (the (signed-byte 30) len) 0))
          nil)
         ((= (the (signed-byte 30) len) 1)
          (list (car x)))
         (t
          (let* ((len1  (the (signed-byte 30)
                          (ash (the (signed-byte 30) len) -1)))
                 (len2  (the (signed-byte 30)
                          (+ (the (signed-byte 30) len1)
                             (the (signed-byte 30)
                               (logand (the (signed-byte 30) len) 1)))))
                 (part1 (fast-comparable-mergesort-fixnums x len1))
                 (part2 (fast-comparable-mergesort-fixnums (nthcdr len1 x) len2)))
            (comparable-merge part1 part2)))))

(defund fast-comparable-mergesort-integers (x len)
  (declare (xargs :guard (and (true-listp x)
                              (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len))
           (type integer len))
  (cond ((mbe :logic (zp len)
              :exec (= (the integer len) 0))
         nil)
        ((= (the integer len) 1)
         (list (car x)))
        (t
         (let* ((len1  (the integer (ash (the integer len) -1)))
                (len2  (the integer
                         (+ (the integer len1)
                            (the integer (logand (the integer len) 1)))))
                (part1 (if (< (the integer len1) *mergesort-fixnum-threshold*)
                           (fast-comparable-mergesort-fixnums x len1)
                         (fast-comparable-mergesort-integers x len1)))
                (part2 (if (< (the integer len2) *mergesort-fixnum-threshold*)
                           (fast-comparable-mergesort-fixnums (nthcdr len1 x) len2)
                         (fast-comparable-mergesort-integers (nthcdr len1 x) len2))))
           (comparable-merge part1 part2)))))

(defund comparable-mergesort (x)
  (declare (xargs :guard (and (true-listp x)
                              (comparable-listp x))))
  (let ((len (mbe :logic (len x)
                  :exec (length x))))
    (if (< (the integer len) *mergesort-fixnum-threshold*)
        (fast-comparable-mergesort-fixnums x len)
      (fast-comparable-mergesort-integers x len))))

(defthm true-listp-of-comparable-mergesort
  (true-listp (comparable-mergesort x))
  :rule-classes :type-prescription)

(defthm comparable-listp-of-comparable-mergesort
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort x)))
  :hints(("Goal" :in-theory (enable comparable-mergesort))))

(defthm duplicity-of-comparable-mergesort
  (equal (duplicity a (comparable-mergesort x))
         (duplicity a x)))

(defthm comparable-orderedp-of-comparable-mergesort
  (comparable-orderedp (comparable-mergesort x)))

(defthm no-duplicatesp-equal-of-comparable-mergesort
  (equal (no-duplicatesp-equal (comparable-mergesort x))
         (no-duplicatesp-equal x)))







(defthm comparable-orderedp-guard
  (and (implies (and (comparable-listp x)
                     (not (atom x))
                     (not (atom (cdr x))))
                (comparablep (car x)))
       (implies (and (comparable-listp x)
                     (not (atom x))
                     (not (atom (cdr x))))
                (comparablep (cadr x)))
       (implies (and (comparable-listp x)
                     (not (atom x))
                     (not (atom (cdr x)))
                     (compare< (car x) (cadr x)))
                (comparable-listp (cdr x)))
       (implies (and (comparable-listp x)
                     (not (atom x))
                     (not (atom (cdr x)))
                     (not (compare< (cadr x) (car x))))
                (comparable-listp (cdr x))))
  :rule-classes nil)

(defthm comparable-merge-admission
  (and (o-p (+ (acl2-count x) (acl2-count y)))
       (implies (and (not (atom x))
                     (not (atom y))
                     (not (compare< (car y) (car x))))
                (o< (+ (acl2-count (cdr x)) (acl2-count y))
                    (+ (acl2-count x) (acl2-count y))))
       (implies (and (not (atom x))
                     (not (atom y))
                     (compare< (car y) (car x)))
                (o< (+ (acl2-count x) (acl2-count (cdr y)))
                    (+ (acl2-count x) (acl2-count y)))))
  :rule-classes nil)

(defthm comparable-merge-guards
  (and (implies (and (comparable-listp y)
                     (comparable-listp x)
                     (not (atom x))
                     (not (atom y)))
                (comparablep (car y)))
       (implies (and (comparable-listp y)
                     (comparable-listp x)
                     (not (atom x))
                     (not (atom y)))
                (comparablep (car x)))
       (implies (and (comparable-listp y)
                     (comparable-listp x)
                     (not (atom x))
                     (not (atom y))
                     (compare< (car y) (car x)))
                (comparable-listp (cdr y)))
       (implies (and (comparable-listp y)
                     (comparable-listp x)
                     (not (atom x))
                     (not (atom y))
                     (not (compare< (car y) (car x))))
                (comparable-listp (cdr x))))
  :rule-classes nil)

(defthm fast-comparable-mergesort-fixnums-guards
  (AND
    (IMPLIES (AND (TRUE-LISTP X)
                  (COMPARABLE-LISTP X)
                  (NATP LEN))
             (RATIONALP (LEN X)))
    (IMPLIES (AND (TRUE-LISTP X)
                  (COMPARABLE-LISTP X)
                  (NATP LEN))
             (RATIONALP LEN))
    (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                  (<= LEN (LEN X))
                  (NATP LEN)
                  (COMPARABLE-LISTP X)
                  (TRUE-LISTP X))
             (EQUAL (ZP LEN) (= LEN 0)))
    (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                  (<= LEN (LEN X))
                  (NATP LEN)
                  (COMPARABLE-LISTP X)
                  (TRUE-LISTP X))
             (LET ((VAR LEN))
                  (SIGNED-BYTE-P 30 VAR)))
    (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                  (<= LEN (LEN X))
                  (NATP LEN)
                  (COMPARABLE-LISTP X)
                  (TRUE-LISTP X))
             (ACL2-NUMBERP LEN))
    (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                  (<= LEN (LEN X))
                  (NATP LEN)
                  (COMPARABLE-LISTP X)
                  (TRUE-LISTP X)
                  (NOT (ZP LEN))
                  (NOT (= LEN 1)))
             (INTEGERP LEN))
    (IMPLIES
     (AND (SIGNED-BYTE-P 30 LEN)
          (<= LEN (LEN X))
          (NATP LEN)
          (COMPARABLE-LISTP X)
          (TRUE-LISTP X)
          (NOT (ZP LEN))
          (NOT (= LEN 1)))
     (LET
      ((LEN1 (ASH LEN -1)))
      (AND
       (LET ((VAR LEN1))
            (SIGNED-BYTE-P 30 VAR))
       (LET ((VAR LEN)) (SIGNED-BYTE-P 30 VAR))
       (INTEGERP LEN)
       (LET ((VAR (LOGAND LEN 1)))
            (SIGNED-BYTE-P 30 VAR))
       (ACL2-NUMBERP LEN1)
       (ACL2-NUMBERP (LOGAND LEN 1))
       (LET ((VAR (+ LEN1 (LOGAND LEN 1))))
            (SIGNED-BYTE-P 30 VAR))
       (LET
        ((LEN2 (+ LEN1 (LOGAND LEN 1))))
        (AND
         (TRUE-LISTP X)
         (SIGNED-BYTE-P 30 LEN1)
         (NATP LEN1)
         (COMPARABLE-LISTP X)
         (<= LEN1 (LEN X))
         (LET
          ((PART1 (FAST-COMPARABLE-MERGESORT-FIXNUMS X LEN1)))
          (AND (INTEGERP LEN1)
               (TRUE-LISTP X)
               (<= 0 LEN1)
               (TRUE-LISTP (NTHCDR LEN1 X))
               (SIGNED-BYTE-P 30 LEN2)
               (NATP LEN2)
               (COMPARABLE-LISTP (NTHCDR LEN1 X))
               (<= LEN2 (LEN (NTHCDR LEN1 X)))
               (LET ((PART2 (FAST-COMPARABLE-MERGESORT-FIXNUMS (NTHCDR LEN1 X)
                                                               LEN2)))
                    (AND (COMPARABLE-LISTP PART1)
                         (COMPARABLE-LISTP PART2))))))))))
    (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                  (<= LEN (LEN X))
                  (NATP LEN)
                  (COMPARABLE-LISTP X)
                  (TRUE-LISTP X)
                  (NOT (ZP LEN))
                  (NOT (= LEN 1)))
             (LET ((VAR (ASH LEN -1)))
                  (SIGNED-BYTE-P 30 VAR))))
  :rule-classes nil)

(defthm fast-comparable-mergesort-integers-guards
  (AND
     (IMPLIES (AND (TRUE-LISTP X)
                   (COMPARABLE-LISTP X)
                   (NATP LEN))
              (RATIONALP (LEN X)))
     (IMPLIES (AND (TRUE-LISTP X)
                   (COMPARABLE-LISTP X)
                   (NATP LEN))
              (RATIONALP LEN))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (TRUE-LISTP X))
              (EQUAL (ZP LEN) (= LEN 0)))
     (IMPLIES
      (AND (INTEGERP LEN)
           (<= LEN (LEN X))
           (NATP LEN)
           (COMPARABLE-LISTP X)
           (TRUE-LISTP X)
           (NOT (ZP LEN))
           (NOT (= LEN 1)))
      (LET
       ((LEN1 (ASH LEN -1)))
       (AND
        (LET ((VAR LEN1)) (INTEGERP VAR))
        (LET ((VAR LEN)) (INTEGERP VAR))
        (INTEGERP LEN)
        (LET ((VAR (LOGAND LEN 1)))
             (INTEGERP VAR))
        (ACL2-NUMBERP LEN1)
        (ACL2-NUMBERP (LOGAND LEN 1))
        (LET ((VAR (+ LEN1 (LOGAND LEN 1))))
             (INTEGERP VAR))
        (LET
         ((LEN2 (+ LEN1 (LOGAND LEN 1))))
         (AND
          (LET ((VAR LEN1)) (INTEGERP VAR))
          (RATIONALP LEN1)
          (OR (<= 536870912 LEN1) (TRUE-LISTP X))
          (OR (<= 536870912 LEN1)
              (SIGNED-BYTE-P 30 LEN1))
          (OR (<= 536870912 LEN1) (NATP LEN1))
          (OR (<= 536870912 LEN1)
              (COMPARABLE-LISTP X))
          (OR (<= 536870912 LEN1)
              (<= LEN1 (LEN X)))
          (OR (< LEN1 536870912) (TRUE-LISTP X))
          (OR (< LEN1 536870912) (INTEGERP LEN1))
          (OR (< LEN1 536870912) (NATP LEN1))
          (OR (< LEN1 536870912)
              (COMPARABLE-LISTP X))
          (OR (< LEN1 536870912)
              (<= LEN1 (LEN X)))
          (LET
           ((PART1 (IF (< LEN1 536870912)
                       (FAST-COMPARABLE-MERGESORT-FIXNUMS X LEN1)
                       (FAST-COMPARABLE-MERGESORT-INTEGERS X LEN1))))
           (AND
            (LET ((VAR LEN2)) (INTEGERP VAR))
            (RATIONALP LEN2)
            (OR (<= 536870912 LEN2) (INTEGERP LEN1))
            (OR (<= 536870912 LEN2) (TRUE-LISTP X))
            (OR (<= 536870912 LEN2) (<= 0 LEN1))
            (OR (<= 536870912 LEN2)
                (TRUE-LISTP (NTHCDR LEN1 X)))
            (OR (<= 536870912 LEN2)
                (SIGNED-BYTE-P 30 LEN2))
            (OR (<= 536870912 LEN2) (NATP LEN2))
            (OR (<= 536870912 LEN2)
                (COMPARABLE-LISTP (NTHCDR LEN1 X)))
            (OR (<= 536870912 LEN2)
                (<= LEN2 (LEN (NTHCDR LEN1 X))))
            (OR (< LEN2 536870912) (INTEGERP LEN1))
            (OR (< LEN2 536870912) (TRUE-LISTP X))
            (OR (< LEN2 536870912) (<= 0 LEN1))
            (OR (< LEN2 536870912)
                (TRUE-LISTP (NTHCDR LEN1 X)))
            (OR (< LEN2 536870912) (INTEGERP LEN2))
            (OR (< LEN2 536870912) (NATP LEN2))
            (OR (< LEN2 536870912)
                (COMPARABLE-LISTP (NTHCDR LEN1 X)))
            (OR (< LEN2 536870912)
                (<= LEN2 (LEN (NTHCDR LEN1 X))))
            (LET ((PART2 (IF (< LEN2 536870912)
                             (FAST-COMPARABLE-MERGESORT-FIXNUMS (NTHCDR LEN1 X)
                                                                LEN2)
                             (FAST-COMPARABLE-MERGESORT-INTEGERS (NTHCDR LEN1 X)
                                                                 LEN2))))
                 (AND (COMPARABLE-LISTP PART1)
                      (COMPARABLE-LISTP PART2))))))))))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (TRUE-LISTP X)
                   (NOT (ZP LEN))
                   (NOT (= LEN 1)))
              (LET ((VAR (ASH LEN -1)))
                   (INTEGERP VAR))))
  :rule-classes nil)









(defthm fast-comparable-mergesort-integers-admission
  (and (o-p (nfix len))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o<
         (nfix
          (let
           ((var
             (+ (let ((var (let ((var (ash (let ((var len))
                                                (if (integerp var)
                                                    var (the-error 'integer var)))
                                           -1)))
                                (if (integerp var)
                                    var (the-error 'integer var)))))
                     (if (integerp var)
                         var (the-error 'integer var)))
                (let ((var (logand (let ((var len))
                                        (if (integerp var)
                                            var (the-error 'integer var)))
                                   1)))
                     (if (integerp var)
                         var (the-error 'integer var))))))
           (if (integerp var)
               var (the-error 'integer var))))
         (nfix len)))
       (implies (and (not (zp len)) (not (= len 1)))
                (o< (nfix (let ((var (ash (let ((var len))
                                               (if (integerp var)
                                                   var (the-error 'integer var)))
                                          -1)))
                               (if (integerp var)
                                   var (the-error 'integer var))))
                    (nfix len))))
  :rule-classes nil)


(defthm fast-comparable-mergesort-fixnums-admission
  (and (o-p (nfix len))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o<
         (nfix
          (let
              ((var
                (+
                 (let
                     ((var
                       (let ((var (ash (let ((var len))
                                         (if (signed-byte-p 30 var)
                                             var (the-error '(signed-byte 30) var)))
                                       -1)))
                         (if (signed-byte-p 30 var)
                             var
                           (the-error '(signed-byte 30) var)))))
                   (if (signed-byte-p 30 var)
                       var (the-error '(signed-byte 30) var)))
                 (let ((var (logand (let ((var len))
                                      (if (signed-byte-p 30 var)
                                          var (the-error '(signed-byte 30) var)))
                                    1)))
                   (if (signed-byte-p 30 var)
                       var
                     (the-error '(signed-byte 30) var))))))
            (if (signed-byte-p 30 var)
                var (the-error '(signed-byte 30) var))))
         (nfix len)))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o< (nfix (let ((var (ash (let ((var len))
                                    (if (signed-byte-p 30 var)
                                        var (the-error '(signed-byte 30) var)))
                                  -1)))
                    (if (signed-byte-p 30 var)
                        var (the-error '(signed-byte 30) var))))
            (nfix len))))
  :rule-classes nil)