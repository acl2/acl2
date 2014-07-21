; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/lists/duplicity" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "generic-impl"))
(set-enforce-redundancy t)


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


(defund comparable-merge-tr (x y acc)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))))
  (cond ((atom x)
         (revappend-without-guard acc y))
        ((atom y)
         (revappend-without-guard acc x))
        ((compare< (car y) (car x))
         (comparable-merge-tr x (cdr y) (cons (car y) acc)))
        (t
         (comparable-merge-tr (cdr x) y (cons (car x) acc)))))

(defthm comparable-merge-tr-removal
  (equal (comparable-merge-tr x y nil)
         (comparable-merge x y)))


(defmacro mergesort-fixnum-threshold () 536870912)

(defund fast-comparable-mergesort-fixnums (x len)
   (declare (xargs :guard (and (comparable-listp x)
                               (natp len)
                               (<= len (len x)))
                   :measure (nfix len))
            (type (signed-byte 30) len))
   (cond ((mbe :logic (zp len)
               :exec (eql (the (signed-byte 30) len) 0))
          nil)
         ((eql (the (signed-byte 30) len) 1)
          (list (car x)))
         (t
          (let* ((len1  (the (signed-byte 30)
                          (ash (the (signed-byte 30) len) -1)))
                 (len2  (the (signed-byte 30)
                          (+ (the (signed-byte 30) len1)
                             (the (signed-byte 30)
                               (logand (the (signed-byte 30) len) 1)))))
                 (part1 (fast-comparable-mergesort-fixnums x len1))
                 (part2 (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)))
            (comparable-merge-tr part1 part2 nil)))))

(defund fast-comparable-mergesort-integers (x len)
  (declare (xargs :guard (and (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len))
           (type integer len))
  (cond ((mbe :logic (zp len)
              :exec (eql (the integer len) 0))
         nil)
        ((eql (the integer len) 1)
         (list (car x)))
        (t
         (let* ((len1  (the integer (ash (the integer len) -1)))
                (len2  (the integer
                         (+ (the integer len1)
                            (the integer (logand (the integer len) 1)))))
                (part1 (if (< (the integer len1) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums x len1)
                         (fast-comparable-mergesort-integers x len1)))
                (part2 (if (< (the integer len2) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)
                         (fast-comparable-mergesort-integers (rest-n len1 x) len2))))
           (comparable-merge-tr part1 part2 nil)))))

(defund comparable-mergesort (x)
  (declare (xargs :guard (comparable-listp x)))
  (let ((len (len x)))
    (if (< len (mergesort-fixnum-threshold))
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

(defthm comparable-merge-tr-guards
  (AND (IMPLIES (AND (COMPARABLE-LISTP Y)
                     (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM Y))
                     (COMPARE< (CAR Y) (CAR X)))
                (COMPARABLE-LISTP (CDR Y)))
       (IMPLIES (AND (COMPARABLE-LISTP Y)
                     (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM Y))
                     (NOT (COMPARE< (CAR Y) (CAR X))))
                (COMPARABLE-LISTP (CDR X))))
  :rule-classes nil)

(defthm fast-comparable-mergesort-fixnums-guards
  (AND
   (IMPLIES (AND (COMPARABLE-LISTP X) (NATP LEN))
            (RATIONALP (LEN X)))
   (IMPLIES (AND (COMPARABLE-LISTP X) (NATP LEN))
            (RATIONALP LEN))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X))
            (EQUAL (ZP LEN) (EQL LEN 0)))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X))
            (LET ((VAR LEN))
                 (SIGNED-BYTE-P 30 VAR)))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X)
                 (NOT (EQLABLEP LEN)))
            (EQLABLEP 0))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X)
                 (NOT (ZP LEN))
                 (NOT (EQLABLEP LEN)))
            (EQLABLEP 1))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X)
                 (NOT (ZP LEN))
                 (NOT (EQL LEN 1)))
            (LET ((VAR (ASH LEN -1)))
                 (SIGNED-BYTE-P 30 VAR)))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X)
                 (NOT (ZP LEN))
                 (NOT (EQL LEN 1)))
            (INTEGERP LEN))
   (IMPLIES
    (AND (SIGNED-BYTE-P 30 LEN)
         (<= LEN (LEN X))
         (NATP LEN)
         (COMPARABLE-LISTP X)
         (NOT (ZP LEN))
         (NOT (EQL LEN 1)))
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
        (COMPARABLE-LISTP X)
        (<= LEN1 (LEN X))
        (NATP LEN1)
        (SIGNED-BYTE-P 30 LEN1)
        (LET
         ((PART1 (FAST-COMPARABLE-MERGESORT-FIXNUMS X LEN1)))
         (AND (NATP LEN1)
              (COMPARABLE-LISTP (REST-N LEN1 X))
              (<= LEN2 (LEN (REST-N LEN1 X)))
              (NATP LEN2)
              (SIGNED-BYTE-P 30 LEN2)
              (LET ((PART2 (FAST-COMPARABLE-MERGESORT-FIXNUMS (REST-N LEN1 X)
                                                              LEN2)))
                   (AND (COMPARABLE-LISTP PART1)
                        (COMPARABLE-LISTP PART2))))))))))
   (IMPLIES (AND (SIGNED-BYTE-P 30 LEN)
                 (<= LEN (LEN X))
                 (NATP LEN)
                 (COMPARABLE-LISTP X)
                 (NOT (ZP LEN))
                 (EQL LEN 1)
                 (NOT (CONSP X)))
            (EQUAL X NIL)))
  :rule-classes nil)

(defthm fast-comparable-mergesort-integers-guards
  (AND
     (IMPLIES (AND (COMPARABLE-LISTP X) (NATP LEN))
              (RATIONALP (LEN X)))
     (IMPLIES (AND (COMPARABLE-LISTP X) (NATP LEN))
              (RATIONALP LEN))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X))
              (EQUAL (ZP LEN) (EQL LEN 0)))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (NOT (EQLABLEP LEN)))
              (EQLABLEP 0))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (NOT (ZP LEN))
                   (NOT (EQLABLEP LEN)))
              (EQLABLEP 1))
     (IMPLIES
      (AND (INTEGERP LEN)
           (<= LEN (LEN X))
           (NATP LEN)
           (COMPARABLE-LISTP X)
           (NOT (ZP LEN))
           (NOT (EQL LEN 1)))
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
          (OR (<= 536870912 LEN1)
              (COMPARABLE-LISTP X))
          (OR (<= 536870912 LEN1)
              (<= LEN1 (LEN X)))
          (OR (<= 536870912 LEN1) (NATP LEN1))
          (OR (<= 536870912 LEN1)
              (SIGNED-BYTE-P 30 LEN1))
          (OR (< LEN1 536870912)
              (COMPARABLE-LISTP X))
          (OR (< LEN1 536870912)
              (<= LEN1 (LEN X)))
          (OR (< LEN1 536870912) (NATP LEN1))
          (OR (< LEN1 536870912) (INTEGERP LEN1))
          (LET
           ((PART1 (IF (< LEN1 536870912)
                       (FAST-COMPARABLE-MERGESORT-FIXNUMS X LEN1)
                       (FAST-COMPARABLE-MERGESORT-INTEGERS X LEN1))))
           (AND
            (LET ((VAR LEN2)) (INTEGERP VAR))
            (RATIONALP LEN2)
            (OR (<= 536870912 LEN2) (NATP LEN1))
            (OR (<= 536870912 LEN2)
                (COMPARABLE-LISTP (REST-N LEN1 X)))
            (OR (<= 536870912 LEN2)
                (<= LEN2 (LEN (REST-N LEN1 X))))
            (OR (<= 536870912 LEN2) (NATP LEN2))
            (OR (<= 536870912 LEN2)
                (SIGNED-BYTE-P 30 LEN2))
            (OR (< LEN2 536870912) (NATP LEN1))
            (OR (< LEN2 536870912)
                (COMPARABLE-LISTP (REST-N LEN1 X)))
            (OR (< LEN2 536870912)
                (<= LEN2 (LEN (REST-N LEN1 X))))
            (OR (< LEN2 536870912) (NATP LEN2))
            (OR (< LEN2 536870912) (INTEGERP LEN2))
            (LET ((PART2 (IF (< LEN2 536870912)
                             (FAST-COMPARABLE-MERGESORT-FIXNUMS (REST-N LEN1 X)
                                                                LEN2)
                             (FAST-COMPARABLE-MERGESORT-INTEGERS (REST-N LEN1 X)
                                                                 LEN2))))
                 (AND (COMPARABLE-LISTP PART1)
                      (COMPARABLE-LISTP PART2))))))))))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (NOT (ZP LEN))
                   (NOT (EQL LEN 1)))
              (LET ((VAR (ASH LEN -1)))
                   (INTEGERP VAR)))
     (IMPLIES (AND (INTEGERP LEN)
                   (<= LEN (LEN X))
                   (NATP LEN)
                   (COMPARABLE-LISTP X)
                   (NOT (ZP LEN))
                   (EQL LEN 1)
                   (NOT (CONSP X)))
              (EQUAL X NIL)))
  :rule-classes nil)

(defthm fast-comparable-mergesort-integers-admission
; Modified after v6-1 by Matt K. because the-error no longer is defined.
  (and (o-p (nfix len))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o<
         (nfix
          (+ (ash len -1)
             (logand len 1)))
         (nfix len)))
       (implies (and (not (zp len)) (not (= len 1)))
                (o< (nfix (ash len -1))
                    (nfix len))))
  :rule-classes nil)

(defthm fast-comparable-mergesort-fixnums-admission
; Modified after v6-1 by Matt K. because the-error no longer is defined.
  (and (o-p (nfix len))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o<
         (nfix
          (+
           (ash len -1)
           (logand len 1)))
         (nfix len)))
       (implies
        (and (not (zp len)) (not (= len 1)))
        (o< (nfix (ash len -1))
            (nfix len))))
  :rule-classes nil)
