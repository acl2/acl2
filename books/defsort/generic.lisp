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
(include-book "tools/save-obligs" :dir :system)
(include-book "std/util/defredundant" :dir :system)
(local (include-book "generic-impl"))
(set-enforce-redundancy t)

(defthmd comparable-mergesort-admission-nthcdr
  (implies (consp (cdr x))
           (< (len (nthcdr (floor (len x) 2) x))
              (len x)))
  :rule-classes :linear)

(defthmd comparable-mergesort-admission-take
  (implies (consp (cdr x))
           (< (len (take (floor (len x) 2) x))
              (len x)))
  :rule-classes :linear)

(defthmd fast-mergesort-admission-1
  (implies (and (not (zp len))
                (not (equal len 1)))
           (< (nfix (+ len (- (ash len -1))))
              (nfix len)))
  :rule-classes :linear)

(defthmd fast-mergesort-admission-2
  (implies (and (not (zp len))
                (not (equal len 1)))
           (< (nfix (ash len -1))
              (nfix len)))
  :rule-classes :linear)


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
   (implies (and (compare< x y)
                 (compare< y z)
                 (comparablep x)
                 (comparablep y)
                 (comparablep z))
            (compare< x z))))




(defund comparable-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (comparablep (car x))
           (comparable-listp (cdr x)))
    (element-list-final-cdr-p x)))

(std::defredundant :names (comparable-merge-admission))


(defund comparable-merge (x y)
  (declare (xargs :measure (+ (len x)
                              (len y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))
                  :verify-guards nil))
  (cond ((atom x)
         y)
        ((atom y)
         x)
        ((compare< (car y) (car x))
         (cons (car y) (comparable-merge x (cdr y))))
        (t
         ;; Either (car x) < (car y) or they are equivalent.  In either case,
         ;; for stability, take (car x) first.
         (cons (car x) (comparable-merge (cdr x) y)))))

(std::defredundant :names (comparable-merge-guards))

(verify-guards comparable-merge)

(defthm len-of-comparable-merge
  (equal (len (comparable-merge x y))
         (+ (len x) (len y))))

(defthm comparable-listp-of-comparable-merge
  (implies (and (force (comparable-listp x))
                (force (comparable-listp y)))
           (equal (comparable-listp (comparable-merge x y))
                  t)))

(defthm duplicity-of-comparable-merge
  (equal (duplicity a (comparable-merge x y))
         (+ (duplicity a x)
            (duplicity a y))))

(defthm true-listp-of-comparable-merge
  (implies (and (true-listp y)
                (true-listp x))
           (true-listp (comparable-merge x y)))
  :rule-classes :type-prescription)



(defund comparable-merge-tr (x y acc)
  (declare (xargs :measure (+ (len x)
                              (len y))
                  :guard (and (comparable-listp x)
                              (comparable-listp y))
                  :verify-guards nil))
  (cond ((atom x)
         (revappend-without-guard acc y))
        ((atom y)
         (revappend-without-guard acc x))
        ((compare< (car y) (car x))
         (comparable-merge-tr x (cdr y) (cons (car y) acc)))
        (t
         ;; Either (car x) < (car y) or they are equivalent.  In either case,
         ;; for stability, take (car x) first.
         (comparable-merge-tr (cdr x) y (cons (car x) acc)))))

(std::defredundant :names (comparable-merge-tr-guards))

(verify-guards comparable-merge-tr)

(std::defredundant :names (fast-comparable-mergesort-fixnums-admission))

(defund fast-comparable-mergesort-fixnums (x len)
  (declare (xargs :guard (and (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :verify-guards nil)
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
                         (- (the (signed-byte 30) len)
                            (the (signed-byte 30) len1))))
                (part1 (fast-comparable-mergesort-fixnums x len1))
                (part2 (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)))
           (comparable-merge-tr part1 part2 nil)))))

(std::defredundant :names (fast-comparable-mergesort-fixnums-guards))

(verify-guards fast-comparable-mergesort-fixnums)

(defmacro mergesort-fixnum-threshold () 536870912)

(std::defredundant :names (fast-comparable-mergesort-integers-admission))

(defund fast-comparable-mergesort-integers (x len)
  (declare (xargs :guard (and (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :verify-guards nil)
           (type integer len))
  (cond ((mbe :logic (zp len)
              :exec (eql (the integer len) 0))
         nil)

        ((eql (the integer len) 1)
         (list (car x)))

        (t
         (let* ((len1  (the integer (ash (the integer len) -1)))
                (len2  (the integer
                         (- (the integer len) (the integer len1))))
                (part1 (if (< (the integer len1) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums x len1)
                         (fast-comparable-mergesort-integers x len1)))
                (part2 (if (< (the integer len2) (mergesort-fixnum-threshold))
                           (fast-comparable-mergesort-fixnums (rest-n len1 x) len2)
                         (fast-comparable-mergesort-integers (rest-n len1 x) len2))))
           (comparable-merge-tr part1 part2 nil)))))

(std::defredundant :names (fast-comparable-mergesort-integers-guards))

(verify-guards fast-comparable-mergesort-integers)

(std::defredundant :names (comparable-mergesort-admission))

(defund comparable-mergesort (x)
  (declare (xargs :measure (len x)
                  :guard (comparable-listp x)
                  :verify-guards nil))
  (mbe :logic (cond ((atom x)
                     nil)
                    ((atom (cdr x))
                     (list (car x)))
                    (t
                     (let ((half (floor (len x) 2)))
                       (comparable-merge
                        (comparable-mergesort (take half x))
                        (comparable-mergesort (nthcdr half x))))))
       :exec (let ((len (len x)))
               (if (< len (mergesort-fixnum-threshold))
                   (fast-comparable-mergesort-fixnums x len)
                 (fast-comparable-mergesort-integers x len)))))


(defthm duplicity-of-comparable-mergesort
  (equal (duplicity a (comparable-mergesort x))
         (duplicity a x)))

(defthm true-listp-of-comparable-mergesort
  (true-listp (comparable-mergesort x))
  :rule-classes :type-prescription)

(defthm len-of-comparable-mergesort
  (equal (len (comparable-mergesort x))
         (len x)))


(defthm consp-of-comparable-mergesort
  (equal (consp (comparable-mergesort x))
         (consp x)))

(defthm comparable-listp-of-comparable-mergesort
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort x))))

(defthm comparable-mergesort-of-list-fix
  (equal (comparable-mergesort (list-fix x))
         (comparable-mergesort x)))

(defthm fast-comparable-mergesort-fixnums-of-len-is-spec
    (equal (fast-comparable-mergesort-fixnums x (len x))
           (comparable-mergesort x)))

(defthm fast-comparable-mergesort-integers-of-len-is-spec
  (equal (fast-comparable-mergesort-integers x (len x))
         (comparable-mergesort x)))

(std::defredundant :names (comparable-mergesort-guard))

(verify-guards comparable-mergesort)


(defund comparable-orderedp (x)
  (declare (xargs :guard (comparable-listp x)
                  :verify-guards nil))
  (cond ((atom x)
         t)
        ((atom (cdr x))
         t)
        ((compare< (first x) (second x))
         (comparable-orderedp (cdr x)))
        (t
         (and (not (compare< (second x) (first x)))
              (comparable-orderedp (cdr x))))))

(std::defredundant :names (comparable-orderedp-guard))

(verify-guards comparable-orderedp)

(defthm comparable-orderedp-of-comparable-merge
  (implies (and (comparable-orderedp x)
                (comparable-orderedp y))
           (comparable-orderedp (comparable-merge x y))))

(defthm comparable-orderedp-of-comparable-mergesort
  (comparable-orderedp (comparable-mergesort x)))

(defthm no-duplicatesp-equal-of-comparable-mergesort
  (equal (no-duplicatesp-equal (comparable-mergesort x))
         (no-duplicatesp-equal x)))


(defun-sk compare<-negation-transitive ()
  ;; This says that the negation of the comparison relation is also transitive.
  ;; One big effect of it is that incomparable elements -- where (not (compare<
  ;; x y)) and (not (compare< y x)) -- are all in an equivalence class under
  ;; the comparison function.  (Transitivity of compare< shows that elements
  ;; with (compare< x y) and (compare< y x) are in an equivalence class as
  ;; well.)
  (forall (x y z)
          (implies (and (not (compare< x y))
                        (not (compare< y z))
                        (comparablep x)
                        (comparablep y)
                        (comparablep z))
                   (not (compare< x z))))
  :rewrite :direct)

(defun-sk compare<-strict ()
  ;; We need this property of the comparison to make our merge functions
  ;; stable; if we don't know that either compare< or its negation is strict,
  ;; then it doesn't suffice to do only one comparison per element merged.
  (forall (x) (implies (comparablep x)
                       (not (compare< x x))))
  :rewrite :direct)


(std::defredundant :names (comparable-insert-guard))

(defund comparable-insert (elt x)
  (declare (xargs :guard (and (comparablep elt)
                              (comparable-listp x))))
  (if (atom x)
      (list elt)
    (if (compare< (car x) elt)
        (cons (car x) (comparable-insert elt (cdr x)))
      (cons elt x))))

(defthm comparable-orderedp-of-comparable-insert
  (implies (and (comparable-orderedp x)
                (comparable-listp x)
                (comparablep elt))
           (comparable-orderedp (comparable-insert elt x))))

(defthm comparable-listp-of-comparable-insert
  (implies (and (comparable-listp x)
                (comparablep elt))
           (comparable-listp (comparable-insert elt x))))

(defthm true-listp-of-comparable-insert
  (implies (true-listp x)
           (true-listp (comparable-insert elt x))))

(defund comparable-insertsort (x)
  (declare (xargs :guard (comparable-listp x)))
  (if (atom x)
      nil
    (comparable-insert (car x)
                       (comparable-insertsort (cdr x)))))

(std::defredundant :names (comparable-insertsort-guard))

(defthm comparable-listp-of-comparable-insertsort
  (implies (comparable-listp x)
           (comparable-listp (comparable-insertsort x))))

(defthm comparable-orderedp-of-comparable-insertsort
  (implies (comparable-listp x)
           (comparable-orderedp (comparable-insertsort x))))

(defthm true-listp-of-comparable-insertsort
  (true-listp (comparable-insertsort x)))


(defthm comparable-mergesort-equals-comparable-insertsort
  (implies (and (compare<-negation-transitive)
                (compare<-strict)
                (comparable-listp x))
           (equal (comparable-mergesort x)
                  (comparable-insertsort x))))
