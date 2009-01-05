; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact: Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "tools/with-arith4-help" :dir :system)
(include-book "unicode/take" :dir :system)
(include-book "unicode/nthcdr" :dir :system)
(include-book "unicode/list-fix" :dir :system)
(include-book "duplicity")
(allow-arith4-help)


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
            (compare< x z)))
 )




(defund comparable-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (comparablep (car x))
           (comparable-listp (cdr x)))
    t))

(defthm comparable-listp-when-not-consp
  (implies (not (consp x))
           (equal (comparable-listp x)
                  t))
  :hints(("Goal" :in-theory (enable comparable-listp))))

(defthm comparable-listp-of-cons
  (equal (comparable-listp (cons a x))
         (and (comparablep a)
              (comparable-listp x)))
  :hints(("Goal" :in-theory (enable comparable-listp))))

(defthm comparable-listp-of-simpler-take
  (implies (and (force (comparable-listp x))
                (force (<= (nfix n) (len x))))
           (comparable-listp (simpler-take n x)))
  :hints(("Goal" 
          :in-theory (enable (:induction simpler-take))
          :induct (simpler-take n x))))

(defthm comparable-listp-of-nthcdr
  (implies (force (comparable-listp x))
           (comparable-listp (nthcdr n x)))
  :hints(("Goal"
          :in-theory (enable (:induction nthcdr))
          :induct (nthcdr n x))))

(defthm comparable-listp-of-cdr
  (implies (comparable-listp x)
           (comparable-listp (cdr x))))

(defthm comparablep-of-car
  (implies (comparable-listp x)
           (equal (comparablep (car x))
                  (or (consp x)
                      (comparablep nil)))))
                                      
                           
(defthm comparable-merge-admission 
  (AND (O-P (+ (ACL2-COUNT X) (ACL2-COUNT Y)))
       (IMPLIES (AND (NOT (ATOM X))
                     (NOT (ATOM Y))
                     (NOT (COMPARE< (CAR Y) (CAR X))))
                (O< (+ (ACL2-COUNT (CDR X)) (ACL2-COUNT Y))
                    (+ (ACL2-COUNT X) (ACL2-COUNT Y))))
       (IMPLIES (AND (NOT (ATOM X))
                     (NOT (ATOM Y))
                     (COMPARE< (CAR Y) (CAR X)))
                (O< (+ (ACL2-COUNT X) (ACL2-COUNT (CDR Y)))
                    (+ (ACL2-COUNT X) (ACL2-COUNT Y)))))
  :rule-classes nil)

(defund comparable-merge (x y)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))
                  :hints(("Goal" :use ((:instance comparable-merge-admission))))
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
  :rule-classes nil
  :hints(("goal" :in-theory (enable comparable-merge))))

(encapsulate
 ()
 (local (in-theory nil))
 (verify-guards comparable-merge
                :hints(("Goal"
                        :use ((:instance comparable-merge-guards))))))


(defthm comparable-listp-of-comparable-merge
  (implies (and (force (comparable-listp x))
                (force (comparable-listp y)))
           (equal (comparable-listp (comparable-merge x y))
                  t))
  :hints(("Goal" :in-theory (enable comparable-merge))))

(defthm comparable-merge-when-not-consp-left
  (implies (not (consp x))
           (equal (comparable-merge x y)
                  y))
  :hints(("Goal" :in-theory (enable comparable-merge))))

(defthm comparable-merge-when-not-consp-right
  (implies (not (consp y))
           (equal (comparable-merge x y)
                  (if (consp x)
                      x
                    y)))
  :hints(("Goal" :in-theory (enable comparable-merge))))



(with-arith4-help
 (defthm comparable-mergesort-spec-admission
   (AND (O-P (LEN X))
        (IMPLIES (AND (NOT (ATOM X))
                      (NOT (ATOM (CDR X))))
                 (O< (LEN (NTHCDR (FLOOR (LEN X) 2) X))
                     (LEN X)))
        (IMPLIES (AND (NOT (ATOM X))
                      (NOT (ATOM (CDR X))))
                 (O< (LEN (TAKE (FLOOR (LEN X) 2) X))
                     (LEN X))))
   :rule-classes nil))

(defund comparable-mergesort-spec (x)
  (declare (xargs :measure (len x)
                  :hints(("Goal" :use ((:instance comparable-mergesort-spec-admission))))))
  (cond ((atom x) 
         nil)
        ((atom (cdr x))
         (list (car x)))
        (t
         (let ((half (floor (len x) 2)))
           (comparable-merge 
            (comparable-mergesort-spec (take half x))
            (comparable-mergesort-spec (nthcdr half x)))))))







; Refinement 1.  We replace "(floor (len x) 2)" with (first-half-len (len x)),
; in order to keep our arithmetic relatively simple.

(encapsulate
 ()
 (local (in-theory (enable-arith4)))

 (defthm true-listp-of-nthcdr-weak
   (implies (true-listp x)
            (true-listp (nthcdr n x))))

 (defthm simpler-take-of-simpler-take
   (implies (< (nfix a) (nfix b))
            (equal (simpler-take a (simpler-take b x))
                   (simpler-take a x))))

 (defthm simpler-take-of-simpler-take-same
   (equal (simpler-take a (simpler-take a x))
          (simpler-take a x)))

 (defthm simpler-take-of-len
   (equal (simpler-take (len x) x)
          (list-fix x)))

 (defund first-half-len (len)
   (declare (xargs :guard (natp len)))
   (floor (nfix len) 2))

 (defthm natp-of-first-half-len
   (natp (first-half-len len))
   :rule-classes :type-prescription)

 (defthm first-half-len-less
   (implies (< 0 len)
            (< (first-half-len len) len))
   :rule-classes (:rewrite :linear)
   :hints(("Goal" :in-theory (enable first-half-len))))

 (defthm first-half-len-zero
   (equal (equal (first-half-len len) 0)
          (or (zp len)
              (= len 1)))
   :hints(("Goal" :in-theory (enable first-half-len))))

 (defund second-half-len (len)
   (declare (xargs :guard (natp len)))
   (+ (floor (nfix len) 2)
      (mod (nfix len) 2)))

 (defthm natp-of-second-half-len
   (natp (second-half-len len))
   :rule-classes :type-prescription)

 (defthm second-half-len-less
   (implies (and (natp len)
                 (not (= 0 len))
                 (not (= 1 len)))
            (< (second-half-len len) len))
   :rule-classes (:rewrite :linear)
   :hints(("Goal" :in-theory (enable second-half-len))))

 (defthm second-half-len-zero
   (equal (equal (second-half-len len) 0)
          (zp len))
   :hints(("Goal" :in-theory (enable second-half-len zp))))

 (defthm first-plus-second-half
   (implies (natp len)
            (equal (+ (first-half-len len)
                      (second-half-len len))
                   len))
   :hints(("Goal" :in-theory (enable first-half-len second-half-len)))))

(defund comparable-mergesort-spec2 (x)
  (declare (xargs :measure (len x)
                  :hints(("Goal" 
                          :use ((:instance comparable-mergesort-spec-admission))
                          :in-theory (enable first-half-len)))))
  (cond ((atom x) 
         nil)
        ((atom (cdr x))
         (list (car x)))
        (t
         (let ((half (first-half-len (len x))))
           (comparable-merge 
            (comparable-mergesort-spec2 (take half x))
            (comparable-mergesort-spec2 (nthcdr half x)))))))

(defthm true-listp-of-comparable-merge
  (implies (and (true-listp y)
                (true-listp x))
           (true-listp (comparable-merge x y)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable comparable-merge))))

(defthm true-listp-of-comparable-mergesort-spec2
  (true-listp (comparable-mergesort-spec2 x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))

(defthm comparable-mergesort-spec-redefinition
  (equal (comparable-mergesort-spec x)
         (comparable-mergesort-spec2 x))
  :hints(("Goal" :in-theory (enable comparable-mergesort-spec
                                    comparable-mergesort-spec2
                                    first-half-len))))

(defthm comparable-listp-of-comparable-mergesort-spec2
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort-spec2 x)))
  :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))

(defthm comparable-listp-of-comparable-mergesort-spec
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort-spec x))))




; Refinement 2.  Our efficient sorting routine only tries to sort the first n
; elements of the list.  This allows us to implicitly partition the list
; without having to do any consing.

(defun comparable-mergesort-spec3 (x len)
  (declare (xargs :guard (and (true-listp x)
                              (comparable-listp x)
                              (<= len (len x)))
                  :measure (nfix len)
                  :verify-guards nil)
           (type integer len))

; This computes (comparable-mergesort-spec (take len x)).

  (cond ((zp len)
         nil)
        ((= len 1)
         (list (car x)))
        (t
         (let* ((len1  (first-half-len len))
                (len2  (second-half-len len))
                (part1 (comparable-mergesort-spec3 x len1))
                (part2 (comparable-mergesort-spec3 (nthcdr len1 x) len2)))
           (comparable-merge part1 part2)))))

(encapsulate
 ()
 (local (in-theory (enable-arith4)))

 (local (defthm crock
          (implies (and (natp len1)
                        (natp len2))
                   (equal (NTHCDR len1 (SIMPLER-TAKE (+ len1 len2) X))
                          (SIMPLER-TAKE len2 (NTHCDR len1 X))))))

 (local (defthm crock2
          (implies (and (natp len)
                        (<= len (len x)))
                   (equal (NTHCDR (FIRST-HALF-LEN LEN) (SIMPLER-TAKE LEN X))
                          (SIMPLER-TAKE (SECOND-HALF-LEN LEN)
                                        (NTHCDR (FIRST-HALF-LEN LEN) X))))
          :hints(("Goal"
                  :in-theory (disable crock)
                  :use ((:instance crock
                                   (len1 (first-half-len len))
                                   (len2 (second-half-len len))))))))
                              
 (defthm comparable-mergesort-spec3-redefinition
   (implies (<= len (len x))
            (equal (comparable-mergesort-spec3 x len)
                   (comparable-mergesort-spec2 (simpler-take len x))))
   :hints(("Goal"
           :do-not '(generalize eliminate-destructors)
           :induct (comparable-mergesort-spec3 x len)
           :in-theory (enable comparable-mergesort-spec3
                              comparable-mergesort-spec2)
           :expand (comparable-mergesort-spec2 (simpler-take len x))))))

(defthm comparable-listp-of-comparable-mergesort-spec3
  (implies (and (<= len (len x))
                (force (comparable-listp x)))
           (comparable-listp (comparable-mergesort-spec3 x len))))



; Refinement 3.  We now add fixnum and integer declarations, in order to make
; the arithmetic faster.

(with-arith4-help
 (defthm fast-comparable-mergesort-fixnums-admission
   (AND (O-P (NFIX LEN))
        (IMPLIES
         (AND (NOT (ZP LEN)) (NOT (= LEN 1)))
         (O<
          (NFIX
           (LET
            ((VAR
              (+
               (LET
                ((VAR
                  (LET ((VAR (ASH (LET ((VAR LEN))
                                       (IF (SIGNED-BYTE-P 30 VAR)
                                           VAR (THE-ERROR '(SIGNED-BYTE 30) VAR)))
                                  -1)))
                       (IF (SIGNED-BYTE-P 30 VAR)
                           VAR
                           (THE-ERROR '(SIGNED-BYTE 30) VAR)))))
                (IF (SIGNED-BYTE-P 30 VAR)
                    VAR (THE-ERROR '(SIGNED-BYTE 30) VAR)))
               (LET ((VAR (LOGAND (LET ((VAR LEN))
                                       (IF (SIGNED-BYTE-P 30 VAR)
                                           VAR (THE-ERROR '(SIGNED-BYTE 30) VAR)))
                                  1)))
                    (IF (SIGNED-BYTE-P 30 VAR)
                        VAR
                        (THE-ERROR '(SIGNED-BYTE 30) VAR))))))
            (IF (SIGNED-BYTE-P 30 VAR)
                VAR (THE-ERROR '(SIGNED-BYTE 30) VAR))))
          (NFIX LEN)))
        (IMPLIES
         (AND (NOT (ZP LEN)) (NOT (= LEN 1)))
         (O< (NFIX (LET ((VAR (ASH (LET ((VAR LEN))
                                        (IF (SIGNED-BYTE-P 30 VAR)
                                            VAR (THE-ERROR '(SIGNED-BYTE 30) VAR)))
                                   -1)))
                        (IF (SIGNED-BYTE-P 30 VAR)
                            VAR (THE-ERROR '(SIGNED-BYTE 30) VAR))))
             (NFIX LEN))))
   :rule-classes nil))

(defund fast-comparable-mergesort-fixnums (x len)
  (declare (xargs :guard (and (true-listp x)
                              (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :hints(("Goal" :use ((:instance fast-comparable-mergesort-fixnums-admission))))
                  :verify-guards nil)
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

(with-arith4-help
 (defthm fast-comparable-mergesort-fixnums-redefinition
   (equal (fast-comparable-mergesort-fixnums x len)
          (comparable-mergesort-spec3 x len))
   :hints(("Goal"
           :in-theory (e/d (fast-comparable-mergesort-fixnums
                            comparable-mergesort-spec3
                            first-half-len
                            second-half-len)
                           (comparable-mergesort-spec3-redefinition))))))

(defthm comparable-listp-of-fast-comparable-mergesort-fixnums
  (implies (and (<= len (len x))
                (force (comparable-listp x)))
           (comparable-listp (fast-comparable-mergesort-fixnums x len))))



(with-arith4-help
 ;; To generate this, run (in-theory (theory 'minimal-theory)) and then try to
 ;; verify-guards.
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
   :rule-classes nil
   :hints(("Goal" 
           :in-theory (disable fast-comparable-mergesort-fixnums-redefinition)))))

(encapsulate
 ()
 (local (in-theory nil))
 (verify-guards fast-comparable-mergesort-fixnums
                :hints(("Goal"
                        :use ((:instance fast-comparable-mergesort-fixnums-guards))))))



(defconst *mergesort-fixnum-threshold* 536870912)


(with-arith4-help
 (defthm fast-comparable-mergesort-integers-admission
   (AND (O-P (NFIX LEN))
        (IMPLIES
         (AND (NOT (ZP LEN)) (NOT (= LEN 1)))
         (O<
          (NFIX
           (LET
            ((VAR
              (+ (LET ((VAR (LET ((VAR (ASH (LET ((VAR LEN))
                                                 (IF (INTEGERP VAR)
                                                     VAR (THE-ERROR 'INTEGER VAR)))
                                            -1)))
                                 (IF (INTEGERP VAR)
                                     VAR (THE-ERROR 'INTEGER VAR)))))
                      (IF (INTEGERP VAR)
                          VAR (THE-ERROR 'INTEGER VAR)))
                 (LET ((VAR (LOGAND (LET ((VAR LEN))
                                         (IF (INTEGERP VAR)
                                             VAR (THE-ERROR 'INTEGER VAR)))
                                    1)))
                      (IF (INTEGERP VAR)
                          VAR (THE-ERROR 'INTEGER VAR))))))
            (IF (INTEGERP VAR)
                VAR (THE-ERROR 'INTEGER VAR))))
          (NFIX LEN)))
        (IMPLIES (AND (NOT (ZP LEN)) (NOT (= LEN 1)))
                 (O< (NFIX (LET ((VAR (ASH (LET ((VAR LEN))
                                                (IF (INTEGERP VAR)
                                                    VAR (THE-ERROR 'INTEGER VAR)))
                                           -1)))
                                (IF (INTEGERP VAR)
                                    VAR (THE-ERROR 'INTEGER VAR))))
                     (NFIX LEN))))
   :rule-classes nil))

(defund fast-comparable-mergesort-integers (x len)
  (declare (xargs :guard (and (true-listp x)
                              (comparable-listp x)
                              (natp len)
                              (<= len (len x)))
                  :measure (nfix len)
                  :hints(("Goal" :use ((:instance fast-comparable-mergesort-integers-admission))))
                  :verify-guards nil)
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

(with-arith4-help
 (defthm fast-comparable-mergesort-integers-redefinition
   (equal (fast-comparable-mergesort-integers x len)
          (comparable-mergesort-spec3 x len))
   :hints(("Goal"
           :in-theory (e/d (fast-comparable-mergesort-integers
                            comparable-mergesort-spec3
                            first-half-len
                            second-half-len)
                           (comparable-mergesort-spec3-redefinition))))))

(defthm comparable-listp-of-fast-comparable-mergesort-integers
  (implies (and (<= len (len x))
                (force (comparable-listp x)))
           (comparable-listp (fast-comparable-mergesort-integers x len))))


(encapsulate
 ()
 (local (defthm crock
          (equal (fast-comparable-mergesort-fixnums x len)
                 (fast-comparable-mergesort-integers x len))
          :hints(("Goal" :in-theory (e/d (fast-comparable-mergesort-integers
                                          fast-comparable-mergesort-fixnums)
                                         (fast-comparable-mergesort-fixnums-redefinition
                                          fast-comparable-mergesort-integers-redefinition))))))
  
 (with-arith4-help
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
    :rule-classes nil
    :hints(("Goal" :in-theory (disable 
                               fast-comparable-mergesort-integers-redefinition
                               fast-comparable-mergesort-fixnums-redefinition)))))

 (local (in-theory nil))
 (verify-guards fast-comparable-mergesort-integers
                :hints(("Goal" 
                        :use ((:instance fast-comparable-mergesort-integers-guards))))))



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
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable comparable-mergesort))))


(defthm nthcdr-of-list-fix
  (equal (nthcdr n (list-fix x))
         (list-fix (nthcdr n x))))

(defthm simpler-take-of-list-fix
  (equal (simpler-take n (list-fix x))
         (list-fix (simpler-take n x))))

(defthm comparable-mergesort-spec2-of-list-fix
  (equal (comparable-mergesort-spec2 (list-fix x))
         (comparable-mergesort-spec2 x))
  :hints(("Goal"
          :in-theory (enable comparable-mergesort-spec2))))

(defthm comparable-mergesort-redefinition
  (equal (comparable-mergesort x)
         (comparable-mergesort-spec x))
  :hints(("Goal" :in-theory (enable comparable-mergesort))))

(defthm comparable-listp-of-comparable-mergesort
  (implies (force (comparable-listp x))
           (comparable-listp (comparable-mergesort x)))
  :hints(("Goal" :in-theory (enable comparable-mergesort))))





;; We now establish that sorting preserves the duplicities of elements.  In
;; other words, the output is a permutation of its input.

(defthm duplicity-of-list-fix
  (equal (duplicity a (list-fix x))
         (duplicity a x))
  :hints(("Goal" :induct (len x))))

(defthm duplicity-of-pieces
  (implies (and (natp n)
                (< n (len x)))
           (equal (+ (duplicity a (simpler-take n x))
                     (duplicity a (nthcdr n x)))
                  (duplicity a x))))

(defthm duplicity-of-comparable-merge
  (equal (duplicity a (comparable-merge x y))
         (+ (duplicity a x)
            (duplicity a y)))
  :hints(("Goal" :in-theory (enable comparable-merge))))

(with-arith4-help
 (defthm duplicity-of-comparable-mergesort-spec2
   (equal (duplicity a (comparable-mergesort-spec2 x))
          (duplicity a x))
   :hints(("Goal" :in-theory (enable comparable-mergesort-spec2)))))

(with-arith4-help
 (defthm duplicity-of-comparable-mergesort
   (equal (duplicity a (comparable-mergesort x))
          (duplicity a x))
   :hints(("Goal" :in-theory (enable comparable-mergesort)))))




; We now establish that the sort returns produces an ordered list.  There may
; be "equivalent" elements in the list, where we simultaneously have:
;
;    (compare< a b) = nil
;    (compare< b a) = nil
;
; For instance, when sorting integers with <, if there are any duplicates in
; the input list then we will have this situation.  So we only want to ensure
; that, for every A which preceeds B in the list, either A < B, or A === B in
; the above sense.

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
         (and (not (compare< (cadr x) (car x)))
              (comparable-orderedp (cdr x))))))

(defthm comparable-orderedp-guard
  (AND (IMPLIES (AND (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM (CDR X))))
                (COMPARABLEP (CAR X)))
       (IMPLIES (AND (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM (CDR X))))
                (COMPARABLEP (CADR X)))
       (IMPLIES (AND (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM (CDR X)))
                     (COMPARE< (CAR X) (CADR X)))
                (COMPARABLE-LISTP (CDR X)))
       (IMPLIES (AND (COMPARABLE-LISTP X)
                     (NOT (ATOM X))
                     (NOT (ATOM (CDR X)))
                     (NOT (COMPARE< (CADR X) (CAR X))))
                (COMPARABLE-LISTP (CDR X))))
  :rule-classes nil)

(encapsulate
 ()
 (local (in-theory nil))
 (verify-guards comparable-orderedp
                :hints(("Goal" 
                        :use ((:instance comparable-orderedp-guard))))))

(defthm comparable-orderedp-when-not-consp
  (implies (not (consp x))
           (comparable-orderedp x))
  :hints(("Goal" :in-theory (enable comparable-orderedp))))

(defthm comparable-orderedp-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (comparable-orderedp x))
  :hints(("Goal" :in-theory (enable comparable-orderedp))))

(defthm comparable-orderedp-of-comparable-merge
  (implies (and (comparable-orderedp x)
                (comparable-orderedp y))
           (comparable-orderedp (comparable-merge x y)))
  :hints(("Goal" :in-theory (enable comparable-merge comparable-orderedp))))

(defthm comparable-orderedp-of-comparable-mergesort-spec2
  (comparable-orderedp (comparable-mergesort-spec2 x))
  :hints(("Goal" :in-theory (enable comparable-mergesort-spec2))))


(with-arith4-help
 (defthm comparable-orderedp-of-comparable-mergesort
   (comparable-orderedp (comparable-mergesort x))))

(defthm no-duplicatesp-equal-of-comparable-mergesort
  (equal (no-duplicatesp-equal (comparable-mergesort x))
         (no-duplicatesp-equal x))
  :hints(("Goal"
          :use ((:functional-instance no-duplicatesp-equal-same-by-duplicity
                                      (duplicity-hyp (lambda () t))
                                      (duplicity-lhs (lambda () (comparable-mergesort x)))
                                      (duplicity-rhs (lambda () x)))))))

  
                               
