; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
(include-book "misc/records" :dir :system)
(local (include-book "misc/equal-by-g" :dir :system))
(local (include-book "centaur/misc/equal-by-nths" :dir :system))
(local (include-book "local"))


; array-rec.lisp
;
; This file defines some basic helper routines that can be used to convert
; arrays (by which we mean true-listp's of a certain length that are read and
; written by position, in the logical sense of STOBJ arrays) and records.


(defund array-to-rec (n arr rec)
  ;; Store arr[0]...arr[n] into rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      (s 0 (nth 0 arr) rec)
    (array-to-rec (- n 1) arr
                  (s n (nth n arr) rec))))

(defund rec-to-array (n rec arr)
  ;; Load arr[0]...arr[n] from rec[0]...rec[n]
  (declare (xargs :guard (and (natp n)
                              (true-listp arr))))
  (if (zp n)
      (update-nth 0 (g 0 rec) arr)
    (rec-to-array (- n 1) rec
                  (update-nth n (g n rec) arr))))

(defund delete-rec-indices (n rec)
  ;; Delete rec[0]...rec[n] from rec
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (s 0 nil rec)
    (delete-rec-indices (- n 1)
                        (s n nil rec))))

(defund array-rec-pair-p (arr rec len)
  ;; Recognize array/record pairs where the array has size LEN and the record
  ;; has nothing in keys 0...LEN-1.
  (declare (xargs :guard (posp len)))
  (and (true-listp arr)
       (= (len arr) len)
       (equal rec (delete-rec-indices (- len 1) rec))))









(local (in-theory (enable array-to-rec
                          rec-to-array
                          delete-rec-indices
                          array-rec-pair-p)))

(defthm g-of-array-to-rec
  (equal (g key (array-to-rec n arr rec))
         (if (and (natp key)
                  (<= key (nfix n)))
             (nth key arr)
           (g key rec))))



(defthm len-of-rec-to-array
  (equal (len (rec-to-array n rec arr))
         (max (+ 1 (nfix n)) (len arr))))

(defthm true-listp-of-rec-to-array
  (implies (true-listp arr)
           (true-listp (rec-to-array n rec arr))))

(defthm nth-of-rec-to-array
  (equal (nth key (rec-to-array n rec arr))
         (cond ((zp key)
                (g 0 rec))
               ((<= key (nfix n))
                (g key rec))
               (t
                (nth key arr)))))

(defthm nth-of-rec-to-array-of-array-to-rec
  (implies (and (natp key)
                (<= key n)
                (equal (len arr1) (len arr2))
                (natp n)
                (<= n (len arr1)))
           (equal (nth key (rec-to-array n (array-to-rec n arr1 rec) arr2))
                  (nth key arr1))))

(defthm rec-to-array-of-array-to-rec
  (implies (and (force (equal (len arr1) (len arr2)))
                (force (equal n (- (len arr1) 1)))
                (force (posp (len arr1)))
                (force (true-listp arr1))
                (force (true-listp arr2)))
           (equal (rec-to-array n (array-to-rec n arr1 rec) arr2)
                  arr1))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (equal (len arr1) (len arr2))
                                           (equal n (- (len arr1) 1))
                                           (true-listp arr1)
                                           (true-listp arr2))))
                 (equal-by-nths-lhs (lambda ()
                                      (rec-to-array n (array-to-rec n arr1 rec) arr2)))
                 (equal-by-nths-rhs (lambda ()
                                      arr1)))))))

(defthm rec-to-array-idempotent
  (implies (and (force (posp (len arr1)))
                (force (true-listp arr1)))
           (equal (rec-to-array n val1 (rec-to-array n val2 arr1))
                  (rec-to-array n val1 arr1)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (posp (len arr1))
                                           (true-listp arr1))))
                 (equal-by-nths-lhs (lambda ()
                                      (rec-to-array n val1 (rec-to-array n val2 arr1))))
                 (equal-by-nths-rhs (lambda ()
                                      (rec-to-array n val1 arr1))))))))



(defthm rec-to-array-of-set-index
  (implies (and (natp n)
                (natp i)
                (<= i n)
                (true-listp arr))
           (equal (rec-to-array n (s i val rec) arr)
                  (update-nth i val (rec-to-array n rec arr))))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-nths
                 (equal-by-nths-hyp (lambda ()
                                      (and (natp n)
                                           (natp i)
                                           (<= i n)
                                           (true-listp arr))))
                 (equal-by-nths-lhs (lambda ()
                                      (rec-to-array n (s i val rec) arr)))
                 (equal-by-nths-rhs (lambda ()
                                      (update-nth i val (rec-to-array n rec arr)))))))))



(defthm delete-rec-indices-when-nil
  (equal (delete-rec-indices n nil)
         nil))

(defthm g-of-delete-rec-indices
  (equal (g key (delete-rec-indices n rec))
         (if (and (natp key)
                  (<= key (nfix n)))
             nil
           (g key rec))))

(defthm delete-rec-indicies-of-array-to-rec
  (equal (delete-rec-indices n (array-to-rec n arr rec))
         (delete-rec-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-g
                 (equal-by-g-hyp (lambda () t))
                 (equal-by-g-lhs (lambda ()
                                   (delete-rec-indices n (array-to-rec n arr rec))))
                 (equal-by-g-rhs (lambda ()
                                   (delete-rec-indices n rec))))))))

(defthm delete-rec-indices-of-set-index
  (implies (and (natp n)
                (natp i)
                (<= i n))
           (equal (delete-rec-indices n (s i val rec))
                  (delete-rec-indices n rec)))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-g
                 (equal-by-g-hyp (lambda ()
                                   (and (natp n)
                                        (natp i)
                                        (<= i n))))
                 (equal-by-g-lhs (lambda ()
                                   (delete-rec-indices n (s i val rec))))
                 (equal-by-g-rhs (lambda ()
                                   (delete-rec-indices n rec))))))))


(defthm array-to-rec-inverse-lemma
  (equal (g key (array-to-rec n
                              (rec-to-array n rec arr)
                              (delete-rec-indices n rec)))
         (g key rec)))

(defthm array-to-rec-inverse
  (equal (array-to-rec n
                       (rec-to-array n rec arr)
                       (delete-rec-indices n rec))
         rec)
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-g
                 (equal-by-g-hyp (lambda () t))
                 (equal-by-g-lhs (lambda ()
                                   (array-to-rec n
                                                 (rec-to-array n rec arr)
                                                 (delete-rec-indices n rec))))
                 (equal-by-g-rhs (lambda () rec)))))))

(defthm delete-rec-indices-idempotent
  (equal (delete-rec-indices n (delete-rec-indices n rec))
         (delete-rec-indices n rec))
  :hints(("Goal"
          :use ((:functional-instance
                 equal-by-g
                 (equal-by-g-hyp (lambda () t))
                 (equal-by-g-lhs (lambda ()
                                   (delete-rec-indices n (delete-rec-indices n rec))))
                 (equal-by-g-rhs (lambda ()
                                   (delete-rec-indices n rec))))))))



(defthm array-rec-pair-p-of-nil
  (implies (and (true-listp arr)
                (equal (len arr) n))
           (array-rec-pair-p arr nil n)))

(defthm array-rec-pair-p-of-update-nth
  (implies (and (array-rec-pair-p arr rec len)
                (force (natp n))
                (force (posp len))
                (force (< n len)))
           (array-rec-pair-p (update-nth n val arr) rec len)))

(defthm array-rec-pair-p-of-delete-rec-indices
  (implies (array-rec-pair-p arr rec len)
           (array-rec-pair-p arr (delete-rec-indices (- len 1) rec) len)))


