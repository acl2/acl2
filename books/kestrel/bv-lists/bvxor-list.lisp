
; BV List Library: bvxor-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../typed-lists-light/all-integerp")
(include-book "all-unsigned-byte-p")
(include-book "unsigned-byte-listp-def")
(include-book "../bv/bvxor")

(defund bvxor-list (size x y)
  (declare (xargs :guard (and (all-integerp x)
                              (all-integerp y)
                              (<= (len x) (len y))))
           (type (integer 0 *) size))
  (if (atom x)
      nil
    (cons (bvxor size (car x) (car y))
          (bvxor-list size (cdr x) (cdr y)))))

(defthm bvxor-list-of-nil
  (equal (bvxor-list size nil y)
         nil)
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm len-of-bvxor-list
  (equal (len (bvxor-list size x y))
         (len x))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm consp-of-bvxor-list
  (equal (consp (bvxor-list size x y))
         (consp x))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm nth-of-bvxor-list
  (implies (and (equal (len vals1) (len vals2))
                (natp index)
                (< index (len vals1)))
           (equal (nth index (bvxor-list size vals1 vals2))
                  (bvxor size (nth index vals1)
                         (nth index vals2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((bvxor-list size vals1 vals2))
           :in-theory (enable bvxor-list nth))))

(defthm all-unsigned-byte-p-of-bvxor-list
  (implies (natp size)
           (all-unsigned-byte-p size (bvxor-list size x y)))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm unsigned-byte-listp-of-bvxor-list
  (implies (natp size)
           (unsigned-byte-listp size (bvxor-list size x y)))
  :hints (("Goal" :in-theory (enable bvxor-list unsigned-byte-listp))))

(defthm all-integerp-of-bvxor-list
  (all-integerp (bvxor-list size x y))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm bvxor-list-iff
  (iff (bvxor-list size x y)
       (consp x))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm take-of-bvxor-list
  (implies (and (natp n)
                (<= n (len x)))
           (equal (take n (bvxor-list size x y))
                  (bvxor-list size (take n x) (take n y))))
  :hints (("Goal" :in-theory (enable take bvxor-list))))

(defthm nthcdr-of-bvxor-list
  (implies (and (natp n)
                (<= n (len x)))
           (equal (nthcdr n (bvxor-list size x y))
                  (bvxor-list size (nthcdr n x) (nthcdr n y))))
  :hints (("Goal" :in-theory (enable nthcdr bvxor-list))))

(defthm bvxor-list-of-true-list-fix-arg2
  (equal (bvxor-list size (true-list-fix x) y)
         (bvxor-list size x y))
  :hints (("Goal" :in-theory (enable bvxor-list))))

(defthm bvxor-list-of-true-list-fix-arg3
  (equal (bvxor-list size x (true-list-fix y))
         (bvxor-list size x y))
  :hints (("Goal" :in-theory (enable bvxor-list))))
