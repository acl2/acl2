; A predicate to recognize arrays of bit-vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system) ;deprecate?
(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

(defund bv-arrayp (element-width length val)
  (declare (xargs :guard t))
  (and (all-unsigned-byte-p element-width val)
       (true-listp val)
       (equal (len val) length)))

(defthm bv-arrayp-forward-to-natp
  (implies (bv-arrayp element-width length val)
           (natp length))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm len-when-bv-arrayp
  (implies (bv-arrayp element-width length val)
           (equal (len val)
                  length))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm true-listp-when-bv-arrayp
  (implies (bv-arrayp bytesize numcols item1)
           (true-listp item1))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

;; this breaks the array abstraction
(defthm bv-arrayp-of-cons
  (equal (bv-arrayp bytesize len (cons item items))
         (and (unsigned-byte-p bytesize item)
              (bv-arrayp bytesize (+ -1 len) items)))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

;deprecate?
(defthm all-unsigned-byte-p-when-bv-arrayp
 (implies (bv-arrayp bytesize len input)
          (all-unsigned-byte-p bytesize input))
 :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm unsigned-byte-listp-when-bv-arrayp
 (implies (bv-arrayp bytesize len input)
          (unsigned-byte-listp bytesize input))
 :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm bv-arrayp-when-length-is-0
  (equal (bv-arrayp bytesize 0 val)
         (equal val nil))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthm bv-arrayp-when-not-consp
  (implies (not (consp val))
           (equal (bv-arrayp element-width length val)
                  (and (equal val nil)
                       (equal 0 length))))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthmd integerp-of-nth-when-bv-arrayp
  (implies (and (bv-arrayp freewidth freelen val)
                (natp n)
                (< n freelen))
           (integerp (nth n val)))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

(defthmd <=-of-0-and-nth-when-bv-arrayp
  (implies (and (bv-arrayp freewidth freelen val)
                (natp n)
                (< n freelen))
           (<= 0 (nth n val)))
  :hints (("Goal" :in-theory (enable bv-arrayp))))

;; Do not remove: helps justify the correctness of intersect-types in Axe.
(defthm bv-arrayp-when-bv-arrayp-narrower
  (implies (and (bv-arrayp small-element-width length val)
                (<= small-element-width element-width)
                (natp small-element-width)
                (natp element-width))
           (bv-arrayp element-width length val))
  :hints (("Goal" :in-theory (enable bv-arrayp))))
