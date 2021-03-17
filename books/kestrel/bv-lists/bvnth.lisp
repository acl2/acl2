; A BV version of nth
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Deprecate bvnth?
;; See also bv-array-read.

(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "all-unsigned-byte-p")
(include-book "bvchop-list")
(local (include-book "kestrel/lists-light/nth" :dir :system))

;we go from nth to this to bvnth - do we still?
(defund nth2 (indexsize n lst)
  (DECLARE (XARGS :GUARD (AND (INTEGERP N)
                              (natp indexsize)
                              ;(>= N 0)
                              (TRUE-LISTP Lst))))
  (nth (bvchop indexsize n) lst))

;can drop the ifix
(defund bvnth (element-size index-size index data)
  (declare (xargs :guard (and (natp element-size)
                              (natp index-size)
                              (integerp index)
                              (true-listp data)
                              )))
  (bvchop element-size (ifix (nth (bvchop index-size index) data))))

(defthm unsigned-byte-p-of-bvnth
  (implies (natp element-size)
           (unsigned-byte-p element-size (bvnth element-size index-size n data)))
  :hints (("Goal" :in-theory (enable bvnth))))

(defthm unsigned-byte-p-of-bvnth-gen
  (implies (and (<= element-size n)
                (natp n)
                (natp element-size))
           (unsigned-byte-p n (bvnth element-size index-size index data)))
  :hints (("Goal" :in-theory (enable bvnth))))

(defthm bvnth-of-bvchop
  (implies (and (<= isize n)
                (natp isize)
                (natp n))
           (equal (bvnth esize isize (bvchop n index) data)
                  (bvnth esize isize index data)))
  :hints (("Goal" :in-theory (enable BVNTH))))

;bozo gen
(defthm bvchop-8-bvnth-8
  (equal (bvchop 8 (bvnth 8 isize i vals))
         (bvnth 8 isize i vals)))

(defthm bvnth-when-data-isnt-an-all-unsigned-byte-p
  (implies (and (not (all-unsigned-byte-p esize data))
                (natp esize))
           (equal (bvnth esize isize index data)
                  (bvnth esize isize index (bvchop-list esize data))))
  :hints (("Goal"
           :cases ((<= (len data) (bvchop isize index)))
           :in-theory (enable bvnth bvchop-when-i-is-not-an-integer))))
