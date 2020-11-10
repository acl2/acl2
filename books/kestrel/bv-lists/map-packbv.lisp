; Functions to map packbv and unpack BV over lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv")
(include-book "unpackbv") ;todo: separate
(include-book "all-unsigned-byte-p2")
(include-book "all-all-unsigned-byte-p")
(include-book "../typed-lists-light/all-all-integerp")
(include-book "kestrel/typed-lists-light/all-integerp2" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/sequences/defmap" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "packbv-and-unpackbv")
(local (include-book "packbv-theorems"))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(defmap map-packbv (itemcount itemsize items-lst) (packbv itemcount itemsize items-lst) :fixed (itemcount itemsize)
  :declares ((xargs :guard (and (natp itemsize)(natp itemcount) ;automatically generate this from the guard for packbv?
                                (all-true-listp items-lst)
                                (all-all-integerp items-lst)
                                ))))

(defmap map-unpackbv (itemcount itemsize bv-lst) (unpackbv itemcount itemsize bv-lst) :fixed (itemcount itemsize)
  :declares ((xargs :guard (and (integer-listp bv-lst)
                                         (natp itemcount)
                                         (natp itemsize)))))

(defthm all-true-listp-of-map-unpackbv
  (implies (natp itemcount)
           (all-true-listp (map-unpackbv itemcount itemsize bv-lst)))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

(defthm items-have-len-of-map-unpackbv
  (implies (natp itemcount)
           (items-have-len itemcount (map-unpackbv itemcount itemsize bv-lst)))
  :hints (("Goal" :in-theory (enable map-unpackbv items-have-len))))

(defthm all-all-unsigned-byte-p-of-map-unpackbv
  (implies (natp size)
           (all-all-unsigned-byte-p size (map-unpackbv itemcount size bvs)))
  :hints (("Goal" :in-theory (enable map-unpackbv))))

;; (defun packbv-induct (n count ;size
;;                         bvs)
;;   (if (zp count)
;;       (list n count bvs)
;;     (packbv-induct (+ -1 ;(- size)
;;                       n) (+ -1 count) ;size
;;                       (cdr bvs))))


;fixme defmap should do this
(defthm equal-of-nil-and-map-packbv
  (equal (equal nil (map-packbv a b c))
         (equal 0 (len c)))
  :hints (("Goal" :in-theory (enable map-packbv))))

(defthm map-packbv-of-map-unpackbv
  (implies (and (natp itemcount)
                (posp itemsize))
           (equal (map-packbv itemcount itemsize (map-unpackbv itemcount itemsize bvs))
                  (bvchop-list (* itemcount itemsize) bvs)))
  :hints (("Goal" :in-theory (enable packbv map-packbv map-unpackbv))))

(defmap map-reverse-list (items) (reverse-list items)
  :declares ((xargs :guard (all-true-listp items))))

(defthm all-true-listp-of-map-reverse-list
  (all-true-listp (map-reverse-list x))
  :hints (("Goal" :in-theory (enable map-reverse-list all-true-listp))))

(defthm items-have-len-of-map-reverse-list
  (equal (items-have-len len (map-reverse-list x))
         (items-have-len len x))
  :hints (("Goal" :in-theory (enable map-reverse-list items-have-len))))

;fixme gen to any double-mapped predicate somehow??
(defthm all-all-unsigned-byte-p-of-map-reverse-list
  (equal (all-all-unsigned-byte-p width (map-reverse-list x))
         (all-all-unsigned-byte-p width x))
  :hints (("Goal" :in-theory (enable map-reverse-list all-all-unsigned-byte-p))))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
       (double-cdr-induct (cdr x) (cdr y)))))

;move hyps to conclusion?
(defthm equal-of-map-reverse-list-and-map-reverse-list
  (implies (and (all-true-listp x)
                (all-true-listp y)
                (true-listp x)
                (true-listp y)
                )
           (equal (equal (map-reverse-list x) (map-reverse-list y))
                  (equal x y)))
  :hints (("Goal" :induct (double-cdr-induct x y)
           :in-theory (enable MAP-REVERSE-LIST))))


;move?
;move hyps to conclusion?
;fixme in general a map function is invertible iff its core function is
(defthm equal-of-map-packbv-and-map-packbv
  (implies (and (items-have-len count x)
                (items-have-len count y)
                (natp count)
                (posp size)
                (all-all-unsigned-byte-p size x)
                (all-all-unsigned-byte-p size y)
                (true-listp x)
                (true-listp y)
                (all-true-listp x)
                (all-true-listp y))
           (equal (equal (map-packbv count size x) (map-packbv count size y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable map-packbv packbv)
           :induct (double-cdr-induct x y))))

(defthmd map-packbv-of-myif-arg3
  (equal (map-packbv m n (myif test a b))
         (myif test (map-packbv m n a)
               (map-packbv m n b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm all-unsigned-byte-p-of-map-packbv
  (implies (and (<= (* size count) n)
                (natp n)
                (natp size)
                (natp count))
           (all-unsigned-byte-p n (map-packbv count size items)))
  :hints (("Goal" :in-theory (enable map-packbv))))

(defthm all-all-integerp-of-map-reverse-list
  (implies (all-all-integerp x)
           (all-all-integerp (map-reverse-list x)))
  :hints (("Goal" :in-theory (enable all-all-integerp))))

(defthm all-integerp-of-map-packbv
  (all-integerp (map-packbv itemcount itemsize items-lst))
  :hints (("Goal" :in-theory (enable map-packbv))))

(defthm true-list-listp-of-map-reverse-list
  (true-list-listp (map-reverse-list x))
  :hints (("Goal" :in-theory (enable map-reverse-list))))
