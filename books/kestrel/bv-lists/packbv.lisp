; BV Lists Library: theorems about packbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "packbv-def")
(include-book "all-unsigned-byte-p")
(include-book "../bv/bvcat-def")
(include-book "../bv/getbit")
(include-book "../lists-light/repeat")
(local (include-book "../bv/bvcat"))
(local (include-book "../bv/unsigned-byte-p"))
(local (include-book "../../ihs/ihs-lemmas")) ;why? for <-*-left-cancel
(local (include-book "../lists-light/butlast"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../../meta/meta-plus-lessp"))

(local (in-theory (disable mod-x-y-=-x+y-for-rationals))) ;bad

(defthm <-cancel-hack
  (implies (and (posp size)
                (rationalp count)
                (rationalp n))
           (equal (< (+ (- size) (* count size)) (* n size))
                  (< (+ -1 count) n)))
  :hints (("Goal" :use (:instance <-*-left-cancel (z size) (x (+ -1 count)) (y n)))))

(defthmd packbv-base
  (implies (zp itemcount)
           (equal (packbv itemcount itemsize items)
                  0))
  :hints (("Goal" :in-theory (enable packbv))))

(defthmd packbv-opener
  (implies (not (zp itemcount))
           (equal (packbv itemcount itemsize items)
                  (bvcat itemsize
                         (car items)
                         (* itemsize (+ -1 itemcount))
                         (packbv (+ -1 itemcount) itemsize (cdr items)))))
  :hints (("Goal" :in-theory (enable packbv))))

(defthm packbv-of-0
  (equal (packbv 0 size bvs)
         0)
  :hints (("Goal" :in-theory (enable packbv))))

(defthm unsigned-byte-p-of-packbv
  (implies (and (natp size)
                (natp num))
           (unsigned-byte-p (* size num)
                            (packbv num size items)))
  :hints (("Goal" :in-theory (enable packbv))))

(defthm unsigned-byte-p-of-packbv-gen
  (implies (and (<= (* size num) n)
                (natp size)
                (natp n)
                (natp num))
           (unsigned-byte-p n (packbv num size items)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-packbv)
           :in-theory (disable unsigned-byte-p-of-packbv))))

;gen the 1
(defthm bvchop-of-packbv-1-helper
  (implies (and (<= n count)
                (natp n)
                (natp count))
           (equal (bvchop n (packbv count 1 bvs))
                  (packbv n 1 (nthcdr (- count n) bvs))))
  :hints (("Goal" :in-theory (enable packbv))))

;gen the 1?
(defthm bvchop-of-packbv-1
  (implies (and (<= n count)
                (natp count))
           (equal (bvchop n (packbv count 1 bvs))
                  (packbv n 1 (nthcdr (- count n) bvs))))
  :hints (("Goal" :use (:instance bvchop-of-packbv-1-helper)
           :in-theory (e/d (packbv-base) (bvchop-of-packbv-1-helper)))))

;gen the 1
(defthm getbit-of-packbv-1
  (implies (and (natp n)
                (integerp count)
                (< n count))
           (equal (getbit n (packbv count 1 bvs))
                  (getbit 0 (nth (+ count -1 (- n)) bvs))))
  :hints (("Goal" ;:induct (packbv-induct count n bvs)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable packbv nth zp))))

(defthm bvchop-of-packbv-helper
  (implies (and (<= n count)
                (natp n)
                (posp size)
                (natp count))
           (equal (bvchop (* n size) (packbv count size bvs))
                  (packbv n size (nthcdr (- count n) bvs))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (packbv posp nthcdr natp)
                           (bvcat-equal-rewrite-alt bvcat-equal-rewrite)))))

;gen to non multiples of size?
(defthm bvchop-of-packbv
  (implies (and (<= (floor k size) count)
                (equal 0 (mod k size))
                (natp k)
                (posp size)
                (natp count))
           (equal (bvchop k (packbv count size bvs))
                  (packbv (floor k size) size (nthcdr (- count (floor k size)) bvs))))
  :hints (("Goal" :use (:instance bvchop-of-packbv-helper (n (floor k size)))
           :in-theory (disable bvchop-of-packbv-helper))))

(defthm packbv-of-nil
  (equal (packbv itemcount itemsize nil)
         0)
  :hints (("Goal" :in-theory (enable packbv))))

(defthm logtail-of-packbv-gen2
  (implies (and (natp n)
                (equal len (len vals)))
           (equal (logtail (* 8 n) (packbv len 8 vals))
                  (packbv (- len n) 8 (butlast vals n))))
  :hints (("Goal" :induct (packbv len 8 vals)
           :in-theory (enable packbv bvchop-of-logtail-becomes-slice))))

(defthm logtail-8-of-packbv
  (implies (equal len (len vals))
           (equal (logtail 8 (packbv len 8 vals))
                  (packbv (- len 1) 8 (butlast vals 1))))
  :hints (("Goal" :use (:instance logtail-of-packbv-gen2 (n 1))
           :in-theory (disable logtail-of-packbv-gen2))))

(defthm logtail-of-packbv-simple
  (implies (and (equal len (len vals))
                (posp itemsize))
           (equal (logtail itemsize (packbv len itemsize vals))
                  (packbv (- len 1) itemsize (butlast vals 1))))
  :hints (("Goal" :induct (packbv len itemsize vals)
           :in-theory (enable packbv))))

(defthm packbv-of-1
  (equal (packbv 1 size items)
         (bvchop size (first items)))
  :hints (("Goal" :in-theory (enable packbv))))

;might not need this if the syntax functions knew the size of packbv
(defthm getbit-of-packbv-too-high
  (equal (getbit num (packbv num 1 items))
         0)
  :hints (("Goal" :in-theory (enable packbv))))

(defthm packbv-of-repeat-of-0
  (equal (packbv num 1 (repeat num 0))
         0)
  :hints (("Goal" :in-theory (enable packbv repeat))))

(defthm packbv-of-true-list-fix
  (equal (packbv count size (true-list-fix items))
         (packbv count size items))
  :hints (("Goal" :in-theory (enable packbv))))

;; This version splits off the least significant piece
(defthmd packbv-opener-alt
  (implies (and (not (zp itemcount))
                (posp itemsize)
                (equal itemcount (len items)))
           (equal (packbv itemcount itemsize items)
                  (bvcat (* itemsize (+ -1 itemcount))
                         (packbv (+ -1 itemcount) itemsize (butlast items 1))
                         itemsize
                         (nth (+ -1 itemcount) items))))
  :hints (("Goal" :in-theory (e/d (slice) (len BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))
