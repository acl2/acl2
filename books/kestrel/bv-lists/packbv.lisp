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

;; See packbv-def.lisp for the definition of packbv.

(include-book "packbv-def")
;(include-book "all-unsigned-byte-p")
;(include-book "../bv/bvcat-def")
(include-book "../bv/getbit")
(include-book "../lists-light/repeat")
(local (include-book "../bv/bvcat"))
(local (include-book "../bv/unsigned-byte-p"))
(local (include-book "../lists-light/butlast"))
(local (include-book "../lists-light/nthcdr"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../../meta/meta-plus-lessp"))

;(local (in-theory (disable mod-x-y-=-x+y-for-rationals))) ;bad

(local
 (defthm <-cancel-hack
   (implies (and (posp size)
                 (rationalp count)
                 (rationalp n))
            (equal (< (+ (- size) (* count size)) (* n size))
                   (< (+ -1 count) n)))
   :hints (("Goal" :use (:instance <-of-*-and-*-cancel (y size) (x1 (+ -1 count)) (x2 n))))))

(defthmd packbv-base
  (implies (zp itemcount)
           (equal (packbv itemcount itemsize items)
                  0))
  :hints (("Goal" :in-theory (enable packbv))))

;; Splits off the first item, which becomes the most significant part of the result
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
  :hints (("Goal" :use unsigned-byte-p-of-packbv
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
  :hints (("Goal" :use bvchop-of-packbv-1-helper
           :in-theory (e/d (packbv-base) (bvchop-of-packbv-1-helper)))))

;gen the 1
(defthm getbit-of-packbv-1
  (implies (and (natp n)
                (integerp count)
                (< n count))
           (equal (getbit n (packbv count 1 bvs))
                  (getbit 0 (nth (+ count -1 (- n)) bvs))))
  :hints (("Goal" ;:induct (packbv-induct count n bvs)
           :in-theory (e/d (packbv nth zp GETBIT-TOO-HIGH)
                           (;BVCAT-OF-IF-ARG2
                            )))))

(defthm bvchop-of-packbv-helper
  (implies (and (<= n count)
                (natp n)
                (posp size)
                (natp count))
           (equal (bvchop (* n size) (packbv count size bvs))
                  (packbv n size (nthcdr (- count n) bvs))))
  :hints (("Goal"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this version throws away the unneeded items with take
;; may not match very nicely because of the * in the LHS
(defthm logtail-of-packbv-with-take
  (implies (and (natp n)
                (natp itemsize))
           (equal (logtail (* itemsize n) (packbv itemcount itemsize items))
                  (packbv (- itemcount n) itemsize (take (- itemcount n) items))))
  :hints (("Goal" :in-theory (enable packbv zp))))

;drop this version?
;; this version throws away the unneeded items with butlast
;; may not match very nicely because of the * in the LHS
(defthm logtail-of-packbv
  (implies (and (equal itemcount (len items)) ; (natp itemcount)
                (natp n)
                (natp itemsize))
           (equal (logtail (* itemsize n) (packbv itemcount itemsize items))
                  (packbv (- itemcount n) itemsize (butlast items n))))
  :hints (("Goal" :in-theory (enable packbv
                               bvchop-of-logtail-becomes-slice))))

;; this version doesn't throw away the unneeded items
;; may not match very nicely because of the * in the LHS
(defthmd logtail-of-packbv-no-discard
  (implies (and (natp n)
                (natp itemsize))
           (equal (logtail (* itemsize n) (packbv itemcount itemsize items))
                  (packbv (- itemcount n) itemsize items)))
  :hints (("Goal" :in-theory (e/d (packbv bvchop-of-logtail-becomes-slice zp)
                                  (logtail-of-packbv-with-take)))))

;drop this version or adapt to use take?
;; special case for n-1; throws away the first item
(defthm logtail-of-packbv-special
  (implies (and (equal itemcount (len items))
                (natp itemsize))
           (equal (logtail itemsize (packbv itemcount itemsize items))
                  (packbv (- itemcount 1) itemsize (butlast items 1))))
  :hints (("Goal" :use (:instance logtail-of-packbv (n 1))
           :in-theory (disable logtail-of-packbv))))

;; uses take to discard values
;;special case for itemsize=1
(defthm logtail-of-packbv-with-take-size-1
  (implies (and (natp itemcount)
                (natp n))
           (equal (logtail n (packbv itemcount 1 items))
                  (packbv (- itemcount n) 1 (take (- itemcount n) items))))
  :hints (("Goal" :use (:instance logtail-of-packbv-with-take
                                  (itemsize 1))
           :in-theory (disable logtail-of-packbv-with-take))))

(local
  (defthm +-of---and-*-of-2-same
    (implies (acl2-numberp x)
             (equal (+ (- x) (* 2 x))
                    x))))

;; no need to do discard items at the end
(defthmd logtail-of-packbv-new-no-discard-special
  (implies (posp itemsize)
           (equal (logtail itemsize (packbv itemcount itemsize items))
                  (packbv (- itemcount 1) itemsize items)))
  :hints (("Goal" :use (:instance logtail-of-packbv-no-discard (n 1))
           :in-theory (disable logtail-of-packbv-no-discard))))

(defthm packbv-of-1
  (equal (packbv 1 size items)
         (bvchop size (first items)))
  :hints (("Goal" :in-theory (enable packbv))))

;might not need this if the syntax functions knew the size of packbv
(defthm getbit-of-packbv-too-high
  (equal (getbit num (packbv num 1 items))
         0)
  :hints (("Goal" :in-theory (e/d (packbv) (;bvcat-of-if-arg2
                                            )))))

(defthm packbv-of-repeat-of-0
  (equal (packbv num 1 (repeat num 0))
         0)
  :hints (("Goal" :in-theory (enable packbv repeat))))

(defthm packbv-of-true-list-fix
  (equal (packbv count size (true-list-fix items))
         (packbv count size items))
  :hints (("Goal" :in-theory (enable packbv))))

;; This version splits off the last item, which becomes the least significant part
;; of the result.
;; todo: make a version that uses take?
(defthmd packbv-opener-alt
  (implies (and (not (zp itemcount))
                (posp itemsize)
                (equal itemcount (len items)) ; but see just below
                )
           (equal (packbv itemcount itemsize items)
                  (bvcat (* itemsize (+ -1 itemcount))
                         (packbv (+ -1 itemcount) itemsize (butlast items 1))
                         itemsize
                         (nth (+ -1 itemcount) items))))
  :hints (("Goal" :in-theory (e/d (slice) (len BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;; This one splits off the last item, which becomes the least significant part
;; of the result.
(defthmd packbv-opener-alt-no-discard
  (implies (and (not (zp itemcount))
                (posp itemsize)
                ;; (equal itemcount (len items))
                )
           (equal (packbv itemcount itemsize items)
                  (bvcat (* itemsize (+ -1 itemcount))
                         (packbv (+ -1 itemcount) itemsize items)
                         itemsize
                         (nth (+ -1 itemcount) items))))
  :hints (("Goal" :in-theory (e/d (slice logtail-of-packbv-new-no-discard-special)
                                  (len bvchop-of-logtail-becomes-slice)))))

(defthm packbv-of-1-linear
  (implies (natp i)
           (<= (packbv i 1 items)
               (+ -1 (expt 2 i))))
  :rule-classes :linear
  :hints (("Goal" :expand (packbv i 1 items)
           :in-theory (disable bvchop-of-packbv
                               bvchop-of-packbv-1
                               bvchop-of-packbv-1-helper
                               expt
                               bvcat-of-0-arg2))))
