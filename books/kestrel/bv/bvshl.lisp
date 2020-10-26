; Left shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(local (include-book "bvcat"))

;often we will let this open to bvcat
;we expect (<= shift-amount width)
;left shift within a fixed range
;see bvshl-rewrite-with-bvchop for a version that puts a bvchop around x to help us simplify stuff
(defund bvshl (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type (integer 0 *) width)
           (type integer x)
           (xargs :guard (<= shift-amount width)))
  (bvcat (- width shift-amount) x shift-amount 0))

(defthm bvshl-of-0-arg1
  (implies (natp amt)
           (equal (bvshl 0 x amt)
                  0))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-of-0-arg2
  (equal (bvshl width 0 amt)
         0)
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bvshl-of-0-arg3
  (equal (bvshl width x 0)
         (bvchop width x))
  :hints (("Goal" :in-theory (enable bvshl))))

;allow the widths to differ
(defthm bvshl-of-bvchop
  (implies (and (natp k)
                (natp width)
                (< k width) ;drop?
                )
           (equal (bvshl width (bvchop width x) k)
                  (bvshl width x k)))
  :hints (("Goal" :in-theory (enable bvshl))))

(defthm integerp-of-bvshl
  (integerp (bvshl width x shift-amount)))

(defthm natp-of-bvshl
  (natp (bvshl width x shift-amount))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bvshl))))


;bozo shouldn't need the hyp?
(defthm unsigned-byte-p-of-bvshl
  (implies (and (natp amt)
                (<= amt 32))
           (unsigned-byte-p 32 (bvshl 32 x amt)))
  :hints (("Goal" :in-theory (enable bvshl))))
