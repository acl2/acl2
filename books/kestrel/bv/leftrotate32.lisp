; BV Library: leftrotate for size 32
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "leftrotate")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "bvcat"))

(local (in-theory (disable unsigned-byte-p)))

(defund leftrotate32 (amt val)
  (declare (type integer amt val))
  (leftrotate 32 amt val))

(defthm leftrotate32-of-0-arg1
  (equal (leftrotate32 0 val)
         (bvchop 32 val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm leftrotate32-of-0-arg2
  (equal (leftrotate32 amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate32))))

;todo gen the 5
(defthm leftrotate32-of-bvchop-5
  (implies (natp amt)
           (equal (leftrotate32 (bvchop 5 amt) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :expand ((:with bvchop (BVCHOP 5 Amt)))
           :in-theory (enable leftrotate32 leftrotate))))

;justifies the correctness of some operations performed by Axe
(defthm unsigned-byte-p-32-of-leftrotate32
  (unsigned-byte-p 32 (leftrotate32 x y))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm unsigned-byte-p-of-leftrotate32
  (implies (and (<= 32 size)
                (integerp size))
           (unsigned-byte-p size (leftrotate32 x y)))
  :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))

;or should leftrotate32 be among the functions we can take the size of?
(defthm bvchop-of-leftrotate32-does-nothing
  (implies (and (<= 32 size)
                (integerp size))
           (equal (bvchop size (leftrotate32 x y))
                  (leftrotate32 x y))))

(defthm leftrotate32-of-bvchop-arg2
  (implies (and (<= 32 size)
                (integerp size))
           (equal (leftrotate32 amt (bvchop size x))
                  (leftrotate32 amt x)))
  :hints (("Goal" :in-theory (enable leftrotate32 leftrotate))))

(defthm leftrotate32-of-bvchop-helper
  (implies (natp amt)
           (equal (leftrotate32 (bvchop 5 amt) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :expand (:with bvchop (BVCHOP 5 Amt))
           :in-theory (enable leftrotate32 leftrotate))))

(defthm leftrotate32-of-bvchop
  (implies (natp amt)
           (equal (leftrotate32 (bvchop 32 amt) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :in-theory (disable leftrotate32 leftrotate32-of-bvchop-helper)
           :use ((:instance leftrotate32-of-bvchop-helper (amt amt))
                 (:instance leftrotate32-of-bvchop-helper (amt (bvchop 32 amt)))))))

;do not remove.  this helps justify how Axe translates leftrotate32 to STP:
(defthm leftrotate32-of-mod
  (implies (natp amt)
           (equal (leftrotate32 (mod amt 32) val)
                  (leftrotate32 amt val)))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthmd leftrotate-becomes-leftrotate32
  (equal (leftrotate 32 amt val)
         (leftrotate32 amt val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(theory-invariant (incompatible (:rewrite leftrotate-becomes-leftrotate32) (:definition leftrotate32)))

;gen
(defthm leftrotate-32-of-bvchop-5
  (implies (natp amt)
           (equal (leftrotate 32 (bvchop 5 amt) val)
                  (leftrotate 32 (ifix amt) val)))
  :hints (("Goal" :in-theory (enable bvchop))))
