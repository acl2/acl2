; BV Library: leftrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "slice-def")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "bvcat"))

(local (in-theory (disable expt)))

;; Rotate VAL to the left by AMT positions within a field of width WIDTH.  We
;; reduce the rotation amount modulo the width.
(defund leftrotate (width amt val)
  (declare (type integer val amt)
           (type (integer 0 *) width))
  (if (= 0 width)
      0
    (let* ((amt (mod (nfix amt) width)))
      (bvcat (- width amt)
             (slice (+ -1 width (- amt)) 0 val)
             amt
             (slice (+ -1 width) (+ width (- amt)) val)))))

(defthm unsigned-byte-p-of-leftrotate
  (implies (natp size)
           (unsigned-byte-p size (leftrotate size x y)))
  :hints (("Goal" :in-theory (enable leftrotate natp))))

(defund leftrotate16 (amt val)
  (declare (type integer amt val))
  (leftrotate 16 amt val))

(defund leftrotate32 (amt val)
  (declare (type integer amt val))
  (leftrotate 32 amt val))

(defund leftrotate64 (amt val)
  (declare (type integer amt val))
  (leftrotate 64 amt val))

(defthm leftrotate-of-0-arg2
  (equal (leftrotate width 0 val)
         (bvchop width val))
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate32-of-0-arg1
  (equal (leftrotate32 0 val)
         (bvchop 32 val))
  :hints (("Goal" :in-theory (enable leftrotate32))))

(defthm leftrotate-of-0-arg3
  (equal (leftrotate width amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate))))

(defthm leftrotate32-of-0-arg2
  (equal (leftrotate32 amt 0)
         0)
  :hints (("Goal" :in-theory (enable leftrotate32))))

;gen!
(defthm leftrotate-of-plus
  (IMPLIES (natp AMT) ;was integerp
           (EQUAL (LEFTROTATE 32 (+ 32 AMT) VAL)
                  (LEFTROTATE 32 AMT VAL)))
  :hints (("Goal" :in-theory (enable LEFTROTATE))))

;fixme gen the 5
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

(defthm leftrotate-of-mod-same
  (implies (and (natp width)
                (natp amt))
           (equal (leftrotate width (mod amt width) val)
                  (leftrotate width (nfix amt) val)))
  :hints (("Goal" :in-theory (enable leftrotate))))

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

(defthmd leftrotate-becomes-leftrotate64
  (equal (leftrotate 64 amt val)
         (leftrotate64 amt val))
  :hints (("Goal" :in-theory (enable leftrotate64))))

(theory-invariant (incompatible (:rewrite leftrotate-becomes-leftrotate64) (:definition leftrotate64)))

(defthm leftrotate-of-leftrotate
  (implies (and (natp width)
                (natp amt1)
                (natp amt2))
           (equal (leftrotate width amt1 (leftrotate width amt2 val))
                  (leftrotate width (+ amt1 amt2) val)))
  :hints (("Goal" :in-theory (enable leftrotate mod-sum-cases))))

;gen
(defthm leftrotate-32-of-bvchop-5
  (implies (natp amt)
           (equal (leftrotate 32 (bvchop 5 amt) val)
                  (leftrotate 32 (ifix amt) val)))
  :hints (("Goal" :in-theory (enable bvchop))))
