; BV Library: bvequal
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-def")
(local (include-book "bvchop"))

;; Unlike equal, this makes clear that its operands are BVs (of the given type).
;; So this is better for the induced-type machinery in Axe.
(defund bvequal (size x y)
  (declare (xargs :guard (and (natp size)
                              (integerp x)
                              (integerp y))))
  (equal (bvchop size x) (bvchop size y)))

(defthm bvequal-of-bvchop-arg2
  (equal (bvequal size (bvchop size x) y)
         (bvequal size x y))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-of-bvchop-arg3
  (equal (bvequal size x (bvchop size y))
         (bvequal size x y))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthmd equal-becomes-bvequal-1
  (implies (and (unsigned-byte-p size x) ; size is a free var
                (unsigned-byte-p size y))
           (equal (equal x y)
                  (bvequal size x y)))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthmd equal-becomes-bvequal-2
  (implies (and (unsigned-byte-p size y) ; size is a free var
                (unsigned-byte-p size x))
           (equal (equal x y)
                  (bvequal size x y)))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-same
  (bvequal size x x)
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-of-0-arg1
  (bvequal 0 x y)
  :hints (("Goal" :in-theory (enable bvequal))))
