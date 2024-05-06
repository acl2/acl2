; BV Library: Rules about bvequal
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvequal")
(include-book "bvplus")
(include-book "bvuminus")

;; todo: generalize some of these rules to allow the sizes to differ?

(defthm bvequal-of-bvplus-and-bvplus-cancel-1+-1+
  (equal (bvequal size (bvplus size x y) (bvplus size x z))
         (bvequal size y z))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-of-bvplus-arg2-cancel-1
  (equal (bvequal size x (bvplus size x y))
         (bvequal size 0 y))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-of-bvplus-arg1-cancel-1
  (equal (bvequal size (bvplus size x y) x)
         (bvequal size y 0))
  :hints (("Goal" :in-theory (enable bvequal))))

(defthm bvequal-of-constant-and-bvplus-of-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (integerp k1)
                (integerp k2))
           (equal (bvequal size k1 (bvplus size k2 x))
                  (bvequal size (- k1 k2) x)))
  :hints (("Goal" :in-theory (enable bvequal bvplus bvchop-of-sum-cases))))

(defthm bvequal-of-bvplus-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (integerp k1)
                (integerp k2))
           (equal (bvequal size (bvplus size k1 x) k2)
                  (bvequal size x (- k2 k1))))
  :hints (("Goal" :in-theory (enable bvequal bvplus bvchop-of-sum-cases))))

(defthm bvequal-of-constant-and-bvuminus
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (integerp k))
           (equal (bvequal size k (bvuminus size x))
                  (bvequal size (- k) x)))
  :hints (("Goal" :in-theory (enable bvequal bvplus bvuminus))))

(defthm bvequal-of-bvuminus-and-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (integerp k))
           (equal (bvequal size (bvuminus size x) k)
                  (bvequal size x (- k))))
  :hints (("Goal" :in-theory (enable bvequal bvplus bvuminus))))
