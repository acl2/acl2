; A book about boolxor (boolean-valued xor)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "bool-fix")

;TODO: compare to the built-in function xor!
(defund boolxor (x y)
  (if x
      (if y nil t)
    (if y t nil)))

(defthm booleanp-of-boolxor
  (booleanp (boolxor x y)))

(defthm boolxor-associative
  (equal (boolxor (boolxor x y) z)
         (boolxor x (boolxor y z)))
  :hints (("Goal" :in-theory (enable boolxor))))

(defthm boolxor-commutative
  (equal (boolxor x y)
         (boolxor y x))
  :hints (("Goal" :in-theory (enable boolxor))))

(defthm boolxor-commutative-2
  (equal (boolxor x (boolxor y z))
         (boolxor y (boolxor x z)))
  :hints (("Goal" :in-theory (enable boolxor))))

(defthm boolxor-same-1
  (equal (boolxor x x)
         nil)
  :hints (("Goal" :in-theory (enable boolxor))))

(defthm boolxor-same-2
  (equal (boolxor x (boolxor x y))
         (bool-fix y))
  :hints (("Goal" :in-theory (enable boolxor))))

(defthm boolxor-of-bool-fix-arg1
  (equal (boolxor (bool-fix x) y)
         (boolxor x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline boolxor))))

(defthm boolxor-of-bool-fix-arg2
  (equal (boolxor x (bool-fix y))
         (boolxor x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline boolxor))))
