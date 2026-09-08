; A lightweight book about the built-in function arglistp1
;
; Copyright (C) 2024-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that arglistp1 could perhaps better be called legal-variable-listp.

(defthm arglistp1-forward-to-symbol-listp
   (implies (arglistp1 lst)
            (symbol-listp lst))
   :rule-classes :forward-chaining)

(defthm arglistp1-of-append
  (equal (arglistp1 (append x y))
         (and (arglistp1 (true-list-fix x))
              (arglistp1 y)))
  :hints (("Goal" :in-theory (enable append arglistp1))))

(defthm arglistp1-of-union-equal
  (equal (arglistp1 (union-equal x y))
         (and (arglistp1 (true-list-fix x))
              (arglistp1 y)))
  :hints (("Goal" :in-theory (enable union-equal arglistp1))))

(defthm arglistp1-of-intersection-equal-1
  (implies (arglistp1 x)
           (arglistp1 (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal arglistp1))))

(defthm arglistp1-of-intersection-equal-2
  (implies (arglistp1 y)
           (arglistp1 (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal arglistp1))))

(defthm arglistp1-of-set-difference-equal
  (implies (arglistp1 x)
           (arglistp1 (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal arglistp1))))

(defthm arglistp1-of-remove1-equal
  (implies (arglistp1 x)
           (arglistp1 (remove1-equal a x)))
  :hints (("Goal" :in-theory (enable remove1-equal arglistp1))))
