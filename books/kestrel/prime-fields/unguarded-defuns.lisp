; Function variants with guards of T
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "prime-fields")
(include-book "kestrel/axe/unguarded-primitives" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; These functions, each of whose guard is T, are used by the Axe evaluator.

(defund add-unguarded (x y p)
  (declare (xargs :guard t))
  (mod (+ (ifix x) (ifix y)) (pos-fix p)))

(defthm add-unguarded-correct
  (equal (add-unguarded x y p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add add-unguarded))))

(defun fep-unguarded (x p)
  (declare (xargs :guard t))
  (and (natp x)
       (acl2::<-unguarded x p)))

(defthm fep-unguarded-correct
  (equal (fep-unguarded x p)
         (fep x p))
  :hints (("Goal" :in-theory (enable fep fep-unguarded))))

(defund neg-unguarded (x p)
  (declare (xargs :guard t))
  (mod (- (ifix x)) (pos-fix p)))

(defthm neg-unguarded-correct
  (equal (neg-unguarded x p)
         (neg x p))
  :hints (("Goal" :in-theory (enable neg neg-unguarded))))

(defund mul-unguarded (x y p)
  (declare (xargs :guard t))
  (let ((p (pos-fix p)))
    (mul (mod (ifix x) p)
         (mod (ifix y) p)
         p)))

(defthm mul-unguarded-correct
  (equal (mul-unguarded x y p)
         (mul x y p))
  :hints (("Goal" :in-theory (enable mul mul-unguarded))))

(defthm mul-of-0-arg3
  (equal (mul x y 0)
         0)
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-of-1-arg3
  (equal (mul x y 1)
         0)
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-small-arg3
  (implies (<= p 1)
           (equal (mul x y p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defthm mul-when-not-natp-arg3
  (implies (not (natp p))
           (equal (mul x y p)
                  0))
  :hints (("Goal" :in-theory (enable mul))))

(defund pow-unguarded (x n p)
  (declare (xargs :guard t :guard-debug t))
  (if (not (posp n))
      1
    (if (<= (ifix p) 1)
        0
      (mod-expt-fast (ifix x) (nfix n) (ifix p)))))

(defthm pow-when-not-rationalp-arg3
  (implies (and (not (rationalp p))
                (posp n))
           (equal (pow x n p)
                  0))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-when-small-arg3
  (implies (and (<= p 1)
                (posp n))
           (equal (pow x n p)
                  0))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-1-arg3
  (equal (pow x n 1)
         (if (posp n)
             0
           1))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-0-arg3
  (implies (posp n)
           (equal (pow x n 0)
                  0))
  :hints (("Goal" :in-theory (enable pow expt))))

(defthm pow-unguarded-correct
  (equal (pow-unguarded x n p)
         (pow x n p))
  :hints (("Goal" :in-theory (enable pow pow-unguarded
                                     pow-rewrite))))

(defund minus1-unguarded (p)
  (declare (xargs :guard t))
  (+ -1 (fix p)))

(defthm minus1-unguarded-correct
  (equal (minus1-unguarded p)
         (minus1 p))
  :hints (("Goal" :in-theory (enable minus1
                                     minus1-unguarded))))

(defun inv-unguarded (x p)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (pow-unguarded x (+ -1 (minus1-unguarded p)) p))

(defthm inv-unguarded-correct
  (equal (inv-unguarded x p)
         (inv x p))
  :hints (("Goal" :in-theory (enable inv
                                     inv-unguarded))))

(defun div-unguarded (x y p)
  (declare (xargs :guard t))
  (mul-unguarded x (inv-unguarded y p) p))

(defthm div-unguarded-correct
  (equal (div-unguarded x y p)
         (div x y p))
  :hints (("Goal" :in-theory (enable div div-unguarded))))
