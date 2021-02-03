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
