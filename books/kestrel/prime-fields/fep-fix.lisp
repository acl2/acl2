; Prime fields library: field-element fixing predicate
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep")
(local (include-book "../arithmetic-light/mod"))

;; Coerce X to satisfy (fep x p).
;; TODO: Disable?
(defun fep-fix (x p)
  (mod (ifix x) p))

(defthm fep-of-fep-fix
  (implies (posp p)
           (fep (fep-fix x p) p))
  :hints (("Goal" :in-theory (enable fep-fix))))

(defthm fep-fix-when-fep
  (implies (fep x p)
           (equal (fep-fix x p)
                  x))
  :hints (("Goal" :in-theory (enable fep-fix fep))))
