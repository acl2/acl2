; Rules that recognize selection constraints
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

;; See also ../sparse/gadgets/selection.lisp

(defthmd introduce-selection-1
  (implies (and (fep z p)
                (fep y p)
                (fep x p)
                (bitp b)
                (rtl::primep p))
           (equal (equal (mul b (add y (neg x p) p) p)
                         (add y (neg z p) p))
                  (equal z (if (equal 1 b) x y)))))

(defthmd introduce-selection-2
  (implies (and (fep z p)
                (fep y p)
                (fep x p)
                (bitp b)
                (rtl::primep p))
           (equal (equal (mul b (add (neg x p) y p) p)
                         (add y (neg z p) p))
                  (equal z (if (equal 1 b) x y)))))

(defthmd introduce-selection-3
  (implies (and (fep z p)
                (fep y p)
                (fep x p)
                (bitp b)
                (rtl::primep p))
           (equal (equal (mul b (add y (neg x p) p) p)
                         (add (neg z p) y p))
                  (equal z (if (equal 1 b) x y)))))

(defthmd introduce-selection-4
  (implies (and (fep z p)
                (fep y p)
                (fep x p)
                (bitp b)
                (rtl::primep p))
           (equal (equal (mul b (add (neg x p) y p) p)
                         (add (neg z p) y p))
                  (equal z (if (equal 1 b) x y)))))
