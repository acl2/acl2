; Rules that recognize boolean constraints (alternative formulation)
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

;; See also ../sparse/gadgets/boolean-alt.lisp.  This book uses 1-b instead of
;; b-1 in the constraint.

(defthmd introduce-bitp-alt-1
  (implies (and (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul x (sub 1 x p) p))
                  (bitp x)))
  :hints (("Goal" :in-theory (disable sub))))

;; Instead of -1 here we might say (neg 1 p), but that seems like something we
;; want to simplfy.
(defthmd introduce-bitp-alt-2
  (implies (and (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul x (add 1 (neg x p) p) p))
                  (bitp x)))
  :hints (("Goal" :use introduce-bitp-alt-1
           :in-theory (enable sub))))

;; This version has the MUL commuted
(defthmd introduce-bitp-alt-1-alt
  (implies (and (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul (sub 1 x p) x p))
                  (bitp x)))
  :hints (("Goal" :in-theory (disable sub))))

;; This version has the MUL commuted
(defthmd introduce-bitp-alt-2-alt
  (implies (and (fep x p)
                (rtl::primep p))
           (equal (equal 0 (mul (add 1 (neg x p) p) x p))
                  (bitp x)))
  :hints (("Goal" :use introduce-bitp-alt-1
           :in-theory (enable sub))))
