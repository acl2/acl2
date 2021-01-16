; Rules that make use of nonzero constraints
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

;; See also ../sparse/gadgets/nonzero.lisp

(defthmd use-nonzero-constraint-1
  (implies (and (equal 1 (mul a a-inverse p))
                (fep a p)
                (rtl::primep p))
           (not (equal a 0))))

(defthmd use-nonzero-constraint-2
  (implies (and (equal 1 (mul a-inverse a p))
                (fep a p)
                (rtl::primep p))
           (not (equal a 0))))
