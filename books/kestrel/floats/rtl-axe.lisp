; Axe versions of rules in rtl.lisp
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rtl")

;; The main rule has a free var in the RHS
(defthm iencode-becomes-encode-bv-float-axe
  (implies (and (rtl::formatp f)
                (not (rtl::explicitp f)) ; we only handle implicit formats
                (bitp sgn))
           (equal (rtl::iencode sgn f)
                  (encode-bv-float (format-k f) (format-p f)
                                   (if (equal 0 sgn) *float-positive-infinity* *float-negative-infinity*)
                                   :fake ; avoids a var here
                                   )))
  :hints (("Goal" :use (:instance iencode-becomes-encode-bv-float (oracle :fake))
           :in-theory (disable iencode-becomes-encode-bv-float))))

;move?
(defthm integerp-of-encode-bv-float (integerp (encode-bv-float k p datum oracle)))
