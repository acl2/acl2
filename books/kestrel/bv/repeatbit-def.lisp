; The definition of repeatbit (for creating BVs of all ones or all zeros)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See theorems in repeatbit.lisp and repeatbit2.lisp

(include-book "bvchop-def")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system)) ; for the :type-prescription

;we expect bit to be 0 or 1
(defund repeatbit (n bit)
  (declare (xargs :guard (and (natp n)
                              (bitp bit))
                  :split-types t
                  :type-prescription (natp (repeatbit n bit))
                  )
           (type (integer 0 *) n)
           (type (integer 0 1) bit))
  (if (not (natp n))
      0
    ;; chop BIT down to 1 bit if needed:
    (let ((bit (mbe :logic (bvchop 1 bit)
                    :exec bit)))
      (if (= 0 bit)
          0
        (+ -1 (expt 2 n))))))
