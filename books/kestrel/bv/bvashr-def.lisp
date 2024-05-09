; Cherry-pick the definitions of the BV functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvshr-def")
(include-book "bvsx-def")

;; NOTE: Currently, the shift amount must be less than the width.
;perhaps this should be called xshr (for sign-extending shift), but jvm has a function or macro with that name already (get rid of it first!)
;; TODO: it might be more elegant to change the behavior with large shift amounts to avoid alsways getting 0; consider: (bvashr 32 -1 32).
(defund bvashr (width x shift-amount)
  (declare (xargs :guard (and (integerp width)
                              (integerp x)
                              (natp shift-amount)
                              (< shift-amount width))  ;what happens if they're equal?
                  :split-types t)
           (type (integer 0 *) width shift-amount)
           (type integer x))
  (bvsx width
        (- width shift-amount)
        (bvshr width x shift-amount)))
