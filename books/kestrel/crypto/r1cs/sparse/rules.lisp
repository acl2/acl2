; Rules about R1CSes
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "r1cs")
(include-book "kestrel/utilities/defopeners" :dir :system)

(acl2::defopeners dot-product)

;(acl2::defopeners R1CS-CONSTRAINTS-HOLDP) ;does not generate what I want

(defthm r1cs-constraints-holdp-opener
  (implies (not (endp constraints))
           (equal (r1cs-constraints-holdp constraints valuation prime)
                  (and (r1cs-constraint-holdsp (first constraints)
                                               valuation prime)
                       (r1cs-constraints-holdp (rest constraints)
                                               valuation prime)))))

(defthm r1cs-constraints-holdp-base
  (r1cs-constraints-holdp nil valuation prime))
