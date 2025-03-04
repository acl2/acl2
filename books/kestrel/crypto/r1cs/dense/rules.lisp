; Rules about the R1CS formalization
;
; Copyright (C) 2019-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "r1cs")
(include-book "kestrel/utilities/defopeners" :dir :system)

;(acl2::defopeners constraints-have-lengthp)

(in-theory (enable make-constraint-vector))

(acl2::defopeners dot-product)

;(acl2::defopeners r1cs-constraints-holdp)
