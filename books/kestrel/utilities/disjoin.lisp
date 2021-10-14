; A book about the built-in function disjoin
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable disjoin))

(defthm disjoin-when-not-consp
  (implies (not (consp clause))
           (equal (disjoin clause)
                  *nil*))
  :hints (("Goal" :in-theory (enable disjoin))))
