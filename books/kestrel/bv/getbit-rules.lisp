; Mixed theorems about getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "bitnot")
(local (include-book "slice-rules"))

(defthm getbit-of-minus
  (implies (and (integerp x)
                (natp n)
                )
           (equal (getbit n (- x))
                  (if (EQUAL (BVCHOP N X) 0)
                      (getbit n x)
                    (bitnot (getbit n x)))))
  :hints (("Goal" :in-theory (e/d (getbit bitnot)
                                  (BVCHOP-1-BECOMES-GETBIT
                                   SLICE-BECOMES-GETBIT
                                   ;BITNOT-OF-SLICE ;bozo
                                   ;BITXOR-OF-SLICE-ARG2 ;loops with defn getbit
                                   )))))
