; Tests for check-equivs
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-equivs")

(local
 (defconst *equiv-alist-for-built-ins*
   (acons 'iff
          (acons 'iff '(iff iff)
                 (acons 'not '(iff)
                        (acons 'implies '(iff iff)
                               nil)))
          (acons 'equal
                 (acons 'iff '(iff iff)
                        (acons 'not '(iff)
                               (acons 'implies '(iff iff)
                                      nil)))
                 nil))))

(local (check-equiv-alist *equiv-alist-for-built-ins*))
