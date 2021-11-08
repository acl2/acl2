; A utility to check whether a list is a permutation of another.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Checks whether the true-list X is a permutation of the true-list Y.
(defund perm (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (endp x)
      (endp y)
    (and (member-equal (first x) y)
         (perm (rest x) (remove1-equal (first x) y)))))
