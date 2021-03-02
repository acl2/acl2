; Call BVPLUS on corresponding elements of two lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvplus" :dir :system)

(defun bvplus-list (n items1 items2)
  (declare (xargs :guard (and (natp n)
                              (true-listp items1)
                              (true-listp items2))))
  (if (endp items1)
      nil
    (cons (bvplus n (car items1) (car items2))
          (bvplus-list n (cdr items1) (cdr items2)))))
