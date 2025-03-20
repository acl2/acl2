; A function to divide a list into fixed-sized chunks
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "firstn-def")
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;only makes sense when (len x) is a multiple of n?
;; See also group2.
(defund group (n x)
  (declare (xargs :measure (+ 1 (len x))
                  :guard (and (true-listp x) ;would be nice for firstn's guard to not require true-listp
                              (posp n))))
  (if (or (not (mbt (posp n)))
          (atom x))
      nil
    (cons (firstn n x)
          (group n (nthcdr n x)))))
