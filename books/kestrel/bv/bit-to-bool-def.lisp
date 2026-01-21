; Converting a bit to a boolean
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider chopping X down to 1 bit.
(defund bit-to-bool (x)
  (declare (xargs :guard (unsigned-byte-p 1 x) ; or we could use bitp
                  :split-types t)
           (type bit x))
  (if (= x 0) nil t))
