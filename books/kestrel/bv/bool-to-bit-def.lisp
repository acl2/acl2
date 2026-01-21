; Converting a boolean to a bit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Converts a boolean (t or nil) to a bit (1 or 0).
;; The guard requires the argument to be boolean, but this does handle
;; generalized booleans naturally, treating anything other than nil as "true".
(defund bool-to-bit (test)
  (declare (xargs :guard (booleanp test)
                  :type-prescription (bitp (bool-to-bit test))))
  (if test 1 0))
