; Base-2 integer logarithm (definition only)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns the floor of the base-2 logarithm of x, which must be a positive integer.
;; TODO: Rename lg to floor-of-lg ?
;; TODO: what should lg of 0 be?
(defund lg (x)
  (declare (xargs :guard (posp x)
                  :split-types t)
           (type integer x))
  (+ -1 (integer-length x)))
