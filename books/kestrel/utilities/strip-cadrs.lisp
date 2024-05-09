; A lightweight book about the built-in-function strip-cadrs
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also ../alists-light/strip-cars.lisp.
;; See also ../alists-light/strip-cdrs.lisp.

(defthm len-of-strip-cadrs
  (equal (len (strip-cadrs x))
         (len x))
  :hints (("Goal" :in-theory (enable strip-cadrs))))
