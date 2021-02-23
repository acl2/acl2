; Lists of field elements
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)

;; Recognize a true list of field elements.
(defun fe-listp (elems prime)
  (declare (xargs :guard (rtl::primep prime)))
  (if (atom elems)
      (equal elems nil)
    (and (fep (first elems) prime)
         (fe-listp (rest elems) prime))))
