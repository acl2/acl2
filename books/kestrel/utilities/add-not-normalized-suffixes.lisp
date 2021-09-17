; Making 'not-normalized' names
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Add $NOT-NORMALIZED to each of the SYMS
(defun add-not-normalized-suffixes (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (cons (add-suffix (first syms) "$NOT-NORMALIZED")
          (add-not-normalized-suffixes (rest syms)))))
