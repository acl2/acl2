; A utility to apply symbol-name to every symbol in a list
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun map-symbol-name (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (cons (symbol-name (first syms))
          (map-symbol-name (rest syms)))))
