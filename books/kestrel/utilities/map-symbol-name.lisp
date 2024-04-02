; A utility to apply symbol-name to every symbol in a list
;
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a list of strings
(defund map-symbol-name (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (cons (symbol-name (first syms))
          (map-symbol-name (rest syms)))))

(defthm string-listp-of-map-symbol-name
  (string-listp (map-symbol-name syms))
  :hints (("Goal" :in-theory (enable map-symbol-name))))
