; An assistant to help find simple proofs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Similar to flatten but simpler and with a stronger guard
(defun append-all (xs)
  (declare (xargs :guard (true-list-listp xs)))
  (if (endp xs)
      nil
    (append (first xs) (append-all (rest xs)))))
