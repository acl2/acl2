; Generating names for the "becomes theorem"
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/pack" :dir :system)
(include-book "function-renamingp")

;; Generate the name of the "becomes" theorem that replaces OLD-FN with NEW-FN.
(defun becomes-theorem-name (old-fn new-fn)
  (declare (xargs :guard (and (symbolp old-fn)
                              (symbolp new-fn))))
  (pack$ old-fn '-becomes- new-fn))

;; The names of the "becomes theorems" for each of the functions in FUNCTION-RENAMING.
(defun becomes-theorem-names (function-renaming)
  (declare (xargs :guard (function-renamingp function-renaming)))
  (if (endp function-renaming)
      nil
    (let* ((pair (first function-renaming))
           (old-fn (car pair))
           (new-fn (cdr pair)))
      (cons (becomes-theorem-name old-fn new-fn)
            (becomes-theorem-names (rest function-renaming))))))
