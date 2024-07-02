; Adding prefixes to symbols
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Similar to the built-in function add-suffix.
(defun add-prefix (prefix sym)
  (declare (xargs :guard (and (stringp prefix)
                              (symbolp sym))))
  (intern-in-package-of-symbol (concatenate 'string prefix (symbol-name sym))
                               sym))

;; Similar to the built-in function add-suffix-to-fn.
;; Avoids using the COMMON-LISP package since we can't define new functions in that package.
(defun add-prefix-to-fn (prefix sym)
  (declare (xargs :guard (and (stringp prefix)
                              (symbolp sym))))
  (if (equal (symbol-package-name sym)
             *main-lisp-package-name*)
      (intern (concatenate 'string prefix (symbol-name sym))
              "ACL2")
    (add-prefix prefix sym)))
