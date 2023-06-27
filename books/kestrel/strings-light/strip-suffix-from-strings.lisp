; Strip a suffix from each of a list of strings, if it is present
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "strip-suffix-from-string")

(defund strip-suffix-from-strings (suffix strings)
  (declare (xargs :guard (and (stringp suffix)
                              (string-listp strings))))
  (if (endp strings)
      nil
    (cons (strip-suffix-from-string suffix (first strings))
          (strip-suffix-from-strings suffix (rest strings)))))
