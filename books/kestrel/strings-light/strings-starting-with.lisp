; Keeping strings that start with a prefix
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-starts-withp")

;; Filter the STRINGS, keeping only those that start with PREFIX
(defun strings-starting-with (prefix strings)
  (declare (xargs :guard (and (string-listp strings)
                              (stringp prefix))))
  (if (endp strings)
      nil
    (let ((string (first strings)))
      (if (string-starts-withp string prefix)
          (cons string
                (strings-starting-with prefix (rest strings)))
        (strings-starting-with prefix (rest strings))))))
