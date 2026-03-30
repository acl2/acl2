; Adding a prefix to each member of a list of strings
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund add-prefix-to-strings (prefix strings)
  (declare (xargs :guard (and (stringp prefix)
                              (string-listp strings))))
  (if (endp strings)
      nil
    (cons (concatenate 'string prefix (first strings))
          (add-prefix-to-strings prefix (rest strings)))))

(defthm string-listp-of-add-prefix-to-strings
  (implies (and (stringp prefix)
                (string-listp strings))
           (string-listp (add-prefix-to-strings prefix strings)))
  :hints (("Goal" :in-theory (enable add-prefix-to-strings))))
