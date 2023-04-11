; Removing a prefix from the start of a string
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-starts-withp")
(include-book "strnthcdr")

(defund strip-prefix-from-string (prefix string)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp string))))
  (if (string-starts-withp string prefix)
      (strnthcdr (length prefix) string)
    (er hard? 'strip-prefix-from-string "String ~x0 does not start with ~x1." string prefix)))
