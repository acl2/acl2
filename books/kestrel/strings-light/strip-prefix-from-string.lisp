; Removing a prefix from the start of a string
;
; Copyright (C) 2022-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-starts-withp")
(include-book "strnthcdr")
(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/lists-light/prefixp" :dir :system))

(defund strip-prefix-from-string (prefix string)
  (declare (xargs :guard (and (stringp prefix)
                              (stringp string))))
  (if (string-starts-withp string prefix)
      (strnthcdr (length prefix) string)
    (prog2$ (er hard? 'strip-prefix-from-string "String ~x0 does not start with ~x1." string prefix)
            ;; just returns some string, to support the return type theorem:
            "")))

(defthm stringp-of-strip-prefix-from-string
  (implies (stringp string)
           (stringp (strip-prefix-from-string prefix string)))
    :hints (("Goal" :in-theory (enable strip-prefix-from-string))))

(defthm length-of-strip-prefix-from-string
  (implies (and (string-starts-withp string prefix)
                (stringp prefix) ; drop?
                (stringp string))
           (equal (length (strip-prefix-from-string prefix string))
                  (- (length string) (length prefix))))
  :hints (("Goal" :in-theory (enable strip-prefix-from-string
                                     string-starts-withp
                                     length))))
