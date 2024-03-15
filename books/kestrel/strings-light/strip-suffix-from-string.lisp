; Strip a suffix from a string, if it is present
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-ends-withp")

(local (in-theory (disable length)))

(defund strip-suffix-from-string (suffix string)
  (declare (xargs :guard (and (stringp suffix)
                              (stringp string))))
  (if (string-ends-withp string suffix)
      (subseq string 0 (- (length string) (length suffix)))
    string))

(defthm stringp-of-strip-suffix-from-string
  (implies (stringp string)
           (stringp (strip-suffix-from-string suffix string)))
  :hints (("Goal" :in-theory (enable strip-suffix-from-string))))
