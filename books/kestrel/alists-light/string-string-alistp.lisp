; A lightweight book about alists whose keys and values are all strings
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; From including std/typed-alists/string-string-alistp.lisp
(defund string-string-alistp (x)
  (declare (xargs :guard t
                  :normalize nil))
  (if (consp x)
      (and (consp (car x))
           (stringp (caar x))
           (stringp (cdar x))
           (string-string-alistp (cdr x)))
    (null x)))

(defthm string-string-alistp-forward-to-alistp
  (implies (string-string-alistp x)
           (alistp x))
  :hints (("Goal" :in-theory (enable string-string-alistp))))
