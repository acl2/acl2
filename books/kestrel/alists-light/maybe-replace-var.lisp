; A utility to replace a var using an alist
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Replace VAR with the item it is bound to in ALIST, if any.  Otherwise,
;; return VAR.  This may be faster than calling assoc-eq, checking whether
;; the result is nil, etc.
(defund maybe-replace-var (var alist)
  (declare (xargs :guard (and (symbolp var)
                              (symbol-alistp alist))))
  (if (endp alist)
      var ; no replacement, so return VAR
    (let ((entry (first alist)))
      (if (eq var (car entry))
          (cdr entry)
        (maybe-replace-var var (rest alist))))))
