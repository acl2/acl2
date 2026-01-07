; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "byte-list")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; for compatibility with [books]/kestrel/zip/unzip.lisp
(defund byte-list-listp (vals)
  (declare (xargs :guard t))
  (if (atom vals)
      (null vals)
    (and (byte-listp (first vals))
         (byte-list-listp (rest vals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist byte-list-list
  :parents (fty::fty-extensions fty::specific-types byte byte-list)
  :short "Fixtype of lists of lists of bytes."
  :elt-type byte-list
  :true-listp t
  :elementp-of-nil t
  :pred byte-list-listp)
