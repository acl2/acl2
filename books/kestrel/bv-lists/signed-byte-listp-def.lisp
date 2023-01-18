; A book that cherry-picks the definition of signed-byte-listp
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Unlike all-signed-byte-p, this one implies true-listp.
;; Also in std/typed-lists/signed-byte-listp.lisp.
(defund signed-byte-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
      (and (signed-byte-p n (car x))
           (signed-byte-listp n (cdr x)))))
