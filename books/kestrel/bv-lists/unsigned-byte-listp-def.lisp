; A book that cherry-picks the definition of unsigned-byte-listp
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Unlike all-unsigned-byte-p, this one implies true-listp.
;; Also in std/typed-lists/unsigned-byte-listp.lisp.
(defund unsigned-byte-listp (n x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (unsigned-byte-p n (car x))
         (unsigned-byte-listp n (cdr x)))))
