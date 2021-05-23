; A book that cherry-picks the definition of unsigned-byte-listp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;unlike all-unsigned-byte-p, this one implies true-listp.
;also in std/typed-lists/unsigned-byte-listp.lisp
(defund unsigned-byte-listp (n x)
;  (declare (type t n x))
  (if (atom x)
      (null x)
      (and (unsigned-byte-p n (car x))
           (unsigned-byte-listp n (cdr x)))))

(verify-guards unsigned-byte-listp)
