; Rules about bit-listp and other non-built-in functions
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bit-listp")
(include-book "kestrel/lists-light/memberp" :dir :system)

(defthm bitp-when-bit-listp-and-memberp
  (implies (and (bit-listp free)
                (memberp x free))
           (bitp x)))

;; (defun gen-bit-listp-assumption (vars)
;;   (declare (xargs :guard (and (symbol-listp vars)
;;                               (consp vars))))
;;   `(bit-listp ,(make-append-with-key-nest vars)))
