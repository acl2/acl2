; Tests of defforall
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This can be local because the make-event expansion is saved in the certificate:
(local (include-book "defforall"))

(include-book "std/testing/must-be-redundant" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defforall-simple posp)

(must-be-redundant
  (defun all-posp (x)
    (if (atom x)
        t
      (and (posp (first x))
           (all-posp (rest x)))))
  ;; todo: add more here
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defforall all-consp (x) (consp x))

(must-be-redundant
  (defun all-consp (x)
    (if (atom x)
        t
      (and (consp (first x))
           (all-consp (rest x)))))
  ;; todo: add more here
  )
