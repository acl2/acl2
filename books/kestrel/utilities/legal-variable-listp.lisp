; A recognizer for true lists of legal variable names
;
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Recognize a true list of legal variable names
(defund legal-variable-listp (names)
  (declare (xargs :guard t))
  (if (atom names)
      (null names)
    (and (legal-variablep (first names))
         (legal-variable-listp (rest names)))))

(defthmd symbol-listp-when-legal-variable-listp
  (implies (legal-variable-listp names)
           (symbol-listp names))
  :hints (("Goal" :in-theory (enable legal-variable-listp))))

(defthm legal-variable-listp-of-cons
  (equal (legal-variable-listp (cons name names))
         (and (legal-variablep name)
              (legal-variable-listp names)))
  :hints (("Goal" :in-theory (enable legal-variable-listp))))

(defthm legal-variable-listp-of-true-list-fix
  (implies (legal-variable-listp names)
           (legal-variable-listp (true-list-fix names)))
  :hints (("Goal" :in-theory (enable legal-variable-listp))))
