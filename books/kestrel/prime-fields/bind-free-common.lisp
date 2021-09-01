; Prime fields library: Utilities for bind-free rules
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/utilities/forms" :dir :system)

;; Extract the addends of TERM, where TERM is a nest of calls to ADD with P as
;; the prime.
(defund get-addends (term p)
  (declare (xargs :guard (pseudo-termp term)
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (and (acl2::call-of 'add term)
           (equal p (acl2::farg3 term)))
      (append (get-addends (acl2::farg1 term) p)
              (get-addends (acl2::farg2 term) p))
    (list term)))

(defthm pseudo-term-listp-of-get-addends
  (implies (pseudo-termp term)
           (pseudo-term-listp (get-addends term p)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp get-addends))))

(defun make-add-nest (addends p)
  (declare (xargs :guard (and (pseudo-term-listp addends)
                              (pseudo-termp p))
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (endp addends)
      (er hard? 'make-add-nest "No addends")
    (if (endp (rest addends))
        (first addends)
      `(add ,(first addends) ,(make-add-nest (rest addends) p) ,p))))

(defthm pseudo-termp-of-make-add-nest
  (implies (and (pseudo-term-listp addends)
                (pseudo-termp p))
           (pseudo-termp (make-add-nest addends p)))
  :hints (("Goal" :in-theory (enable make-add-nest))))

;; If this shows up, it means that something has gone wrong with the bind-free rules
(defund bind-free-id (x) x)
