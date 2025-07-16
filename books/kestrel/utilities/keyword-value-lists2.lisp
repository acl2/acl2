; Utilities about keyword-value-lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "keyword-value-listp")
(include-book "lookup-keyword")

;(in-theory (disable keywordp))

(defthm keyword-value-listp-of-remove-keyword
  (implies (keyword-value-listp l)
           (keyword-value-listp (remove-keyword word l)))
  :hints (("Goal" :in-theory (enable keyword-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extract the keys of a keyword-value-list
(defun keyword-value-list-keys (k)
  (declare (xargs :guard (keyword-value-listp k)))
  (if (endp k)
      nil
    (cons (car k)
          (keyword-value-list-keys (cddr k)))))

(defthm keyword-listp-of-keyword-value-list-keys
  (implies (keyword-value-listp l)
           (keyword-listp (keyword-value-list-keys l)))
  :hints (("Goal" :in-theory (enable keyword-value-listp))))

(defthm symbol-listp-of-keyword-value-list-keys
  (implies (keyword-value-listp l)
           (symbol-listp (keyword-value-list-keys l)))
  :hints (("Goal" :in-theory (enable keyword-value-listp))))
