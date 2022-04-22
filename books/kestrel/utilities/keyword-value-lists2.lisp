; Utilities about keyword-value-lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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

;; TODO: Compare to remove-keyword
(defun clear-key-in-keyword-value-list (key keyword-value-list)
  (declare (xargs :guard (and (keywordp key)
                              (keyword-value-listp keyword-value-list))))
  (if (endp keyword-value-list)
      nil
    (let ((first-key (first keyword-value-list))
          (first-val (second keyword-value-list)))
      (if (eq key first-key)
          (clear-key-in-keyword-value-list key (cddr keyword-value-list)) ;skip the key and its val
        (cons first-key (cons first-val (clear-key-in-keyword-value-list key (cddr keyword-value-list))))))))

(defthm keyword-value-listp-of-clear-key-in-keyword-value-list
  (implies (keyword-value-listp lst)
           (keyword-value-listp (clear-key-in-keyword-value-list key lst)))
  :hints (("Goal" :in-theory (enable keyword-value-listp))))

;;;;;;;;;;

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
