; Recognizing lists of symbol-alists
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Also appears elsewhere in the books.
;; This is defined using COND to match books/kestrel/utilities/auto-instance.lisp.
(defund symbol-alist-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        (t (and (symbol-alistp (car lst))
                (symbol-alist-listp (cdr lst))))))

(defthm symbol-alistp-of-car-when-symbol-alist-listp
  (implies (symbol-alist-listp lst)
           (symbol-alistp (car lst)))
  :hints (("Goal" :in-theory (enable symbol-alist-listp))))

(defthm symbol-alist-listp-of-cdr-when-symbol-alist-listp
  (implies (symbol-alist-listp lst)
           (symbol-alist-listp (cdr lst)))
  :hints (("Goal" :in-theory (enable symbol-alist-listp))))

(defthm symbol-alist-listp-forward-to-true-listp
  (implies (symbol-alist-listp lst)
           (true-listp lst))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-alist-listp))))

(defthm symbol-alist-listp-of-cons
  (equal (symbol-alist-listp (cons alist alists))
         (and (symbol-alistp alist)
              (symbol-alist-listp alists)))
  :hints (("Goal" :in-theory (enable symbol-alist-listp))))

(defthm symbol-alist-listp-of-update-nth
  (implies (and (symbol-alistp alist)
                (symbol-alist-listp alists))
           (symbol-alist-listp (update-nth n alist alists)))
  :hints (("Goal" :in-theory (enable symbol-alist-listp))))
