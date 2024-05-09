; Recognizing lists of symbol-term-alists
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/symbol-term-alistp" :dir :system)

;todo: move
(defthm symbol-listp-of-strip-cars-when-symbol-term-alistp
  (implies (symbol-term-alistp alist)
           (symbol-listp (strip-cars alist)))
  :hints (("Goal" :in-theory (enable symbol-listp strip-cars))))

;todo: move
(defthm symbol-term-alistp-of-append
  (equal (symbol-term-alistp (append x y))
         (and (symbol-term-alistp (true-list-fix x))
              (symbol-term-alistp y))))

;todo: move
(defthm symbol-term-alistp-of-true-list-fix
  (implies (symbol-term-alistp x)
           (symbol-term-alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is gross in order to match what deflist generates.
(defun symbol-term-alist-listp (x)
  (declare (xargs :normalize nil :guard t))
  (let ((__function__ 'symbol-term-alist-listp))
    (declare (ignorable __function__))
    (if (consp x)
        (and (symbol-term-alistp (car x))
             (symbol-term-alist-listp (cdr x)))
      (null x))))

(defthm symbol-term-alistp-of-car-when-symbol-term-alist-listp
  (implies (symbol-term-alist-listp lst)
           (symbol-term-alistp (car lst)))
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))

(defthm symbol-term-alist-listp-of-cdr-when-symbol-term-alist-listp
  (implies (symbol-term-alist-listp lst)
           (symbol-term-alist-listp (cdr lst)))
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))

(defthm symbol-term-alist-listp-forward-to-true-listp
  (implies (symbol-term-alist-listp lst)
           (true-listp lst))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))

(defthm symbol-term-alist-listp-of-cons
  (equal (symbol-term-alist-listp (cons alist alists))
         (and (symbol-term-alistp alist)
              (symbol-term-alist-listp alists)))
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))

(defthm symbol-term-alist-listp-of-update-nth
  (implies (and (symbol-term-alistp alist)
                (symbol-term-alist-listp alists))
           (symbol-term-alist-listp (update-nth n alist alists)))
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))

(defthm symbol-term-alistp-of-nth-when-symbol-term-alist-listp
  (implies (symbol-term-alist-listp alists)
           (symbol-term-alistp (nth n alists)))
  :hints (("Goal" :in-theory (enable symbol-term-alist-listp))))
