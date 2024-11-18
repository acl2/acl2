; Recognizing lists of alists
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund alist-listp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (null lst)
    (and (alistp (car lst))
         (alist-listp (cdr lst)))))

(defthm alist-listp-forward-to-true-listp
  (implies (alist-listp lst)
           (true-listp lst))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable alist-listp))))

;; Disable?
(defthm alistp-of-car-when-alist-listp
  (implies (alist-listp lst)
           (alistp (car lst)))
  :hints (("Goal" :in-theory (enable alist-listp))))

(defthm alistp-of-cdr-when-alist-listp
  (implies (alist-listp lst)
           (alist-listp (cdr lst)))
  :hints (("Goal" :in-theory (enable alist-listp))))

(defthm alistp-of-nth
  (implies (alist-listp alists)
           (alistp (nth n alists)))
  :hints (("Goal" :in-theory (enable alist-listp))))

(defthm alistp-listp-of-cons
  (equal (alist-listp (cons item lst))
         (and (alistp item)
              (alist-listp lst)))
  :hints (("Goal" :in-theory (enable alist-listp))))

(defthm alistp-listp-of-cdr
  (implies (alist-listp lst)
           (alist-listp (cdr lst)))
  :hints (("Goal" :in-theory (enable alist-listp))))

(defthm alist-listp-of-revappend
  (equal (alist-listp (revappend x y))
         (and (alist-listp (true-list-fix x))
              (alist-listp y)))
  :hints (("Goal" :in-theory (enable alist-listp revappend))))

;; Where should this go?
(defthmd alistp-of-cdr-when-alist-listp-of-strip-cdrs
  (implies (alist-listp (strip-cdrs alist))
           (alistp (cdr (car alist))))
  :hints (("Goal" :in-theory (enable alist-listp))))
