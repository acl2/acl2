; A lightweight book about the built-in function last1.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun last1 (l)
  (declare (xargs :guard (listp l)))
  (if (endp l)
      nil
    (if (atom (cdr l))
        (car l)
      (last1 (cdr l)))))

(in-theory (disable last1))

;; Use the param name x to match books/kestrel/utilities/lists/last-theorems.lisp.
(defthm last1-of-cdr
  (implies (consp x)
           (equal (last1 (cdr x))
                  (if (consp (cdr x))
                      (last1 x)
                    (cadr x))))
  :hints (("Goal" :in-theory (enable last1))))

(defthmd car-of-last1-becomes-nth
  (equal (last1 lst)
         (nth (+ -1 (len lst)) lst))
  :hints (("Goal" :in-theory (enable last1))))

(defthmd nth-of-len-minus-1-becomes-car-of-last1
  (equal (last1 lst)
         (nth (+ -1 (len lst)) lst))
  :hints (("Goal" :in-theory (enable last1))))

(theory-invariant (incompatible (:rewrite car-of-last1-becomes-nth) (:rewrite nth-of-len-minus-1-becomes-car-of-last1)))

;; Tweaked to match std
(defthm last1-of-cons
  (equal (last1 (cons a x))
         (if (consp x)
             (last1 x)
           a))
  :hints (("Goal" :in-theory (enable last1))))

(defthm last1-when-not-consp-cheap
  (implies (not (consp l))
           (equal (last1 l)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable last1))))

(defthm acl2-count-of-last1-linear
  (<= (acl2-count (last1 x))
      (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable last1))))

;; Avoid name clash with std
(defthm last1-of-append-2
  (equal (last1 (append x y))
         (if (consp y)
             (last1 y)
           (if (consp x)
               (last1 x)
             nil))))

(defthm member-last1
  (implies (consp l)
           (member-equal (last1 l) l))
  :hints (("Goal" :in-theory (enable last1))))
