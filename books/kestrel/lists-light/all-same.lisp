; Recognizing a list all of whose elements are the same
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-equal-dollar")

(defund all-same (lst)
  (declare (xargs :guard (true-listp lst)))
  (or (atom lst)
      (all-equal$ (car lst) (cdr lst))))

(defthm booleanp-of-all-same
  (booleanp (all-same lst)))

(defthmd nth-when-all-same
  (implies (and (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :in-theory (enable (:i nth) all-equal$ all-same))))

(defthm nth-when-all-same-cheap
  (implies (and (syntaxp (quotep lst))
                (all-same lst)
                (integerp x))
           (equal (nth x lst)
                  (if (< x (len lst))
                      (first lst)
                    nil)))
  :hints (("Goal" :use nth-when-all-same
           :in-theory (disable nth-when-all-same))))

(defthm all-same-of-revappend
  (equal (all-same (revappend l1 l2))
         (and (all-same l1)
              (all-same l2)
              (if (or (endp l1)
                      (endp l2))
                  t
                (equal (car l1) (car l2)))))
  :hints (("Goal" :in-theory (enable all-same))))

(defthm all-same-of-reverse
  (equal (all-same (reverse l1))
         (all-same l1))
  :hints (("Goal" :in-theory (enable reverse all-same))))
