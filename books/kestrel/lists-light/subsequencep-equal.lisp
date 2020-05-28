; A lightweight book about the function subsequencep-equal.
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))
(local (include-book "cdr"))

;; See also subsequencep.lisp.

;; Note that the function subsequencep is built into ACL2.  It uses EQL as the
;; test.

(defund subsequencep-equal (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (endp x)
      t
    (let ((tail (member-equal (first x) y)))
      (if (endp tail)
          nil
        (subsequencep-equal (rest x) (rest tail))))))

(defthm subsequencep-equal-of-take
  (implies (<= (nfix n) (len x))
           (subsequencep-equal (take n x) x))
  :hints (("Goal" :in-theory (enable subsequencep-equal))))

(defthm subsequencep-equal-same
  (subsequencep-equal x x)
  :hints (("Goal" :in-theory (enable subsequencep-equal))))

(defthm subsequencep-equal-when-not-consp-cheap
  (implies (not (consp x))
           (subsequencep-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsequencep-equal))))

(defthm not-subsequencep-equal-when-member-equal-and-not-member-equal
  (implies (and (member-equal item x)
                (not (member-equal item y)))
           (not (subsequencep-equal x y)))
  :hints (("Goal" :in-theory (enable subsequencep-equal member-equal-when-not-member-equal-of-cdr))))
