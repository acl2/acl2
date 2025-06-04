; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(defun alist-subsetp1 (keys a1 a2)
  (declare (xargs :guard (and (true-listp keys) (alistp a1) (alistp a2))))
  (cond ((endp keys) t)
        (t (and (equal (assoc-equal (car keys) a1)
                       (assoc-equal (car keys) a2))
                (alist-subsetp1 (cdr keys) a1 a2)))))

(defun alist-subsetp (a1 a2)
  (declare (xargs :guard (and (alistp a1) (alistp a2))))
  (alist-subsetp1 (strip-cars a1) a1 a2))

(local (defthm alist-subsetp1-preserves-assoc-on-keys
         (implies (and (alist-subsetp1 keys a1 a2)
                       (member-equal key keys))
                  (equal (assoc-equal key a2)
                         (assoc-equal key a1)))))

(local (defthm assoc-equal-iff-member-equal-strip-cars
         (implies (alistp alist)
                  (iff (assoc-equal key alist)
                       (member-equal key (strip-cars alist))))))

(defthm alist-subsetp-preserves-assoc-on-keys

; For a key of the smaller alist, this rule reduces assoc into the larger alist
; to assoc into the smaller.

  (implies (and (alist-subsetp a1 a2)
                (alistp a1)
                (assoc-equal key a1))
           (equal (assoc-equal key a2)
                  (assoc-equal key a1))))

(in-theory (disable alist-subsetp))
