; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(defun strip-cars-safe (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((consp (car x)) (cons (caar x) (strip-cars-safe (cdr x))))
        (t (strip-cars-safe (cdr x)))))

(defun alist-subsetp1 (keys a1 a2)
  (declare (xargs :guard t))
  (cond ((atom keys) t)
        (t (and (equal (hons-assoc-equal (car keys) a1)
                       (hons-assoc-equal (car keys) a2))
                (alist-subsetp1 (cdr keys) a1 a2)))))

(defun alist-subsetp (a1 a2)
  (declare (xargs :guard t))
  (alist-subsetp1 (strip-cars-safe a1) a1 a2))

(local (defthm alist-subsetp1-preserves-assoc-on-keys
         (implies (and (alist-subsetp1 keys a1 a2)
                       (member-equal key keys))
                  (equal (hons-assoc-equal key a2)
                         (hons-assoc-equal key a1)))))

(local (defthm hons-assoc-equal-iff-member-equal-strip-cars
         (iff (hons-assoc-equal key alist)
              (member-equal key (strip-cars-safe alist)))))

(defthm alist-subsetp-preserves-assoc-on-keys

; For a key of the smaller alist, this rule reduces assoc into the larger alist
; to assoc into the smaller.

  (implies (and (alist-subsetp a1 a2)
                (hons-assoc-equal key a1))
           (equal (hons-assoc-equal key a2)
                  (hons-assoc-equal key a1))))

(in-theory (disable alist-subsetp))
