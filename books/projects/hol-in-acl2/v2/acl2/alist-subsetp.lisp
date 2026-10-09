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

(defthm alist-subsetp1-keys-s-x
  (alist-subsetp1 keys x x))

(defthm alist-subsetp-s-x
  (alist-subsetp x x))

(local (defthm strip-cars-safe-append
         (equal (strip-cars-safe (append x y))
                (append (strip-cars-safe x)
                        (strip-cars-safe y)))))

(local (defthm alist-subsetp1-append
; uncomfortable induction depth: finishes with proof of *1.1.1.1
         (equal (alist-subsetp1 (append k1 k2) x y)
                (and (alist-subsetp1 k1 x y)
                     (alist-subsetp1 k2 x y)))))

(local (defthm alist-subsetp-from-append-lemma
         (implies (and (alist-subsetp1 ky (append x y) z)
                       (not (intersectp-equal (strip-cars-safe x)
                                              ky)))
                  (alist-subsetp1 ky y z))))

(defthm alist-subsetp-from-append
  (implies (and (not (intersectp-equal (strip-cars-safe x)
                                       (strip-cars-safe y)))
                (not (alist-subsetp y z)))
           (not (alist-subsetp (append x y) z))))

(in-theory (disable alist-subsetp))
