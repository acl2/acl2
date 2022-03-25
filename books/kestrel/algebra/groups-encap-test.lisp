; A test of the group machinery to prove properties of a concrete group
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "groups-encap")

(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable cancel-mod-+)))

;; An example of a group: the set {0,1,2} with the group operation being
;; addition mod 3.
(defun int-mod-3p (x) (and (natp x)
                           (< x 3)))

(defun add-mod-3 (x y) (mod (+ x y) 3))

;; To invert, 0 stays 0, while 1 becomes 2 and vice versa.
(defun inv-mod-3 (x) (if (equal 0 x)
                         0
                       (- 3 x)))

;; The identity element is 0:
(defun id-mod-3 () 0)

;; Now we can obtain the group theorems, after showing that this is indeed a
;; group:

(defthm right-id-mod-3
  (implies (int-mod-3p x)
           (equal (add-mod-3 x (id-mod-3))
                  x))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         right-identity
                         (pred int-mod-3p)
                         (dot add-mod-3)
                         (id id-mod-3)
                         (inv inv-mod-3))))))


(defthm right-inverse-mod-3
  (implies (int-mod-3p x)
           (equal (add-mod-3 x (inv-mod-3 x))
                  (id-mod-3)))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         right-inverse
                         (pred int-mod-3p)
                         (dot add-mod-3)
                         (id id-mod-3)
                         (inv inv-mod-3))))))
