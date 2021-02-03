; A lightweight book about mv-nth
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable mv-nth))

;fixme think about this
(defthmd mv-nth-becomes-nth
  (equal (mv-nth n x)
         (nth n x))
  :hints (("Goal" :in-theory (enable mv-nth))))

(defthm equal-of-mv-nth0-and-car
  (equal (equal (mv-nth 0 x) (car x))
         t)
  :hints (("Goal" :in-theory (enable mv-nth))))

(defthm equal-of-mv-nth1-and-cadr
  (equal (equal (mv-nth 1 x) (cadr x))
         t)
  :hints (("Goal" :in-theory (enable mv-nth))))

(defthm equal-of-mv-nth-and-nth
  (equal (equal (mv-nth n x) (nth n x))
         t)
  :hints (("Goal" :in-theory (enable mv-nth))))

;; n will almost always be a constant
(defthm mv-nth-of-cons-alt
  (equal (mv-nth n (cons a b))
         (if (zp n)
             a
           (mv-nth (+ -1 n) b)))
  :hints (("Goal" :in-theory (enable mv-nth))))
