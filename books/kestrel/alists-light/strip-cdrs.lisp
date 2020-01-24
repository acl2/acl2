; A lightweight book about the built-in function strip-cdrs.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable strip-cdrs))

(defthm consp-of-strip-cdrs
  (equal (consp (strip-cdrs x))
         (consp x))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm len-of-strip-cdrs
  (equal (len (strip-cdrs x))
         (len x))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons a x))
         (cons (cdr a)
               (strip-cdrs x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm car-of-strip-cdrs
  (equal (car (strip-cdrs x))
         (cdr (car x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm cadr-of-strip-cdrs
  (equal (cadr (strip-cdrs x))
         (cdr (cadr x)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))

(defthm nth-of-strip-cdrs
  (equal (nth n (strip-cdrs x))
         (cdr (nth n x)))
  :hints (("Goal" :in-theory (enable nth strip-cdrs))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append x y))
         (append (strip-cdrs x)
                 (strip-cdrs y)))
  :hints (("Goal" :in-theory (enable strip-cdrs))))
