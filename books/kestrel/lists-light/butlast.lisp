; A lightweight book about the built-in function butlast.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "take"))
(local (include-book "true-list-fix"))

(in-theory (disable butlast))

(defthm consp-of-butlast
  (equal (consp (butlast lst n))
         (< (nfix n) (len lst)))
  :hints (("Goal" :in-theory (enable consp butlast))))

(defthm car-of-butlast
  (equal (car (butlast lst n))
         (if (< (nfix n) (len lst))
             (car lst)
           nil))
  :hints (("Goal" :in-theory (enable butlast))))

(defthm butlast-of-cons
  (equal (butlast (cons a lst) n)
         (if (<= (nfix n) (len lst))
             (cons a (butlast lst n))
           nil))
  :hints (("Goal" :in-theory (enable butlast))))

(defthm cdr-of-butlast
  (equal (cdr (butlast lst n))
         (butlast (cdr lst) n))
  :hints (("Goal" :expand (len (cdr lst))
           :in-theory (enable butlast))))

(defthm butlast-of-nil
  (equal (butlast nil n)
         nil)
  :hints (("Goal" :in-theory (enable butlast))))
