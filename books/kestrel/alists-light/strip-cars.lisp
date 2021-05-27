; A lightweight book about the built-in function strip-cars.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable strip-cars))

(defthm consp-of-strip-cars
  (equal (consp (strip-cars x))
         (consp x))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm len-of-strip-cars
  (equal (len (strip-cars x))
         (len x))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-of-cons
  (equal (strip-cars (cons a x))
         (cons (car a)
               (strip-cars x)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-of-acons
  (equal (strip-cars (acons key datum alist))
         (cons key
               (strip-cars alist)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm car-of-strip-cars
  (equal (car (strip-cars x))
         (car (car x)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm cadr-of-strip-cars
  (equal (cadr (strip-cars x))
         (car (cadr x)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm nth-of-strip-cars
  (equal (nth n (strip-cars x))
         (car (nth n x)))
  :hints (("Goal" :in-theory (enable nth strip-cars))))

(defthm strip-cars-of-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-when-not-consp-cheap
  (implies (not (consp x))
           (equal (strip-cars x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable strip-cars))))

;; Not sure which form is better
(defthmd strip-cars-of-cdr
  (equal (strip-cars (cdr x))
         (cdr (strip-cars x)))
  :hints (("Goal" :in-theory (enable strip-cars))))

(theory-invariant (incompatible (:rewrite strip-cars-of-cdr) (:definition strip-cars)))

(defthmd member-equal-of-strip-cars-iff
  (implies (alistp alist)
           (iff (member-equal key (strip-cars alist))
                (assoc-equal key alist)))
  :hints (("Goal" :in-theory (enable assoc-equal member-equal strip-cars))))

(defthm strip-cars-of-pairlis$
  (equal (strip-cars (pairlis$ x y))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable strip-cars))))
