; Check for a list of consecutive integers
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)

;; Check whether ITEMS is a list of consecutive integers
(defund consecutivep (items)
  (declare (xargs :guard (all-integerp items)))
  (if (atom items)
      t
    (if (atom (rest items))
        t
      (and (equal (second items) (+ 1 (first items)))
           (consecutivep (rest items))))))

(defthm consecutivep-of-cons
  (equal (consecutivep (cons a x))
         (if (endp x)
             t
           (and (equal (car x) (+ 1 a))
                (consecutivep x))))
  :hints (("Goal" :in-theory (enable consecutivep))))

(defthm consecutivep-of-cdr
  (implies (consecutivep x)
           (consecutivep (cdr x)))
  :hints (("Goal" :in-theory (enable consecutivep))))

(defthm consecutivep-of-append
  (equal (consecutivep (append x y))
         (and (consecutivep x)
              (consecutivep y)
              (if (or (endp x)
                      (endp y))
                  t
                (equal (car y) (+ 1 (car (last x)))))))
  :hints (("Goal" :in-theory (enable consecutivep append))))

(defthmd car-of-cadr-when-consecutivep-of-strip-cars
  (implies (and (consecutivep (strip-cars x))
                (consp (cdr x)))
           (equal (car (car (cdr x)))
                  (+ 1 (car (car x)))))
  :hints (("Goal" :in-theory (enable consecutivep strip-cars))))

(defthmd caar-of-cdr-when-consecutivep-of-strip-cars
  (implies (and (consecutivep (strip-cars rev-dag-lst))
                (consp (cdr rev-dag-lst)))
           (equal (car (car (cdr rev-dag-lst)))
                  (+ 1 (car (car rev-dag-lst)))))
  :hints (("Goal" :in-theory (enable strip-cars))))
