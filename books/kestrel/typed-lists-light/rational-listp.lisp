; A lightweight book about the built-in function rational-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(in-theory (disable rational-listp))

(defthm rationalp-of-car-when-rational-listp-cheap
  (implies (and (rational-listp x)
                (consp x))
           (rationalp (car x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rational-listp))))

(defthm rational-listp-of-cdr
  (implies (rational-listp x)
           (rational-listp (cdr x)))
  :hints (("Goal" :in-theory (enable rational-listp))))

(defthm rational-listp-of-cons
  (equal (rational-listp (cons a x))
         (and (rationalp a)
              (rational-listp x)))
  :hints (("Goal" :in-theory (enable rational-listp))))

;avoid name clash
(defthm rational-listp-of-append-2
  (equal (rational-listp (append x y))
         (and (rational-listp (true-list-fix x))
              (rational-listp y)))
  :hints (("Goal" :in-theory (enable rational-listp))))

(defthm rational-listp-of-take-2
  (implies (rational-listp l)
           (equal (rational-listp (take n l))
                  (<= (nfix n) (len l))))
  :hints (("Goal" :in-theory (enable take rational-listp))))

;; Kept disabledp by default
(defthmd rational-listp-when-nat-listp
  (implies (nat-listp items)
           (equal (rational-listp items)
                  (true-listp items)))
  :hints (("Goal" :in-theory (enable nat-listp rational-listp))))
