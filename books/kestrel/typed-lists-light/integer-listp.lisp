; A lightweight book about the built-in function integer-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable integer-listp))
(local (include-book "../lists-light/len"))

(defthm integer-listp-of-cdr
  (implies (integer-listp x)
           (integer-listp (cdr x)))
  :hints (("Goal" :in-theory (enable integer-listp))))

(defthm integer-listp-of-cons
  (equal (integer-listp (cons a x))
         (and (integerp a)
              (integer-listp x)))
  :hints (("Goal" :in-theory (enable integer-listp))))

;compare to the one in books/std/typed-lists/integer-listp.
;that one uses iff?
(defthm integer-listp-of-take-2
  (implies (integer-listp lst)
           (equal (integer-listp (take n lst))
                  (<= (nfix n) (len lst))))
  :hints (("Goal" :in-theory (e/d (take integer-listp) (;TAKE-OF-CDR-BECOMES-SUBRANGE
                                              )))))

;; better than the version in books/centaur/fty/baselists.lisp
(defthm integerp-of-car-when-integer-listp-better
  (implies (integer-listp x)
           (equal (integerp (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable integer-listp))))

(defthm integerp-of-car-when-integer-listp-cheap
  (implies (integer-listp x)
           (equal (integerp (car x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable integer-listp))))

;; better than the one in std?
(defthm integer-listp-of-update-nth-better
  (implies (integer-listp lst)
           (equal (integer-listp (update-nth index val lst))
                  (and (<= (nfix index) (len lst))
                       (integerp val))))
  :hints (("Goal" :in-theory (enable update-nth integer-listp)
           :induct (update-nth index val lst))))

(defthm integerp-of-nth-when-integer-listp-cheap
  (implies (and (integer-listp x)
                (natp n)
                (< n (len x)))
           (integerp (nth n x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (enable integer-listp))))

(local
 (defthm not-integer-listp-of-revappend-when-not-integer-listp
   (implies (not (integer-listp y))
            (not (integer-listp (revappend x y))))
   :hints (("Goal" :in-theory (enable integer-listp revappend)))))

(defthm integer-listp-of-revappend
  (equal (integer-listp (revappend x y))
         (and (integer-listp (true-list-fix x))
              (integer-listp y)))
  :hints (("Goal" :in-theory (enable integer-listp revappend))))
