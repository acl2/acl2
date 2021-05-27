; A lightweight book about the built-in function symbol-alistp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm symbol-alistp-of-cons
  (equal (symbol-alistp (cons pair alist))
         (and (consp pair)
              (symbolp (car pair))
              (symbol-alistp alist)))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm symbol-alistp-of-acons
  (equal (symbol-alistp (acons key val alist))
         (and (symbolp key)
              (symbol-alistp alist)))
  :hints (("Goal" :in-theory (enable symbol-alistp acons))))

(defthm symbol-alistp-of-append
  (equal (symbol-alistp (append x y))
         (and (symbol-alistp (true-list-fix x))
              (symbol-alistp y)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm symbol-alistp-of-union-equal
  (implies (and (symbol-alistp x)
                (symbol-alistp y))
           (symbol-alistp (union-equal x y)))
  :hints (("Goal" :in-theory (enable union-equal))))

(defthm symbol-alistp-of-cdr
  (implies (symbol-alistp alist)
           (symbol-alistp (cdr alist)))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm symbol-alistp-of-take
  (implies (symbol-alistp alist)
           (equal (symbol-alistp (take n alist))
                  (<= (nfix n) (len alist))))
  :hints (("Goal" :in-theory (enable symbol-alistp take))))

(defthm symbol-alistp-of-nthcdr
  (implies (symbol-alistp alist)
           (symbol-alistp (nthcdr n alist)))
  :hints (("Goal" :in-theory (enable symbol-alistp nthcdr))))

(defthmd symbolp-of-car-of-car-when-symbol-alistp
  (implies (symbol-alistp alist)
           (symbolp (car (car alist))))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm symbolp-of-car-of-car-when-symbol-alistp-cheap
  (implies (symbol-alistp alist)
           (symbolp (car (car alist))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm symbol-listp-of-strip-cars-when-symbol-alistp
  (implies (symbol-alistp alist)
           (symbol-listp (strip-cars alist)))
  :hints (("Goal" :in-theory (enable symbol-listp strip-cars))))

(defthm symbol-listp-of-strip-cars-when-symbol-alistp-cheap
  (implies (symbol-alistp alist)
           (symbol-listp (strip-cars alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm symbol-alistp-of-pairlis$-alt
  (implies (symbol-listp symbols)
           (symbol-alistp (pairlis$ symbols vals))))

(defthm symbol-alistp-forward-to-true-listp
  (implies (symbol-alistp x)
           (true-listp x))
  :rule-classes :forward-chaining)

;; Disabled by default for speed
(defthmd true-listp-when-symbol-alistp
  (implies (symbol-alistp x)
           (true-listp x)))

(defthm symbol-alistp-of-revappend
  (equal (symbol-alistp (revappend x y))
         (and (symbol-alistp (true-list-fix x))
              (symbol-alistp y)))
  :hints (("Goal" :in-theory (enable revappend))))
