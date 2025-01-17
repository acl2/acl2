; A recognizer for alists that can be made into ACL2 arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;todo: make local
(defthm alistp-of-cdr
  ;; [Jared] changed variable from lst to x for std/alists compatibility
  (implies (alistp x)
           (alistp (cdr x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes an alist mapping indices to values (suitable for conversion to an array).
;; Unlike BOUNDED-INTEGER-ALISTP, this one doesn't allow an entry to be :header.
;; todo: remve the p from natp in the name.
(defund bounded-natp-alistp (l n)
  (declare (xargs :guard (rationalp n)))
  (if (atom l)
      t ; todo: (null l)
    (and (consp (car l))
         (let ((key (caar l)))
           (and (natp key)
                (< key n)
                (bounded-natp-alistp (cdr l) n))))))

(defthm bounded-natp-alistp-monotone
  (implies (and (bounded-natp-alistp alist y)
                (<= y x))
           (bounded-natp-alistp alist x))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthmd <-when-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist n)
                (consp alist))
           (< (caar alist) n))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthm <-of-0-when-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist n) ;n is a free var
                (consp alist))
           (<= 0 (caar alist)))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthm equal-of-non-natp-and-caar-when-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist n) ;n is a free var
                (consp alist)
                (not (natp val)))
           (equal (equal val (caar alist))
                  nil))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthm integerp-of-caar-when-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist n) ;n is a free var
                (consp alist))
           (integerp (caar alist)))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthm true-listp-of-car-when-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist n) ;n is a free var
                (consp alist))
           (consp (car alist)))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

(defthm bounded-natp-alistp-of-cdr
  (implies (bounded-natp-alistp alist n)
           (bounded-natp-alistp (cdr alist) n))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

;expensive
(defthm alistp-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist free) ;had (len alist) instead of free
                (true-listp alist))
           (alistp alist))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp alistp))))

(defthm bounded-integer-alistp-when-bounded-natp-alistp
  (implies (and (natp n)
                (bounded-natp-alistp alist n))
           (equal (bounded-integer-alistp alist n)
                  (true-listp alist)))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp bounded-integer-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund natp-alistp (l)
  (declare (xargs :guard t))
  (if (atom l)
      t ; todo: (null l)
    (and (consp (car l))
         (let ((key (caar l)))
           (and (natp key)
                (natp-alistp (cdr l)))))))

(defthm natp-alistp-of-cdr
  (implies (natp-alistp lst)
           (natp-alistp (cdr lst)))
  :hints (("Goal" :in-theory (enable natp-alistp))))

(defthm natp-alistp-when-bounded-natp-alistp
  (implies (bounded-natp-alistp alist free)
           (natp-alistp alist))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp natp-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund max-key (alist max-so-far)
  (declare (xargs :guard (and (true-listp alist)
                              (natp-alistp alist) ;relax?
                              (rationalp max-so-far)
                              )
                  :guard-hints (("Goal" :in-theory (enable natp-alistp)))
                  ))
  (if (endp alist)
      max-so-far
    (max-key (rest alist) (max max-so-far (car (first alist))))))

(defthm max-key-when-not-consp-cheap
  (implies (not (consp alist))
           (equal (max-key alist max-so-far)
                  max-so-far))
  :hints (("Goal" :in-theory (enable max-key))))

(defthm natp-of-max-key
  (implies (and (natp-alistp alist)
                (natp max-so-far))
           (natp (max-key alist max-so-far)))
  :hints (("Goal" :in-theory (enable max-key)
           :expand ((NATP-ALISTP ALIST)))))

(defthm rationalp-of-max-key
  (implies (and (natp-alistp alist)
                (rationalp max-so-far))
           (rationalp (max-key alist max-so-far)))
  :hints (("Goal" :in-theory (enable max-key)
           :expand ((NATP-ALISTP ALIST)))))

(defthm integerp-of-max-key
  (implies (and (natp-alistp alist)
                (integerp max-so-far))
           (integerp (max-key alist max-so-far)))
  :hints (("Goal" :in-theory (enable max-key)
           :expand ((NATP-ALISTP ALIST)))))

;; (defthm integerp-of-max-key-tp
;;   (implies (and (natp-alistp alist)
;;                 (natp max-so-far))
;;            (integerp (max-key alist max-so-far)))
;;   :rule-classes :type-prescription
;;   :hints (("Goal" :expand ((NATP-ALISTP ALIST)))))

(defthm max-key-linear-1
  (implies (and (natp-alistp alist)
                (natp max-so-far))
           (<= max-so-far (max-key alist max-so-far)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable max-key)
           :expand ((NATP-ALISTP ALIST)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: use bounded-natp-alistp?
(defthm bounded-integer-alistp-of-+-of-1-and-max-key
  (implies (and (natp-alistp alist)
                (true-listp alist)
                (integerp max-so-far))
           (bounded-integer-alistp alist (+ 1 (max-key alist max-so-far))))
  :hints (("Goal" :in-theory (enable natp-alistp bounded-integer-alistp max-key))))

;todo: use bounded-natp-alistp?
(defthm bounded-integer-alistp-of-+-of-1-and-max-key-0
  (implies (and (natp-alistp alist)
                (true-listp alist)
                )
           (bounded-integer-alistp alist (+ 1 (max-key alist 0))))
  :hints (("Goal" :use (:instance bounded-integer-alistp-of-+-of-1-and-max-key (max-so-far 0)))))

(defthm bounded-natp-alistp-of-+-of-1-and-max-key-0-when-bounded-natp-alistp
  (implies (and (bounded-natp-alistp alist bound)
                (true-listp alist)
                )
           (bounded-natp-alistp alist (+ 1 (max-key alist max-so-far))))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp
                                     max-key))))

(defthm max-key-linear-2
  (implies (and (bounded-natp-alistp alist bound)
                (integerp max-so-far)
                (integerp bound)
                (< max-so-far bound))
           (<= (max-key alist max-so-far) (+ -1 bound)))
  :rule-classes ((:linear :trigger-terms ((max-key alist max-so-far))))
  :hints (("Goal" :in-theory (enable max-key bounded-natp-alistp))))

(defthm <-of-max-key
  (implies (and (bounded-natp-alistp alist bound)
                ;(integerp max-so-far)
                ;(integerp bound)
                (< max-so-far bound))
           (< (max-key alist max-so-far) bound))
  :hints (("Goal" :in-theory (enable max-key bounded-natp-alistp))))
