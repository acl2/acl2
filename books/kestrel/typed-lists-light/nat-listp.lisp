; A lightweight book about the built-in function nat-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable nat-listp))

(defthmd eqlable-listp-when-nat-listp
  (implies (nat-listp x)
           (eqlable-listp x))
  :hints (("Goal" :in-theory (enable nat-listp))))

;avoid name clash
(defthmd true-listp-when-nat-listp-rewrite
  (implies (nat-listp x)
           (true-listp x)))

(defthm nat-listp-of-union-equal-2 ;name clash
  (equal (nat-listp (union-equal x y))
         (and (nat-listp (true-list-fix x))
              (nat-listp y)))
  :hints (("Goal" :in-theory (e/d (union-equal nat-listp) (natp)))))

(defthm nat-listp-of-true-list-fix
  (implies (nat-listp x)
           (nat-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;; matches std
(defthm natp-of-nth-when-nat-listp
  (implies (nat-listp x)
           (iff (natp (nth n x))
                (< (nfix n) (len x))))
  :hints (("Goal" :in-theory (enable nat-listp nth))))

(defthm natp-of-nth-when-nat-listp-type
  (implies (and (nat-listp x)
                (< n (len x))
                (natp n))
           (natp (nth n x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nat-listp nth))))

;; (defthm nth-when-nat-listp-type
;;   (implies (nat-listp x)
;;            (or (equal nil (nth n x))
;;                (natp (nth n x))))
;;   :hints (("Goal" :in-theory (enable nat-listp nth)))
;;   :rule-classes :type-prescription)

(defthm nat-listp-of-add-to-set-equal
  (equal (nat-listp (add-to-set-equal a x))
         (and (natp a)
              (nat-listp x)))
  :hints (("Goal" :in-theory (enable add-to-set-equal nat-listp))))

;move
;; tweaked to match books/arithmetic/nat-listp.lisp
(defthm nat-listp-of-cons
  (equal (nat-listp (cons a x))
         (and (natp a)
              (nat-listp x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;; The non-standard variable names here are to match STD
(defthm nat-listp-of-append
  (equal (nat-listp (append a b))
         (and (nat-listp (true-list-fix a))
              (nat-listp b))))
