; A lightweight book about the built-in function nat-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
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

(defthm nat-listp-of-cdr
  (implies (nat-listp x)
           (nat-listp (cdr x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;; The non-standard variable names here are to match STD
(defthm nat-listp-of-append
  (equal (nat-listp (append a b))
         (and (nat-listp (true-list-fix a))
              (nat-listp b))))

(defthm nat-listp-of-take-2
  (implies (nat-listp l)
           (equal (nat-listp (take n l))
                  (<= (nfix n) (len l))))
  :hints (("Goal" :in-theory (enable take nat-listp))))

;disble?
(defthm natp-of-car-when-nat-listp-type
  (implies (and (nat-listp x)
                (consp x))
           (natp (car x)))
  :rule-classes :type-prescription)

;; Avoids name clash with books/centaur/fty/baselists.
(defthmd natp-of-car-when-nat-listp-better
  (implies (nat-listp x)
           (equal (natp (car x))
                  (consp x))))

;; Seems better than the one in STD (except perhaps for the double-rewrite).
(defthm nat-listp-of-update-nth-better
  (implies (nat-listp l)
           (equal (nat-listp (update-nth n val l))
                  (and (<= (nfix n) (len l)) ;might be adding to the end
                       (natp val))))
  :hints (("Goal" :in-theory (enable nat-listp update-nth))))

(defthm nat-listp-of-revappend
  (equal (nat-listp (revappend x y))
         (and (nat-listp (true-list-fix x))
              (nat-listp y)))
  :hints (("Goal" :in-theory (enable nat-listp revappend))))

(defthm nat-listp-of-reverse
  (equal (nat-listp (reverse x))
         (and (not (stringp x)) ;odd
              (nat-listp (true-list-fix x))))
  :hints (("Goal" :in-theory (enable nat-listp reverse))))

(defthm natp-of-car-of-last-when-nat-listp
  (implies (nat-listp x)
           (equal (natp (car (last x)))
                  (consp x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;; Or use integerp-when-natp
(defthmd integerp-of-car-of-last-when-nat-listp
  (implies (nat-listp x)
           (equal (integerp (car (last x)))
                  (consp x)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;; Or use <=-of-0-when-natp
(defthmd <=-of-0-and-car-of-last-when-nat-listp
  (implies (nat-listp x)
           (<= 0 (car (last x))))
  :hints (("Goal" :in-theory (enable nat-listp))))

; var names are to match std
(defthm nat-listp-of-set-difference-equal
  (implies (nat-listp x)
           (nat-listp (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal nat-listp))))

(defthm nat-listp-when-not-consp-cheap
  (implies (not (consp l))
           (equal (nat-listp l)
                  (equal nil l)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable nat-listp))))

(defthmd integer-listp-when-nat-listp
  (implies (nat-listp l)
           (integer-listp l))
  :hints (("Goal" :in-theory (enable integer-listp nat-listp))))

(defthm nat-listp-of-remove1-equal
  (implies (nat-listp nats)
           (nat-listp (remove1-equal a nats)))
  :hints (("Goal" :in-theory (enable remove1-equal))))

;; ACL2 may already have forward-chaining rules which together cover this inference.
(defthmd nat-listp-forward-to-true-listp
  (implies (nat-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

;; ACL2 may already have forward-chaining rules which together cover this inference.
(defthmd nat-listp-forward-to-rational-listp
  (implies (nat-listp x)
           (rational-listp x))
  :rule-classes :forward-chaining)
