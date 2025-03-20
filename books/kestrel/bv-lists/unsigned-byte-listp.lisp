; A lightweight book connecting unsigned-byte-listp to all-unsigned-byte-p.
;
; Copyright (C) 2019-2025 Kestrel Institute
; For unsigned-byte-listp, see the copyright for books/std.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The BV library doesn't use this function very much.  Instead, it uses
;; all-unsigned-byte-p.  In this book, we provide some rules to connect the two
;; functions.

(include-book "all-unsigned-byte-p") ; todo: separate out?
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system) ; todo: separate out?
(include-book "unsigned-byte-listp-def")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "../utilities/equal-of-booleans"))

(defthmd unsigned-byte-listp-rewrite
  (equal (unsigned-byte-listp n x)
         (and (all-unsigned-byte-p n x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

;; Compatible with STD.  Using (null x) in the conclusion might be better.
(defthm unsigned-byte-listp-when-not-consp
  (implies (not (consp x))
           (equal (unsigned-byte-listp n x)
                  (not x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthmd unsigned-byte-listp-forward-to-all-unsigned-byte-p
  (implies (unsigned-byte-listp n x)
           (all-unsigned-byte-p n x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-forward-to-true-listp
  (implies (unsigned-byte-listp n x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm natp-of-car-when-unsigned-byte-listp-forward
  (implies (and (unsigned-byte-listp size x)
                (consp x))
           (natp (car x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-cdr
  (implies (unsigned-byte-listp width x)
           (unsigned-byte-listp width (cdr x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-cons
  (equal (unsigned-byte-listp n (cons a x))
         (and (unsigned-byte-p n a)
              (unsigned-byte-listp n x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-append
  (equal (unsigned-byte-listp width (append x y))
         (and (unsigned-byte-listp width (true-list-fix x))
              (unsigned-byte-listp width y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp append))))

;; avoids name clash with std
(defthm unsigned-byte-listp-of-update-nth-2
  (implies (unsigned-byte-listp width x)
           (equal (unsigned-byte-listp width (update-nth n val x))
                  (and (unsigned-byte-p width val)
                       (<= (nfix n) (len x)) ; can be one past the last element
                       )))
  :hints (("Goal" :in-theory (enable update-nth unsigned-byte-listp))))

(defthm unsigned-byte-listp-of-revappend
  (equal (unsigned-byte-listp width (revappend x y))
         (and (unsigned-byte-listp width (true-list-fix x))
              (unsigned-byte-listp width y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp revappend))))

(defthm unsigned-byte-listp-of-reverse-list
  (equal (unsigned-byte-listp width (reverse-list x))
         (unsigned-byte-listp width (true-list-fix x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp reverse-list))))

;; The version of this in std is a :forward-chaining rule for some reason
(defthm unsigned-byte-p-of-car-when-unsigned-byte-listp-2
  (implies (unsigned-byte-listp width x)
           (equal (unsigned-byte-p width (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

;; Tweaked param names to match std
(defthm unsigned-byte-listp-of-nthcdr
  (implies (unsigned-byte-listp width x)
           (unsigned-byte-listp width (nthcdr n x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp nthcdr))))

;; Perhaps slightly better than the rule in std
(defthm unsigned-byte-listp-of-take-2 ; avoid name clash
  (implies (unsigned-byte-listp width x)
           (equal (unsigned-byte-listp width (take n x))
                  (<= (nfix n) (len x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp nthcdr))))

(defthm unsigned-byte-listp-of-butlast
  (implies (unsigned-byte-listp width x)
           (unsigned-byte-listp width (butlast x n)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp nthcdr))))

(defthm unsigned-byte-listp-of-true-list-fix
  (implies (unsigned-byte-listp width x)
           (unsigned-byte-listp width (true-list-fix x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp true-list-fix))))

(defthm integerp-of-nth-when-unsigned-byte-listp
  (implies (unsigned-byte-listp size x)
           (equal (integerp (nth n x))
                  (< (nfix n) (len x))))
  :hints (("Goal" :in-theory (enable nth))))

(defthmd all-unsigned-byte-p-when-unsigned-byte-listp
  (implies (unsigned-byte-listp size x)
           (all-unsigned-byte-p size x))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p
                                     unsigned-byte-listp))))

(defthm all-unsigned-byte-p-when-unsigned-byte-listp-cheap
  (implies (and (unsigned-byte-listp size2 x) ;free variable makes this cheap
                (equal size2 size)               ;gen?
                )
           (all-unsigned-byte-p size x))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p
                                     unsigned-byte-listp))))

;todo: compare to the one in std
(defthm unsigned-byte-p-of-nth-when-unsigned-byte-listp-2
  (implies (and (unsigned-byte-listp size list)
                (natp n) ;drop?
                )
           (equal (unsigned-byte-p size (nth n list))
                  (< n (len list))))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthm all-integerp-when-unsigned-byte-listp
  (implies (unsigned-byte-listp size x) ; size is a free var
           (all-integerp x))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

;; common special case (8-bit bytes) with no free var
(defthm all-integerp-when-unsigned-byte-listp-8
  (implies (unsigned-byte-listp 8 x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))
