; A lightweight book about the built-in function subsetp-equal.
;
; Copyright (C) 2016-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "member-equal"))

(in-theory (disable subsetp-equal))

(defthm subsetp-equal-of-append
  (equal (subsetp-equal (append x y) z)
         (and (subsetp-equal x z)
              (subsetp-equal y z)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cons
  (equal (subsetp-equal (cons a x) y)
         (and (member-equal a y)
              (subsetp-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-nil
  (subsetp-equal nil x)
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-not-consp
  (implies (not (consp x))
           (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-union-equal
  (equal (subsetp-equal (union-equal x y) z)
         (and (subsetp-equal x z)
              (subsetp-equal y z)))
  :hints (("Goal" :in-theory (enable union-equal
                                     subsetp-equal
                                     add-to-set-equal))))

(defthm subsetp-equal-of-remove-equal2
  (implies (subsetp-equal x y)
           (subsetp-equal (remove-equal a x) y))
  :hints (("Goal" :in-theory (enable subsetp-equal remove-equal))))


;; Disabled because it might be slow, so we include a cheap version below.
(defthmd subsetp-equal-when-subsetp-equal-of-cdr
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthmd subsetp-equal-when-subsetp-equal-of-cdr-cheap
  (implies (subsetp-equal x (cdr y))
           (subsetp-equal x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-self
  (subsetp-equal x x)
  :hints (("Goal" :in-theory (enable subsetp-equal
                                     subsetp-equal-when-subsetp-equal-of-cdr))))

(defthm subsetp-equal-of-cons-same
  (subsetp-equal clauses (cons fact clauses))
  :hints (("Goal" :in-theory (enable subsetp-equal
                                     subsetp-equal-when-subsetp-equal-of-cdr))))


;todo: this must be proved somewhere else
(defthm subsetp-equal-transitive
  (implies (and (subsetp-equal x y)
                (subsetp-equal y z))
           (subsetp-equal x z))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-transitive-2
  (implies (and (subsetp-equal y z) ;y is a free var
                (subsetp-equal x y))
           (subsetp-equal x z))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-cdr-arg1
  (implies (subsetp-equal x y)
           (subsetp-equal (cdr x) y))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-not-consp-1
  (implies (not (consp x))
           (equal (subsetp-equal x y)
                  t))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-when-not-consp-2
  (implies (not (consp y))
           (equal (subsetp-equal x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-true-list-fix
  (equal (subsetp-equal x (true-list-fix y))
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable subsetp-equal true-list-fix))))

(defthm subsetp-equal-of-append-2-1
  (implies (subsetp-equal x z)
           (subsetp-equal x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

(defthm subsetp-equal-of-append-2-2
  (implies (subsetp-equal x y)
           (subsetp-equal x (append y z)))
  :hints (("Goal" :in-theory (enable append subsetp-equal))))

(defthm subsetp-equal-of-cons-arg2
  (implies (and (syntaxp (not (and (quotep a)
                                   (quotep y))))
                (subsetp-equal x y))
           (subsetp-equal x (cons a y))))
