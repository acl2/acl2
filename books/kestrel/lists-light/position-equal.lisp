; A lightweight book about the built-in-function position-equal
;
; Copyright (C) 2015-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "position-equal-ac"))

;; Note that position-equal handles both strings and lists.  It has a formal
;; called LST, but since that formal can be a string (!), we use X here
;; instead.

(in-theory (disable position-equal))

(defthm integerp-of-position-equal-under-iff
  (iff (integerp (position-equal item x))
       (if (stringp x)
           (member-equal item (coerce x 'list))
         (member-equal item x)))
  :hints (("Goal" :in-theory (enable member-equal position-equal))))

(defthm natp-of-position-equal-under-iff
  (iff (natp (position-equal item x))
       (if (stringp x)
           (member-equal item (coerce x 'list))
         (member-equal item x)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable member-equal position-equal))))

(defthm position-equal-under-iff
  (iff (position-equal item x)
       (if (stringp x)
           (member-equal item (coerce x 'list))
         (member-equal item x)))
  :hints (("Goal" :in-theory (enable position-equal))))

;; For when X is a string.
(defthm <-of-position-equal-and-length-linear
  (implies (and (stringp x)
                (position-equal item x) ; rephrase?
                )
           (< (position-equal item x) (length x)))
  :rule-classes ((:linear :trigger-terms ((position-equal item x))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst (coerce x 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when X is a string.
(defthm <-of-position-equal-and-length
  (implies (stringp x)
           (equal (< (position-equal item x) (length x))
                  (if (position-equal item x) ; rephrase?
                      t
                    (< 0 (length x)) ; or (not (equal "" x))
                    )))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst (coerce x 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when X is a list.
(defthm <-of-position-equal-and-len-linear
  (implies (and (not (stringp x))
                (member-equal item x))
           (< (position-equal item x) (len x)))
  :rule-classes ((:linear :trigger-terms ((position-equal item x))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst x))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when X is a list.
(defthm <-of-position-equal-and-len
  (implies (not (stringp x))
           (equal (< (position-equal item x) (len x))
                  (if (member-equal item x)
                      t
                    (consp x))))
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst x))
           :expand (len x)
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

;; For when X is a list
(defthm position-equal-when-not-member-equal
  (implies (and (not (stringp x))
                (not (member-equal item x)))
           (equal (position-equal item x)
                  nil))
  :hints (("Goal" :in-theory (enable position-equal))))
