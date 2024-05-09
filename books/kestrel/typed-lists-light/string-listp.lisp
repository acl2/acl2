; A lightweight book about the built-in function string-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable string-listp))

;; Matches the one in std/
(defthm string-listp-of-append
  (equal (string-listp (append a b))
         (and (string-listp (true-list-fix a))
              (string-listp b)))
  :hints (("Goal" :in-theory (enable string-listp append))))

;; Tweaked to match the one in std.
(defthm string-listp-of-revappend
  (equal (string-listp (revappend x y))
         (and (string-listp (true-list-fix x))
              (string-listp y)))
  :hints (("Goal" :in-theory (enable string-listp revappend))))

(defthm string-listp-of-cons
  (equal (string-listp (cons a x))
         (and (stringp a)
              (string-listp x)))
  :hints (("Goal" :in-theory (enable string-listp))))

;; The non-standard param names are to match the rule in std.
(defthm string-listp-of-remove-equal
  (implies (string-listp x)
           (string-listp (remove-equal a x)))
  :hints (("Goal" :in-theory (enable string-listp))))

(defthm string-listp-of-remove-duplicates-equal-simple
  (implies (string-listp l)
           (string-listp (remove-duplicates-equal l)))
  :hints (("Goal" :in-theory (enable string-listp remove-duplicates-equal))))

;; The non-standard param name X here is to match the rule in std.
(defthm string-listp-of-remove-duplicates-equal
  (equal (string-listp (remove-duplicates-equal x))
         (string-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable string-listp remove-duplicates-equal))))

(defthm string-listp-forward-to-true-listp
  (implies (string-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable string-listp))))

;; Kept disabled by default, to avoid introducing string-listp reasoning into a
;; proof out of nowhere.
(defthmd true-listp-when-string-listp
  (implies (string-listp x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable string-listp))))
