; A lightweight book about the built-in function string-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable string-listp))

;; Matches the on in std/
(defthm string-listp-of-append
  (equal (string-listp (append a b))
         (and (string-listp (true-list-fix a))
              (string-listp b)))
  :hints (("Goal" :in-theory (enable string-listp append))))

(defthm string-listp-of-cons
  (equal (string-listp (cons a x))
         (and (stringp a)
              (string-listp x)))
  :hints (("Goal" :in-theory (enable string-listp))))

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
