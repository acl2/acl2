; Axe rules about lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; combine with list-rules-axe?

(include-book "axe-syntax")
(include-book "std/lists/list-defuns" :dir :system) ;for prefixp
(local (include-book "kestrel/lists-light/prefixp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(defthm equal-of-prefixp-and-equal-work-hard
  (implies (and (work-hard (equal (len x) (len y)))
                (work-hard (true-listp x))
                (work-hard (true-listp y)))
           (equal (equal (prefixp x y) (equal x y))
                  t))
  :hints (("Goal" :in-theory (enable prefixp list-equiv))))

(defthmd equal-of-equal-and-prefixp-work-hard
  (implies (and (work-hard (equal (len x) (len y)))
                (work-hard (true-listp x))
                (work-hard (true-listp y)))
           (equal (equal (equal x y) (prefixp x y))
                  t))
  :hints (("Goal" :in-theory (enable prefixp list-equiv))))

(defthm equal-of-prefixp-and-equal-work-hard-alt
  (implies (and (work-hard (equal (len x) (len y)))
                (work-hard (true-listp x))
                (work-hard (true-listp y)))
           (equal (equal (prefixp x y) (equal y x))
                  t))
  :hints (("Goal" :in-theory (enable prefixp list-equiv))))

(defthmd equal-of-equal-and-prefixp-work-hard-alt
  (implies (and (work-hard (equal (len x) (len y)))
                (work-hard (true-listp x))
                (work-hard (true-listp y)))
           (equal (equal (equal x y) (prefixp y x))
                  t))
  :hints (("Goal" :in-theory (enable prefixp list-equiv))))
