; Rules about group and ungroup
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ungroup")
(include-book "group")
(local (include-book "len"))
(local (include-book "nthcdr"))
(local (include-book "cdr"))
(local (include-book "cons"))
(local (include-book "append"))
(local (include-book "firstn"))
(local (include-book "take"))
(local (include-book "true-list-fix"))

(defthm group-of-ungroup-same
  (implies (and (items-have-len n x)
                (posp n)
                (true-listp x)
                (all-true-listp x)
                )
           (equal (group n (ungroup n x))
                  x))
  :hints (("Goal" :in-theory (enable ungroup))))
