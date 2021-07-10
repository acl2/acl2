; Axe rules about group
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

(include-book "axe-syntax") ;for work-hard
(include-book "kestrel/lists-light/group-rules" :dir :system)
(local (include-book "kestrel/lists-light/take" :dir :system))

(defthmd nth-when-equal-of-firstn-hack
  (implies (and (equal (group 16 k) (firstn m x))
                (work-hard (< n m))
                (natp n)
                (natp m))
           (equal (nth n x)
                  (FIRSTN 16 (NTHCDR (* N 16) K))))
  :hints (("Goal" :use (:instance nth-when-equal-of-firstn (free (group 16 k))))))

(defthmd nth-when-equal-of-firstn-hack-alt
  (implies (and (equal (firstn m x) (group 16 k))
                (work-hard (< n m))
                (natp n)
                (natp m))
           (equal (nth n x)
                  (FIRSTN 16 (NTHCDR (* N 16) K))))
  :hints (("Goal" :use (:instance nth-when-equal-of-firstn-hack)
           :in-theory (disable nth-when-equal-of-firstn-hack))))
