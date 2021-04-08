; A lightweight book about the built-in function remove-duplicates-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable remove-duplicates-equal))

(defthm member-equal-of-remove-duplicates-equal-iff
  (iff (member-equal a (remove-duplicates-equal x))
       (member-equal a x))
  :hints (("Goal" :in-theory (enable remove-duplicates-equal))))

(defthm no-duplicatesp-equal-of-remove-duplicates-equal
  (no-duplicatesp-equal (remove-duplicates-equal x))
  :hints (("Goal" :in-theory (enable remove-duplicates-equal
                                     no-duplicatesp-equal))))
