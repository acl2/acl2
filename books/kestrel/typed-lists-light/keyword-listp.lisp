; A lightweight book about the build-in function keyword-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm keyword-listp-of-append
  (equal (keyword-listp (append x y))
         (and (keyword-listp (true-list-fix x))
              (keyword-listp y)))
  :hints (("Goal" :in-theory (enable TRUE-LIST-FIX))))

(defthm keyword-listp-of-true-list-fix
  (implies (keyword-listp x)
           (keyword-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm keyword-listp-of-remove-duplicates-equal
  (equal (keyword-listp (remove-duplicates-equal x))
         (keyword-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable remove-duplicates-equal true-list-fix))))
