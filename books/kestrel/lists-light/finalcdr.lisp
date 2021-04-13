; Return the final "cdr" (an atom) of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns the atom that is obtained in the last step of cdring down the list
;; x. This will be nil iff x is a true-list.
(defun finalcdr (x)
  (declare (xargs :guard t))
  (if (consp x)
      (finalcdr (cdr x))
    x))

(defthm finalcdr-iff
  (iff (finalcdr x)
       (not (true-listp x)))
  :hints (("Goal" :in-theory (enable true-listp finalcdr))))

;name clash
(defthm len-of-finalcdr-2
  (equal (len (finalcdr x))
         0))

(defthm nthcdr-of-len-same
  (equal (nthcdr (len x) x)
         (finalcdr x)))

;where should this go?
(defthm equal-of-append-same
  (equal (equal x (append x y))
         (equal y (finalcdr x)))
  :hints (("Goal" :in-theory (enable))))
