; A function to add an item to the end of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the function rcons in std/lists/rcons.

;maybe this should always be expanded?
(defun add-to-end (item lst)
  (declare (xargs :guard (true-listp lst)))
  (append lst (list item)))

(defthm true-listp-of-add-to-end
  (true-listp (add-to-end a x)))

(defthm len-of-add-to-end
  (equal (len (add-to-end a x))
         (+ 1 (len x)))
  :hints (("Goal" :in-theory (enable add-to-end))))
