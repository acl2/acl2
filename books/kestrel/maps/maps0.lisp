; Additions to the records library
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Clean this up

(include-book "coi/records/records" :dir :system)  ;consider using the coi/records/domain stuff?

(defmacro empty-map () nil)

;used when we want to fail immediately if the indicated key isn't found;
;with plain old g, we'd return nil in such a case, which would cause a failure downstream (or perhaps a loop, which i've seen)
;fixme use this more
(defun g-safe (a x)
  (declare (type t a x))
  (let ((val (g a x)))
    (if val
        val
      (hard-error 'g-safe "Looking up the key ~x0 in the record ~x1 failed." (acons #\0 a (acons #\1 x nil))))))
