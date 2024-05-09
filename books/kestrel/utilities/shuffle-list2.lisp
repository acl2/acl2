; Randomizing the order of the elements in a list
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also shuffle-list.lisp.

(include-book "shuffle-array-stobj2")

(local (in-theory (disable elems-length)))

;; Returns the shuffled-list.
(defun shuffle-list2 (list seed)
  (declare (xargs :guard (and (true-listp list)
                              (<= (len list) *m31*)
                              (minstd-rand0p seed))))
  (with-local-stobj
    array-stobj
    (mv-let (shuffled-list array-stobj)
      (let ((array-stobj (load-list-into-array-stobj list array-stobj)))
        (let ((array-stobj (shuffle-array-stobj2 seed array-stobj)))
          (mv (extract-list-from-array-stobj array-stobj) array-stobj)))
      shuffled-list)))
