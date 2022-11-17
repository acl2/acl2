; Randomizing the order of the elements in a list
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also shuffle-list2.lisp.

(include-book "shuffle-array-stobj")

;; Returns (mv shuffled-list state).  Returning state may be necessary for soundness.
(defun shuffle-list (list state)
  (declare (xargs :guard (true-listp list)
                  :stobjs state))
  (with-local-stobj
    array-stobj
    (mv-let (shuffled-list array-stobj state)
      (let ((array-stobj (load-list-into-array-stobj list array-stobj)))
        (mv-let (array-stobj state)
          (shuffle-array-stobj array-stobj state)
          (mv (extract-list-from-array-stobj array-stobj) array-stobj state)))
      (mv shuffled-list state))))
