; Randomizing the order of the elements in an array
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "array-stobj")

;; See also shuffle-array-stobj2.lisp

;; (local (in-theory (disable mv-nth)))

(local (in-theory (enable random$))) ;todo: or make/use a book about it

;; A Fisher-Yates shuffle
;; Returns (mv array-stobj state).
(defun shuffle-array-stobj-aux (i array-stobj state)
  (declare (xargs :guard (and (integerp i)
                              (< i (elems-length array-stobj)))
                  :measure (nfix (+ 1 i))
                  :stobjs (array-stobj state)))
  (if (or (not (mbt (integerp i)))
          (<= i 0) ; does nothing when just 1 element is left
          )
      (mv array-stobj state)
    ;; Choose a random element with index in [0,i] to be element i in the result:
    (mv-let (other-index state)
      (random$ (+ 1 i) state)
      (let* ((other-element (elemsi other-index array-stobj))
             (i-element (elemsi i array-stobj))
             ;; Swap element i and the other element:
             (array-stobj (update-elemsi i other-element array-stobj))
             (array-stobj (update-elemsi other-index i-element array-stobj)))
        (shuffle-array-stobj-aux (+ -1 i) array-stobj state)))))

;; I had used with-local-state here, which requires a ttag, but that was unsound.
;; Returns (mv array-stobj state).
(defun shuffle-array-stobj (array-stobj state)
  (declare (xargs :stobjs (array-stobj state)))
  (shuffle-array-stobj-aux (+ -1 (elems-length array-stobj)) array-stobj state))
