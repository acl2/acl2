; Randomizing the order of the elements in an array
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also shuffle-array-stobj.lisp

(include-book "array-stobj")
(include-book "kestrel/random/minstd-rand0" :dir :system)

;; (local (in-theory (disable mv-nth)))

;; A Fisher-Yates shuffle
;; Returns the array-stobj.
(defun shuffle-array-stobj2-aux (i rand array-stobj)
  (declare (xargs :guard (and (integerp i)
                              (< i (elems-length array-stobj))
                              (<= (elems-length array-stobj) *m31*)
                              (minstd-rand0p rand))
                  :measure (nfix (+ 1 i))
                  :stobjs array-stobj))
  (if (or (not (mbt (integerp i)))
          (<= i 0) ; does nothing when just 1 element is left
          )
      array-stobj
    ;; Choose a random element with index in [0,i] to be element i in the result:
    (mv-let (other-index rand)
      (extract-bounded-val-using-minstd-rand0 i rand)
      (let* ((other-element (elemsi other-index array-stobj))
             (i-element (elemsi i array-stobj))
             ;; Swap element i and the other element:
             (array-stobj (update-elemsi i other-element array-stobj))
             (array-stobj (update-elemsi other-index i-element array-stobj)))
        (shuffle-array-stobj2-aux (+ -1 i) rand array-stobj)))))

;; Returns the array-stobj.
(defun shuffle-array-stobj2 (seed array-stobj)
  (declare (xargs :guard (and (minstd-rand0p seed)
                              (<= (elems-length array-stobj) *m31*))
                  :stobjs (array-stobj)))
  (shuffle-array-stobj2-aux (+ -1 (elems-length array-stobj)) seed array-stobj))
