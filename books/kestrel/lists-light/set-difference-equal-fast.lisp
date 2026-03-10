; A fast variant of set-difference-eq
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is fast when the second argument is empty.
(defund set-difference-equal-fast (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (if (endp l2)
      ;; special case where there is nothing to remove:
      (mbe :logic (true-list-fix l1) :exec l1)
    (set-difference-equal l1 l2)))

;; We intend to keep this enabled, to get rid of set-difference-equal-fast.
(defthm set-difference-equal-fast-becomes-set-difference-equal
  (equal (set-difference-equal-fast l1 l2)
         (set-difference-equal l1 l2))
  :hints (("Goal" :in-theory (enable set-difference-equal-fast set-difference-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is fast when the second argument is empty.
;; We intend to keep this enabled, to expose set-difference-equal.
(defun set-difference-eq-fast (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (or (symbol-listp l1)
                                  (symbol-listp l2)))))
  (mbe :logic (set-difference-equal l1 l2)
       :exec (if (endp l2)
                 l1 ; special case where there is nothing to remove
               (set-difference-eq l1 l2))))
