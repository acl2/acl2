; Utilities dealing with ruler-extenders
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/system/ruler-extenders" :dir :system)

;; Merges two values of :ruler-extenders args, conceptually giving the union of the two sets of ruler extenders.
;; Each argument is :basic, :lambdas, :all, or a list of symbols (possibly including :lambda)
(defun union-ruler-extenders (re1 re2)
  (if (or (eq :all re1)
          (eq :all re2))
      :all
    ;; de-sugar :lambdas and :basic:
    (let ((re1 (if (eq :lambdas re1) (cons ':lambdas *basic-ruler-extenders*) (if (eq :basic re1) *basic-ruler-extenders* re1)))
          (re2 (if (eq :lambdas re2) (cons ':lambdas *basic-ruler-extenders*) (if (eq :basic re2) *basic-ruler-extenders* re2))))
      (union-eq re1 re2))))

(defun union-ruler-extenders-of-fns-aux (fns wrld acc)
  (if (endp fns)
      acc
    (union-ruler-extenders-of-fns-aux (rest fns)
                                      wrld
                                      ;; TODO: ruler-extenders seems to de-sugar :basic and :lambdas
                                      ;; It would be better to use a variant of the function ruler-extenders that
                                      ;; gets the actual xarg.
                                      (union-ruler-extenders (ruler-extenders (first fns) wrld)
                                                             acc))))

;; Merge the :ruler-extender xargs for all the FNS in WRLD.
(defun union-ruler-extenders-of-fns (fns wrld)
  (union-ruler-extenders-of-fns-aux fns wrld nil))
