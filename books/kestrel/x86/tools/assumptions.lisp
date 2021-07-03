; Assumptions for x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/state" :dir :system)

;; Assumptions that are common to 32-bit and 64-bit mode.
(defun standard-state-assumption (x86)
  (declare (xargs :stobjs x86))
  (and ;; The x86 state is well-formed:
   (x86p x86)

   ;; The model is operating in the application view (ignore paging):
   (equal (app-view x86) t) ;todo: get rid of the (equal ... t) wrapper (may need to improve the rewriter)

   ;; The initial state is error-free:
   (equal (ms x86) nil)
   (equal (x86isa::fault x86) nil)))

;; A lifter target is a numeric offset, the name of a subroutine (a string), or the symbol :entry-point.
(defun lifter-targetp (target)
  (or (natp target)
      (stringp target)
      (eq :entry-point target)))
