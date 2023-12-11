; The run-until-return function for x86
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;TODO: Use x86isa package?

(include-book "projects/x86isa/machine/x86" :dir :system)
(include-book "misc/defpun" :dir :system)

;; An alias that's in the x86isa package
(defmacro defpun (&rest args)
  `(acl2::defpun ,@args))

;; Tests whether the stack is shorter than it was when the RSP was OLD-RSP.  Recall
;; that the stack grows downward, so a larger RSP means a shorter stack.
(defun stack-shorter-thanp (old-rsp x86)
  (declare (xargs :stobjs x86
                  :guard (natp old-rsp))) ;tighten?
  (> (rgfi *rsp* x86)
     old-rsp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-stack-shorter-than (old-rsp x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (stack-shorter-thanp old-rsp x86)
      x86
    (run-until-stack-shorter-than old-rsp (x86-fetch-decode-execute x86))))

(defthm run-until-stack-shorter-than-base
  (implies (stack-shorter-thanp old-rsp x86)
           (equal (run-until-stack-shorter-than old-rsp x86)
                  x86)))

(defthm run-until-stack-shorter-than-opener
  (implies (not (stack-shorter-thanp old-rsp x86))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  (run-until-stack-shorter-than old-rsp (x86-fetch-decode-execute x86)))))

(defthm run-until-stack-shorter-than-of-if-arg2
  (equal (run-until-stack-shorter-than old-rsp (if test x86a x86b))
         (if test
             (run-until-stack-shorter-than old-rsp x86a)
           (run-until-stack-shorter-than old-rsp x86b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Try to use defun here (but may need a stobj declare on run-until-stack-shorter-than)
(defund-nx run-until-return (x86)
  (declare (xargs :stobjs x86))
  (run-until-stack-shorter-than (xr :rgf *rsp* x86) x86))
