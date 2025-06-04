; The run-until-return function for x86
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;TODO: Use x86isa package?

(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute
(include-book "misc/defpun" :dir :system)

;; Tests whether the stack is shorter than it was when the RSP was OLD-RSP.  Recall
;; that the stack grows downward, so a larger RSP means a shorter stack.
(defun stack-shorter-thanp (old-rsp x86)
  (declare (xargs :stobjs x86
                  :guard (natp old-rsp))) ;tighten? ; todo: this is actually a signed-byte 64?!  we can use > because the canonical block is contiguous using a signed-byte 64 representation
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

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-stack-shorter-than-base
  (implies (stack-shorter-thanp old-rsp x86)
           (equal (run-until-stack-shorter-than old-rsp x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For debugging, or lifting just a segment of code

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-stack-shorter-than-or-reach-pc (old-rsp stop-pcs x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (or (stack-shorter-thanp old-rsp x86)
          (member-equal (rip x86) stop-pcs))
      x86
    (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86))))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-stack-shorter-than-or-reach-pc-base
  (implies (or (stack-shorter-thanp old-rsp x86)
               (member-equal (rip x86) stop-pcs))
           (equal (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-stack-shorter-than-or-reach-pc-opener
  (implies (not (or (stack-shorter-thanp old-rsp x86)
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86)
                  (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86)))))

(defthm run-until-stack-shorter-than-or-reach-pc-of-if-arg2
  (equal (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs (if test x86a x86b))
         (if test
             (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86a)
           (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86b))))

(defund-nx run-until-return-or-reach-pc (stop-pcs x86)
;; TODO: Try to use defun here (but may need a stobj declare on run-until-stack-shorter-than-or-reach-pc)
  (declare (xargs :stobjs x86))
  (run-until-stack-shorter-than-or-reach-pc (xr :rgf *rsp* x86) stop-pcs x86))
