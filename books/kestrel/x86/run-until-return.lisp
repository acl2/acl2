; The run-until-return function for x86
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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

;; Tests whether the stack is shorter than it was when the RSP was val.  Recall
;; that the stack grows downward, so large RSP mean shorter stacks.
(defun rsp-greater-than (val x86)
  (declare (xargs :stobjs x86
                  :guard (natp val))) ;tighten?
  (> (rgfi *rsp* x86)
     val))

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-rsp-greater-than (target-rsp x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (rsp-greater-than target-rsp x86)
      x86
    (run-until-rsp-greater-than target-rsp (x86-fetch-decode-execute x86))))

;; TODO: Try to use defun here (but may need a stobj declare on run-until-rsp-greater-than)
(defund-nx run-until-return (x86)
  (declare (xargs :stobjs x86))
  (run-until-rsp-greater-than (xr :rgf *rsp* x86) x86))

(defthm run-until-rsp-greater-than-base
  (implies (rsp-greater-than target-rsp x86)
           (equal (run-until-rsp-greater-than target-rsp x86)
                  x86)))

(defthm run-until-rsp-greater-than-opener
  (implies (not (rsp-greater-than target-rsp x86))
           (equal (run-until-rsp-greater-than target-rsp x86)
                  (run-until-rsp-greater-than target-rsp (x86-fetch-decode-execute x86)))))
