; A variant scheme for handling "run-until-return"
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; New, experimental scheme (this scheme doesn't work for certain 32-bit PE
;; malware, which increments the stack pointer by 8 instead of 4 as expected
;; for 32-bit):

;TODO: Use x86isa package?

(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute
(include-book "misc/defpun" :dir :system)
(include-book "readers-and-writers64") ; todo: make a separate version for 32-bit that uses eip

(defpun run-until-rsp-is (rsp x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (equal rsp (xr :rgf *rsp* x86)) ; todo: which expression to use here?
      x86
    (run-until-rsp-is rsp (x86-fetch-decode-execute x86))))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-base
  (implies (equal rsp (xr :rgf *rsp* x86))
           (equal (run-until-rsp-is rsp x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-opener
  (implies (not (equal rsp (xr :rgf *rsp* x86)))
           (equal (run-until-rsp-is rsp x86)
                  (run-until-rsp-is rsp (x86-fetch-decode-execute x86)))))

(defthm run-until-rsp-is-of-if-arg2
  (equal (run-until-rsp-is rsp (if test x86a x86b))
         (if test
             (run-until-rsp-is rsp x86a)
           (run-until-rsp-is rsp x86b))))

;; In this version, we run until RSP it exactly 8 more than the original (the
;; stack has shrunk by one slot).
(defund-nx run-until-return64 (x86)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is (+ 8 (xr :rgf *rsp* x86)) x86))

;; In this version, we run until RSP it exactly 4 more than the original (the
;; stack has shrunk by one slot).
(defund-nx run-until-return32 (x86)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is (+ 4 (xr :rgf *rsp* x86)) x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-rsp-is-or-reach-pc (rsp stop-pcs x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (or (equal rsp (xr :rgf *rsp* x86))
          (member-equal (rip x86) stop-pcs))
      x86
    (run-until-rsp-is-or-reach-pc rsp stop-pcs (x86-fetch-decode-execute x86))))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-or-reach-pc-base
  (implies (or (equal rsp (xr :rgf *rsp* x86))
               (member-equal (rip x86) stop-pcs))
           (equal (run-until-rsp-is-or-reach-pc rsp stop-pcs x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-or-reach-pc-opener
  (implies (and (not (equal rsp (xr :rgf *rsp* x86)))
                (not (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-or-reach-pc rsp stop-pcs x86)
                  (run-until-rsp-is-or-reach-pc rsp stop-pcs (x86-fetch-decode-execute x86)))))

(defthm run-until-rsp-is-or-reach-pc-of-if-arg2
  (equal (run-until-rsp-is-or-reach-pc rsp stop-pcs (if test x86a x86b))
         (if test
             (run-until-rsp-is-or-reach-pc rsp stop-pcs x86a)
           (run-until-rsp-is-or-reach-pc rsp stop-pcs x86b))))

(defund-nx run-until-return-or-reach-pc64 (stop-pcs x86)
;; TODO: Try to use defun here (but may need a stobj declare on run-until-rsp-is-or-reach-pc)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is-or-reach-pc (+ 8 (xr :rgf *rsp* x86)) stop-pcs x86))

(defund-nx run-until-return-or-reach-pc32 (stop-pcs x86)
;; TODO: Try to use defun here (but may need a stobj declare on run-until-rsp-is-or-reach-pc)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is-or-reach-pc (+ 4 (xr :rgf *rsp* x86)) stop-pcs x86))
