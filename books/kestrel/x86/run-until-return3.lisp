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

;; New, experimental scheme, aiming to use unsigned vals and be BV compatible.

(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute
(include-book "register-readers-and-writers64") ; for RSP
(include-book "misc/defpun" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)

;; Tests whether the stack pointer is "above" OLD-RSP.  For now, we define
;; "above" as "not closely below".  Recall that the stack grows downward, so a
;; larger RSP means a shorter stack.
(defund rsp-is-abovep (old-rsp x86)
  (declare (xargs :guard (signed-byte-p 64 old-rsp) ; todo: update to unsigned soon
                  :stobjs x86))
  (bvlt 64 2147483648 ; 2^31 ; todo: consider 32-bit and 64-bit
        (bvminus 64 old-rsp (rsp x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-rsp-is-above (old-rsp x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (rsp-is-abovep old-rsp x86)
      x86
    (run-until-rsp-is-above old-rsp (x86-fetch-decode-execute x86))))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-above-base
  (implies (rsp-is-abovep old-rsp x86)
           (equal (run-until-rsp-is-above old-rsp x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-above-opener
  (implies (not (rsp-is-abovep old-rsp x86))
           (equal (run-until-rsp-is-above old-rsp x86)
                  (run-until-rsp-is-above old-rsp (x86-fetch-decode-execute x86)))))

(defthm run-until-rsp-is-above-of-if-arg2
  (equal (run-until-rsp-is-above old-rsp (if test x86a x86b))
         (if test
             (run-until-rsp-is-above old-rsp x86a)
           (run-until-rsp-is-above old-rsp x86b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Try to use defun here (but may need a stobj declare on run-until-rsp-is-above)
(defund-nx run-until-return3 (x86)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is-above (rsp x86) x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For debugging, or lifting just a segment of code

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-rsp-is-above-or-reach-pc (old-rsp stop-pcs x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (or (rsp-is-abovep old-rsp x86)
          (member-equal (rip x86) stop-pcs))
      x86
    (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86))))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-above-or-reach-pc-base
  (implies (or (rsp-is-abovep old-rsp x86)
               (member-equal (rip x86) stop-pcs))
           (equal (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86)
                  x86)))

;; todo: restrict to when x86 is not an IF/MYIF
(defthm run-until-rsp-is-above-or-reach-pc-opener
  (implies (not (or (rsp-is-abovep old-rsp x86)
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86)
                  (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86)))))

(defthm run-until-rsp-is-above-or-reach-pc-of-if-arg2
  (equal (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs (if test x86a x86b))
         (if test
             (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86a)
           (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86b))))

(defund-nx run-until-return-or-reach-pc3 (stop-pcs x86)
;; TODO: Try to use defun here (but may need a stobj declare on run-until-rsp-is-above-or-reach-pc)
  (declare (xargs :stobjs x86))
  (run-until-rsp-is-above-or-reach-pc (rsp x86) stop-pcs x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;mixes abstractions.  may not be needed once we can enable acl2::bvminus-of-+-arg3
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(defthm acl2::bvminus-of-+-cancel-arg3
  (implies (and (integerp x)
                (integerp y))
           (equal (bvminus size x (binary-+ y x))
                  (bvuminus size y)))
  :hints (("Goal" :in-theory (enable bvminus bvuminus))))
