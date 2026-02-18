; A new scheme for handling "run-until-return" (32-bit mode)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; New, experimental scheme, aiming to use unsigned vals and be BV compatible.

(include-book "projects/x86isa/machine/x86" :dir :system) ; for x86-fetch-decode-execute
(include-book "misc/defpun" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "register-readers-and-writers32") ; for esp
(include-book "readers-and-writers64") ; todo: make a separate version for 32-bit that uses eip
(include-book "kestrel/lists-light/memberp" :dir :system)

;; Tests whether the stack pointer is "above" OLD-ESP.  For now, we define
;; "above" as "not closely below".  Recall that the stack grows downward, so a
;; larger ESP means a shorter stack.
(defund esp-is-abovep (old-esp x86)
  (declare (xargs :guard (unsigned-byte-p 32 old-esp)
                  :stobjs x86))
  (bvlt 32 2147483648 ; 2^31
        (bvminus 32 old-esp (esp x86))
        ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-esp-is-above (old-esp x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (esp-is-abovep old-esp x86)
      x86
    (run-until-esp-is-above old-esp (x86-fetch-decode-execute x86))))

;; This is the non-Axe rule
(defthm run-until-esp-is-above-base
  (implies (and (syntaxp (not (and (consp x86) (eq 'if (ffn-symb x86)))))
                (esp-is-abovep old-esp x86))
           (equal (run-until-esp-is-above old-esp x86)
                  x86)))

;; This is the non-Axe rule
(defthm run-until-esp-is-above-opener
  (implies (and (syntaxp (not (and (consp x86) (eq 'if (ffn-symb x86)))))
                (not (esp-is-abovep old-esp x86)))
           (equal (run-until-esp-is-above old-esp x86)
                  (run-until-esp-is-above old-esp (x86-fetch-decode-execute x86)))))

(defthm run-until-esp-is-above-of-if-arg2
  (equal (run-until-esp-is-above old-esp (if test x86a x86b))
         (if test
             (run-until-esp-is-above old-esp x86a)
           (run-until-esp-is-above old-esp x86b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Try to use defun here (but may need a stobj declare on run-until-esp-is-above)
(defund-nx run-until-return32 (x86)
  (declare (xargs :stobjs x86))
  (run-until-esp-is-above (esp x86) x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For debugging, or lifting just a segment of code

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-esp-is-above-or-reach-pc (old-esp stop-pcs x86)
  ;;  (declare (xargs :stobjs x86)) ;TODO: This didn't work
  (if (or (esp-is-abovep old-esp x86)
          (memberp (eip x86) stop-pcs))
      x86
    (run-until-esp-is-above-or-reach-pc old-esp stop-pcs (x86-fetch-decode-execute x86))))

;; This is the non-Axe rule
(defthm run-until-esp-is-above-or-reach-pc-base
  (implies (and (syntaxp (not (and (consp x86) (eq 'if (ffn-symb x86)))))
                (or (esp-is-abovep old-esp x86)
                    (memberp (eip x86) stop-pcs)))
           (equal (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86)
                  x86)))

;; This is the non-Axe rule
(defthm run-until-esp-is-above-or-reach-pc-opener
  (implies (and (syntaxp (not (and (consp x86) (eq 'if (ffn-symb x86)))))
                (not (or (esp-is-abovep old-esp x86)
                         (memberp (eip x86) stop-pcs))))
           (equal (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86)
                  (run-until-esp-is-above-or-reach-pc old-esp stop-pcs (x86-fetch-decode-execute x86)))))

(defthm run-until-esp-is-above-or-reach-pc-of-if-arg2
  (equal (run-until-esp-is-above-or-reach-pc old-esp stop-pcs (if test x86a x86b))
         (if test
             (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86a)
           (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86b))))

(defund-nx run-until-return-or-reach-pc32 (stop-pcs x86)
;; TODO: Try to use defun here (but may need a stobj declare on run-until-esp-is-above-or-reach-pc)
  (declare (xargs :stobjs x86))
  (run-until-esp-is-above-or-reach-pc (esp x86) stop-pcs x86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;mixes abstractions.  may not be needed once we can enable acl2::bvminus-of-+-arg3
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (defthm acl2::bvminus-of-+-cancel-arg3
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (bvminus size x (binary-+ y x))
;;                   (bvuminus size y)))
;;   :hints (("Goal" :in-theory (enable bvminus bvuminus))))
