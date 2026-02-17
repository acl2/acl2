; Running until we return from a function
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

(include-book "portcullis")
(include-book "kestrel/arm/step" :dir :system)
;(include-book "registers") ; for SP
;(include-book "pc")
;(include-book "read-and-write")
(include-book "misc/defpun" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)

(defstub error-wrapper (* * arm) => *)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To determine when to stop symbolic execution, we track the implicit stack
;; height, relative to the start of the symbolic execution.  Calls increase the
;; height and returns decrease it.  We stop symbolic execution when the
;; relative height goes negative.

;; This is separate so we can prevent opening it when INSTR is not a constant.
(defund update-call-stack-height-aux (instr call-stack-height arm)
  (declare (xargs :guard (and (unsigned-byte-p 32 instr) ; todo: use a recognizer
                              (integerp call-stack-height))
                  :stobjs arm))
  (mv-let (erp mnemonic args) ;; where ARGS is an alist from field names
      (arm::arm32-decode instr)
    (declare (ignore args)) ; for now
    (if erp
        (error-wrapper "Can't decode instr." instr arm)
      (case mnemonic
        (:bl ; todo: blx
         ;; We consider every BL to be a subroutine call since it saves the return address in the LR
         (+ 1 call-stack-height))
        ;; TODO: Add checks.  For now, we assume every BX is a return
        ;; TODO: Add suport for other return idioms, including moving to the PC and popping values into a register set that includes the PC
        (:bx
         (+ -1 call-stack-height))
        (otherwise call-stack-height)))))

;; Open only when we can determine the instruction
(defopeners update-call-stack-height-aux :hyps ((syntaxp (quotep instr))))

(defthm update-call-stack-height-aux-of-if-arg1
  (equal (update-call-stack-height-aux (if test instr1 instr2) call-stack-height arm)
         (if test
             (update-call-stack-height-aux instr1 call-stack-height arm)
           (update-call-stack-height-aux instr2 call-stack-height arm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Increment on call, decrement on return
(defund update-call-stack-height (call-stack-height arm)
  (declare (xargs :guard (integerp call-stack-height)
                  :stobjs arm))
  (let* ((pc (pc arm))
         (instr (read 4 pc arm)))
    (update-call-stack-height-aux instr call-stack-height arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider stopping if the error field of the state is set.
;; It would be nice to support the :stobjs arm below, but it is
;; not very important, because a defpun is already non-executable.
(defpun run-until-return-aux (call-stack-height arm)
  ;; (declare (xargs :stobjs arm))
  (if (< call-stack-height 0)
      arm ; stop since we've returned from the function being lifted
    ;; Step the state and also update our tracked version of the call-stack-height:
    (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm))))

;; TODO: Can we prove this?
;; (thm
;;   (implies (armp arm)
;;            (armp (run-until-return-aux call-stack-height arm))))

;; todo: restrict to when arm is not an IF/MYIF
(defthm run-until-return-aux-base
  (implies (< call-stack-height 0)
           (equal (run-until-return-aux call-stack-height arm)
                  arm)))

;; todo: restrict to when arm is not an IF/MYIF
(defthm run-until-return-aux-opener
  (implies (not (< call-stack-height 0))
           (equal (run-until-return-aux call-stack-height arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm)))))

;; todo: add "smart" if handling, like we do elsewhere
(defthm run-until-return-aux-of-if-arg2
  (equal (run-until-return-aux call-stack-height (if test arma armb))
         (if test
             (run-until-return-aux call-stack-height arma)
           (run-until-return-aux call-stack-height armb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run until we return from the current function.
(defund run-until-return (arm)
  ;; (declare (xargs :stobjs arm))
  (run-until-return-aux
   0 ; initial call-stack-height
   arm))

(defund run-subroutine (arm)
  ;; (declare (xargs :stobjs arm))  ;; (declare (xargs :guard )) ; todo: need a property of the defpun
  ;; OLD: We start by stepping once.  This increases the stack height.  Then we run
  ;; until the stack height decreases again.  Finally, we step one more time to
  ;; do the RET.
  ;;(step32 (run-until-return (step32 arm)))
  (run-until-return arm))
