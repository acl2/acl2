; Support for run-until-return, etc.
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

(include-book "kestrel/arm/step" :dir :system)
(include-book "portcullis") ; for the package
(local (include-book "kestrel/alists-light/acons" :dir :system))

(defstub error-wrapper (* *) => *)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To determine when to stop symbolic execution, we track the implicit stack
;; height, relative to the start of the symbolic execution.  Calls increase the
;; height and returns decrease it.  We stop symbolic execution when the
;; relative height goes negative.

;; (defstub stub (x) t)
;; (defstub stub2 (x y) t)
(local (in-theory (disable alistp)))

;; (thm
;;   (integerp (lookup-equal 'arm::register_list (mv-nth 2 (arm32-decode instr))))
;;   :hints (("Goal" :in-theory (enable arm32-decode))))

;; Adjustmust to the stack height for instr (+ 1 for call, -1 for return)
;; todo: speed this up
(defund stack-height-adjustment (instr)
  (declare (xargs :guard (and (unsigned-byte-p 32 instr) ; todo: use a recognizer
                              )
                  :guard-hints (("Goal" :in-theory (enable arm32-decode)))))
  (mv-let (erp mnemonic args) ;; where ARGS is an alist from field names
    (arm::arm32-decode instr)
    (if erp
        (ifix (error-wrapper "Can't decode instr." instr))
      (case mnemonic
        (:bl ; todo: blx
         ;; We consider every BL to be a subroutine call since it saves the return address in the LR
         1)
        ;; TODO: Add checks.  For now, we assume every BX is a return
        ;; TODO: Add support for other return idioms, including moving to the PC and
        ;; popping values into a register set that includes the PC is a return:
        ((:pop-encoding-a1 :ldm/ldmia/ldmfd)
         (if (equal 1 (getbit *pc* (lookup-eq 'arm::register_list args)))
             -1
           0))
        ;; This is a return (todo: what if the register is not LR?):
        (:bx -1)
        (otherwise 0)))))

;; This is separate so we can prevent opening it when INSTR is not a constant.
(defund update-call-stack-height-aux (instr call-stack-height arm)
  (declare (xargs :guard (and (unsigned-byte-p 32 instr) ; todo: use a recognizer
                              (integerp call-stack-height))
                  :stobjs arm))
  (if (not (equal *InstrSet_ARM* (isetstate arm)))
      :not-in-arm-state
    (+ (stack-height-adjustment instr) call-stack-height)))

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
         (maybe-library-function (acl2::lookup pc (library-map arm))))
    (if maybe-library-function
        ;; if this is the first instr of a library function, the model of that
        ;; function will include returning from the stack frame:
        (+ -1 call-stack-height)
      (let ((instr (read 4 pc arm)))
        (update-call-stack-height-aux instr call-stack-height arm)))))
