; Running until we return from a function
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "kestrel/risc-v/specialized/execution32" :dir :system)
(include-book "registers") ; for SP
(include-book "pc")
(include-book "read-and-write")
(include-book "misc/defpun" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)

;; ;; Tests whether the stack pointer is "above" OLD-SP.  For now, we define
;; ;; "above" as "not closely below".  Recall that the stack grows downward, so a
;; ;; larger SP means a shorter stack.
;; (defund sp-is-abovep (old-sp stat)
;;   (declare (xargs :guard (and (unsigned-byte-p 32 old-sp)
;;                               (stat32ip stat))))
;;   (bvlt 32 2147483648 ; 2^31
;;         (bvminus 32 old-sp (sp stat))))

;; (defund sp-is-belowp (old-sp stat)
;;   (declare (xargs :guard (and (unsigned-byte-p 32 old-sp)
;;                               (stat32ip stat))))
;;   (bvlt 32 2147483648 ; 2^31
;;         (bvminus 32 (sp stat) old-sp)))

(defconst *features*
  (riscv::make-feat
    :base (riscv::Feat-base-rv32i)
    :endian (riscv::Feat-endian-little)
    :m t ; whether the M extenion is present
    ))

(defstub error-wrapper (msg stat) t)


;; This is separate so we can prevent opening it when INSTR is not a constant
(defund update-call-stack-height-aux (instr call-stack-height stat)
  (declare (xargs :guard (and (unsigned-byte-p 32 instr)
                              (integerp call-stack-height)
                              (stat32ip stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte32p)))
                  ))
  (let ((decoded-instr (riscv::decodex instr *features*)))
    (riscv::instr-option-case
      decoded-instr
      :none (error-wrapper "Can't decode instr." stat)
      :some (riscv::instr-case
              decoded-instr.val
              (:jal
               (if (= 1 (riscv::instr-jal->rd decoded-instr.val))
                   ;; it's a jump that saves the addres in the RA register (register 1)
                   ;; so we consider this a push of a frame onto the stack and we
                   ;; expect this to be balanced later by a suitable JALR
                   (+ 1 call-stack-height)
                 ;; some other kind of jump:
                 call-stack-height))
              (:jalr
               ;; recognize a RET:
               (if (and (= 1 (riscv::instr-jalr->rs1 decoded-instr.val)) ; jump is to RA
                        (= 0 (riscv::instr-jalr->imm decoded-instr.val)) ; no offset from RA
                        (= 0 (riscv::instr-jalr->rd decoded-instr.val)) ; address not stored anywhere
                        )
                   (+ -1 call-stack-height)
                 ;; recognize a call:
                 (if (and ;; (= 1 (riscv::instr-jalr->rs1 decoded-instr.val)) ; jump is to RA  ; todo: can the address be both read from RA and stored in RA?
                       ;; (= 0 (riscv::instr-jalr->imm decoded-instr.val)) ; no offset from RA
                       (= 1 (riscv::instr-jalr->rd decoded-instr.val)) ; address stored in RA
                       )
                     (+ 1 call-stack-height)
                   ;; some other kind of jump:
                   call-stack-height)))
              (otherwise call-stack-height)))))

(defopeners update-call-stack-height-aux :hyps ((syntaxp (quotep instr))))

(defthm update-call-stack-height-aux-of-if-arg1
  (equal (update-call-stack-height-aux (if test instr1 instr2) call-stack-height stat)
         (if test
             (update-call-stack-height-aux instr1 call-stack-height stat)
           (update-call-stack-height-aux instr2 call-stack-height stat))))


;; Increment on call, decrement on return
(defun update-call-stack-height (call-stack-height stat)
  (declare (xargs :guard (and (integerp call-stack-height)
                              (stat32ip stat))
                  :guard-hints (("Goal" :in-theory (enable ubyte32p)))
                  ))
  (let* ((pc (pc stat))
         (instr (read 4 pc stat)))
    (update-call-stack-height-aux instr call-stack-height stat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defund run-is-donep (return-address old-sp stat)
;;   (declare (xargs :guard (and (unsigned-byte-p 32 return-address)
;;                               (unsigned-byte-p 32 old-sp)
;;                               (stat32ip stat))))
;;   (if (sp-is-abovep old-sp stat) ; the stack has shrunk (it grows downward)
;;       ;; the stack has shrunk, so we've exited the main subroutine being lifted
;;       t
;;     (if (sp-is-abovep old-sp stat) ; the stack has grown (it grows downward)
;;         ;; the stack has grown, so we've are still executing the main
;;         ;; subroutine being lifted (or one of its subroutines):
;;         nil
;;       ;; the stack is the same size as when we started and we've reached the
;;       ;; return address:
;;       (equal (pc stat) return-address))))

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(defpun run-until-return-aux (call-stack-height stat)
  (if (< call-stack-height 0)
      stat
    (run-until-return-aux (update-call-stack-height call-stack-height stat) (step32 stat))))

;; todo: restrict to when stat is not an IF/MYIF
(defthm run-until-return-aux-base
  (implies (< call-stack-height 0)
           (equal (run-until-return-aux call-stack-height stat)
                  stat)))

;; todo: restrict to when stat is not an IF/MYIF
(defthm run-until-return-aux-opener
  (implies (not (< call-stack-height 0))
           (equal (run-until-return-aux call-stack-height stat)
                  (run-until-return-aux (update-call-stack-height call-stack-height stat) (step32 stat)))))

;; todo: add "smart" if handling, like we do elsewhere
(defthm run-until-return-aux-of-if-arg2
  (equal (run-until-return-aux call-stack-height (if test stata statb))
         (if test
             (run-until-return-aux call-stack-height stata)
           (run-until-return-aux call-stack-height statb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund run-until-return (stat)
  (declare (xargs :guard (stat32ip stat)))
  (run-until-return-aux
   0 ; initial call-stack-height
   stat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The RISC-V calling convention seems to involve code like this:
;;
;; 101b0:       fe010113                addi    sp,sp,-32    // increase stack height (grows downward)
;;  ... instructions ...
;; 101e0:       02010113                addi    sp,sp,32     // decrease stack height (grows downward)
;; 101e4:       00008067                ret                  // jump to saved return address
;;
;; So we start by stepping once.  This increases the stack height.  Then we run
;; until the stack height decreases again.  Finally, we step one more time to
;; do the RET.
(defund run-subroutine (stat)
   ;; (declare (xargs :guard (stat32ip stat))) ; todo: need a property of the defpun
  ;;(step32 (run-until-return (step32 stat)))
  (run-until-return stat)
  )
