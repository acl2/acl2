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
(include-book "misc/defpun" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)

;; Tests whether the stack pointer is "above" OLD-SP.  For now, we define
;; "above" as "not closely below".  Recall that the stack grows downward, so a
;; larger SP means a shorter stack.
(defund sp-is-abovep (old-sp stat)
  (declare (xargs :guard (and (unsigned-byte-p 32 old-sp)
                              (stat32ip stat))))
  (bvlt 32 2147483648 ; 2^31
        (bvminus 32 old-sp (sp stat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What should we do about faults?
;; TODO: How to get defpun to work with a stobj?
(acl2::defpun run-until-sp-is-above (old-sp stat)
  (if (sp-is-abovep old-sp stat)
      stat
    (run-until-sp-is-above old-sp (step32 stat))))

;; todo: restrict to when stat is not an IF/MYIF
(defthm run-until-sp-is-above-base
  (implies (sp-is-abovep old-sp stat)
           (equal (run-until-sp-is-above old-sp stat)
                  stat)))

;; todo: restrict to when stat is not an IF/MYIF
(defthm run-until-sp-is-above-opener
  (implies (not (sp-is-abovep old-sp stat))
           (equal (run-until-sp-is-above old-sp stat)
                  (run-until-sp-is-above old-sp (step32 stat)))))

(defthm run-until-sp-is-above-of-if-arg2
  (equal (run-until-sp-is-above old-sp (if test stata statb))
         (if test
             (run-until-sp-is-above old-sp stata)
           (run-until-sp-is-above old-sp statb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund run-until-return (stat)
  (declare (xargs :guard (stat32ip stat)))
  (run-until-sp-is-above (sp stat) stat))

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
  (step32 (run-until-return (step32 stat))))
