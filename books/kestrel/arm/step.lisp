; A formal model of ARM32: Stepping the state
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "instructions")
(include-book "decoder")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-execute-cases (mnemonics)
  (declare (xargs :guard (keyword-listp mnemonics)))
  (if (endp mnemonics)
      nil
    (let* ((mnemonic (first mnemonics))
           (execute-function (pack-in-package-of-first-symbol 'execute- (symbol-name mnemonic))))
      (cons `(,mnemonic (,execute-function args inst-address arm))
            (make-execute-cases (rest mnemonics))))))

(make-event
 ;; Dispatches according to the mnemonic and runs the corresponding semantic
 ;; function.
 `(defund execute-inst (mnemonic args inst-address arm)
    (declare (xargs :guard (and (good-instp mnemonic args)
                                (addressp inst-address))
                    :guard-hints (("Goal" :in-theory (enable good-instp)))
                    :stobjs arm))
    (case mnemonic
      ,@(make-execute-cases (strip-cars *patterns*))
      (otherwise (update-error :unsupported-mnemonic-error arm)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a new state, which might have the error flag set
(defund step (arm)
  (declare (xargs :stobjs arm))
  (if (error arm)
      arm ; errors persist
    (b* ((inst-address (pc arm))
         (inst (read 4 inst-address arm))
         ((mv erp mnemonic args)
          (arm32-decode inst))
         ((when erp)
          (update-error :decoding-error arm)))
      (execute-inst mnemonic args inst-address arm))))

(defthm step-opener
  (implies (and (not (error arm)) ; avoids loops
                ;; todo: use a binding-hyp?
                (not (mv-nth 0 (arm32-decode (read 4 (pc arm) arm)))))
           (equal (step arm)
                  (b* ((inst-address (pc arm))
                       (inst (read 4 inst-address arm))
                       ((mv & ;erp
                            mnemonic args)
                        (arm32-decode inst))
                       ;; ((when erp)
                       ;;  (update-error :decoding-error arm))
                       )
                    (execute-inst mnemonic args inst-address arm))))
  :hints (("Goal" :in-theory (enable step))))

(defthm step-of-if
  (equal (step (if test arm1 arm2))
         (if test (step arm1) (step arm2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Once an error is encountered, no more changes are made.
(defun run (steps arm)
  (declare (xargs :guard (natp steps)
                  :stobjs arm))
  (if (zp steps)
      arm
    (let ((arm (step arm)))
      (run (+ -1 steps) arm))))

(defthm run-opener
  (implies (syntaxp (quotep steps)) ; todo: require us to know the current instruction
           (equal (run steps arm)
                  (if (zp steps)
                      arm
                    (let ((arm (step arm)))
                      (run (+ -1 steps) arm)))))
  :hints (("Goal" :in-theory (enable run))))
