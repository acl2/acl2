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

(defund execute-inst (mnemonic args inst-address arm)
  (declare (xargs :guard (and (good-instp mnemonic args)
                              (addressp inst-address))
                  :guard-hints (("Goal" :in-theory (enable good-instp)))
                  :stobjs arm))
  (case mnemonic
    (:add-immediate (execute-add-immediate args inst-address arm))
    (:add-register (execute-add-register args inst-address arm))
    ;; todo: more
    (otherwise (update-error :unsupported-mnemonic-error arm))))

;; Returns a new state, which might have the error flag set
(defun step (arm)
  (declare (xargs :stobjs arm))
  (if (error arm)
      arm
    (b* ((inst-address (pc arm))
         (inst (read 4 inst-address arm))
         ((mv erp mnemonic args)
          (arm32-decode inst))
         ((when erp)
          (update-error :decoding-error arm)))
      (execute-inst mnemonic args inst-address arm))))
