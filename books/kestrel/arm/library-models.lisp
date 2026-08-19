; Models of library (libc) functions
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "state")
(include-book "kestrel/bv/bvlt-def" :dir :system)

;; todo: undefined if not argument is no either 0-255 or -1 !
;; todo: clobber register and flag values with undefined values (from the oracle)
;; todo: result in the true case should be some undefined non-zero value
(defund run-isdigit (arm)
  (declare (xargs :stobjs arm))
  (let* ((ret-addr (reg *lr* arm)) ; save the return address
         (arg (reg 0 arm)) ; R0 holds the argument
         ;; check for digit character:
         (result (and (bvle 32 (char-code #\0) arg)
                      (bvle 32 arg (char-code #\9))))
         (bit-result (if result
                         #x0800 ; to match glibc
                       0))
         ;; result goes in R0:
         (arm (set-reg 0 bit-result arm))
         ;; return:
         (arm (set-reg *pc* ret-addr arm)))
    arm))

(defund library-model-rules ()
  (declare (xargs :guard t))
  '(arm::run-isdigit))
