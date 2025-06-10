; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "specification/execution")
(include-book "specification/reads-over-writes")
(include-book "executable/decoding-correct")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests in the form of theorems
; that include a mix of symbolic and concrete data.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-thm (formula &rest hints)
  `(encapsulate () (defrulel _test_ ,formula ,@hints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; add

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-thm
 (implies (and (not (errorp stat feat))
               (equal (read-pc stat feat)
                      pc)
               (equal (read-instruction pc stat feat)
                      (encode (instr-op (op-funct-add) 3 1 2) feat))
               (equal (read-xreg-unsigned 1 stat feat)
                      11)
               (equal (read-xreg-unsigned 2 stat feat)
                      22))
          (b* ((stat1 (step stat feat)))
            (and (not (errorp stat1 feat))
                 (equal (read-pc stat1 feat)
                        (loghead (feat->xlen feat) (+ 4 pc)))
                 (equal (read-xreg-unsigned 3 stat1 feat)
                        33))))
 :enable (step
          encode
          decode-is-decodex
          decodex
          exec-instr
          exec-op
          exec-add
          read-xreg-of-write-xreg
          read-xreg-signed
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-thm
 (implies (and (not (errorp stat feat))
               (equal (read-pc stat feat)
                      pc)
               (equal (read-instruction pc stat feat)
                      (encode (instr-op (op-funct-add) 6 4 5) feat))
               (equal (read-xreg-signed 4 stat feat)
                      -11)
               (equal (read-xreg-signed 5 stat feat)
                      -22))
          (b* ((stat1 (step stat feat)))
            (and (not (errorp stat1 feat))
                 (equal (read-pc stat1 feat)
                        (loghead (feat->xlen feat) (+ 4 pc)))
                 (equal (read-xreg-signed 6 stat1 feat)
                        -33))))
 :enable (step
          encode
          decode-is-decodex
          decodex
          exec-instr
          exec-op
          exec-add-alt-def
          read-xreg-of-write-xreg
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))
