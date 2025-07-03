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
(include-book "specification/semantics-equivalences")
(include-book "executable/decoding-correct")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests in the form of theorems
; that include a mix of symbolic and concrete data.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate a test theorem of any form.

(defmacro test-thm (formula &rest hints)
  `(encapsulate () (defrulel _test_ ,formula ,@hints)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate a test theorem for a single instruction execution,
; supplying instruction, preconditions, postconditions, and hints.

(defmacro test-instr-thm (&key instr pre post
                               enable disable cases)
  `(test-thm
    (implies (and (not (errorp stat feat))
                  (equal (read-pc stat feat)
                         pc)
                  (equal (read-instruction pc stat feat)
                         (encode ,instr feat))
                  ,@pre)
             (b* ((stat1 (step stat feat)))
               (and (not (errorp stat1 feat))
                    ,@post)))
    :enable (step
             encode
             decode-is-decodex
             decodex
             exec-instr
             ,@enable)
    :disable ,disable
    ,@(and cases (list :cases cases))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate a test theorem for a single OP instruction execution,
; supplying function,
; source and destination registers,
; source values,
; destination value,
; whether source and destination values are signed or unsigned,
; and hints.

(defmacro test-instr-op-thm (&key funct rs1 rs2 rd
                                  src1 src2 dst
                                  src1-signedp src2-signedp dst-signedp
                                  enable disable cases)
  (b* ((read-rs1 (if src1-signedp 'read-xreg-signed 'read-xreg-unsigned))
       (read-rs2 (if src2-signedp 'read-xreg-signed 'read-xreg-unsigned))
       (read-rd (if dst-signedp 'read-xreg-signed 'read-xreg-unsigned)))
    `(test-instr-thm
      :instr (make-instr-op :funct ,funct :rd ,rd :rs1 ,rs1 :rs2 ,rs2)
      :pre ((equal (,read-rs1 ,rs1 stat feat) ,src1)
            (equal (,read-rs2 ,rs2 stat feat) ,src2))
      :post ((equal (read-pc stat1 feat) (loghead (feat->xlen feat) (+ 4 pc)))
             (equal (,read-rd ,rd stat1 feat) ,dst))
      :enable (exec-op
               ,@enable)
      :disable ,disable
      :cases ,cases)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ADD

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-add)
 :rs1 1
 :rs2 2
 :rd 3
 :src1 11
 :src2 22
 :dst 33
 :enable (exec-add
          read-xreg-of-write-xreg
          read-xreg-signed
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-add)
 :rs1 4
 :rs2 5
 :rd 6
 :src1 -11
 :src2 -22
 :dst -33
 :src1-signedp t
 :src2-signedp t
 :dst-signedp t
 :enable (exec-add-alt-def
          read-xreg-of-write-xreg
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SUB

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-sub)
 :rs1 1
 :rs2 2
 :rd 3
 :src1 54
 :src2 23
 :dst 31
 :enable (exec-sub
          read-xreg-of-write-xreg
          read-xreg-signed
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-sub)
 :rs1 4
 :rs2 5
 :rd 6
 :src1 11
 :src2 22
 :dst -11
 :src1-signedp t
 :src2-signedp t
 :dst-signedp t
 :enable (exec-sub-alt-def
          read-xreg-of-write-xreg
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SLT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-slt)
 :rs1 11
 :rs2 12
 :rd 13
 :src1 78
 :src2 934
 :dst 1
 :src1-signedp t
 :src2-signedp t
 :enable (exec-slt
          read-xreg-of-write-xreg
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-op-thm
 :funct (op-funct-slt)
 :rs1 11
 :rs2 12
 :rd 11
 :src1 78
 :src2 -934
 :dst 0
 :src1-signedp t
 :src2-signedp t
 :enable (exec-slt
          read-xreg-of-write-xreg
          read-pc-of-inc4-pc)
 :disable ((:e tau-system)) ; for speed
 :cases ((feat-32p feat)))
