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

(acl2::controlled-configuration)

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

(defmacro test-instr-op-thm (&key funct (rs1 '1) (rs2 '2) (rd '3)
                                  src1 src2 dst signedp
                                  enable disable cases)
  (b* ((read (if signedp 'read-xreg-signed 'read-xreg-unsigned)))
    `(test-instr-thm
      :instr (make-instr-op :funct ,funct :rd ,rd :rs1 ,rs1 :rs2 ,rs2)
      :pre ((equal (,read ,rs1 stat feat) ,src1)
            (equal (,read ,rs2 stat feat) ,src2))
      :post ((equal (read-pc stat1 feat) (loghead (feat->xlen feat) (+ 4 pc)))
             (equal (,read ,rd stat1 feat) ,dst))
      :enable (exec-op
               read-xreg-of-write-xreg
               read-pc-of-inc4-pc
               ,@enable)
      :disable ,disable
      :cases ,cases)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ADD

(defmacro test-instr-add-thm (&key (rs1 '1) (rs2 '2) (rd '3)
                                   src1 src2 dst signedp
                                   enable)
  `(test-instr-op-thm :funct (op-funct-add)
                      :rs1 ,rs1 :rs2 ,rs2 :rd ,rd
                      :src1 ,src1 :src2 ,src2 :dst ,dst
                      :signedp ,signedp
                      :enable ,enable
                      :disable ((:e tau-system)) ; for speed
                      :cases ((feat-32p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-add-thm
 :src1 11
 :src2 22
 :dst 33
 :enable (exec-add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-add-thm
 :rs1 4
 :rs2 5
 :rd 6
 :src1 -11
 :src2 -22
 :dst -33
 :signedp t
 :enable (exec-add-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SUB

(defmacro test-instr-sub-thm (&key (rs1 '1) (rs2 '2) (rd '3)
                                   src1 src2 dst signedp
                                   enable)
  `(test-instr-op-thm :funct (op-funct-sub)
                      :rs1 ,rs1 :rs2 ,rs2 :rd ,rd
                      :src1 ,src1 :src2 ,src2 :dst ,dst
                      :signedp ,signedp
                      :enable ,enable
                      :disable ((:e tau-system)) ; for speed
                      :cases ((feat-32p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-sub-thm
 :src1 54
 :src2 23
 :dst 31
 :enable (exec-sub))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-sub-thm
 :rs1 4
 :rs2 5
 :rd 6
 :src1 11
 :src2 22
 :dst -11
 :signedp t
 :enable (exec-sub-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SLT

(defmacro test-instr-slt-thm (&key (rs1 '1) (rs2 '2) (rd '3)
                                   src1 src2 dst
                                   enable)
  `(test-instr-op-thm :funct (op-funct-slt)
                      :rs1 ,rs1 :rs2 ,rs2 :rd ,rd
                      :src1 ,src1 :src2 ,src2 :dst ,dst
                      :signedp t
                      :enable ,enable
                      :disable ((:e tau-system)) ; for speed
                      :cases ((feat-32p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-slt-thm
 :rs1 11
 :rs2 12
 :rd 13
 :src1 78
 :src2 934
 :dst 1
 :enable (exec-slt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-slt-thm
 :rs1 11
 :rs2 12
 :rd 13
 :src1 1000
 :src2 1000
 :dst 0
 :enable (exec-slt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-slt-thm
 :rs1 11
 :rs2 12
 :rd 11
 :src1 78
 :src2 -934
 :dst 0
 :enable (exec-slt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; SLTU

(defmacro test-instr-sltu-thm (&key (rs1 '1) (rs2 '2) (rd '3)
                                    src1 src2 dst
                                    enable)
  `(test-instr-op-thm :funct (op-funct-sltu)
                      :rs1 ,rs1 :rs2 ,rs2 :rd ,rd
                      :src1 ,src1 :src2 ,src2 :dst ,dst
                      :signedp nil
                      :enable ,enable
                      :disable ((:e tau-system)) ; for speed
                      :cases ((feat-32p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-sltu-thm
 :rs1 14
 :rs2 1
 :rd 1
 :src1 78
 :src2 934
 :dst 1
 :enable (exec-sltu))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-sltu-thm
 :rs1 5
 :rs2 3
 :rd 5
 :src1 1000
 :src2 1000
 :dst 0
 :enable (exec-sltu))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-sltu-thm
 :rs1 14
 :rs2 1
 :rd 1
 :src1 20000
 :src2 19999
 :dst 0
 :enable (exec-sltu))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; AND

(defmacro test-instr-and-thm (&key (rs1 '1) (rs2 '2) (rd '3)
                                   src1 src2 dst signedp
                                   enable)
  `(test-instr-op-thm :funct (op-funct-and)
                      :rs1 ,rs1 :rs2 ,rs2 :rd ,rd
                      :src1 ,src1 :src2 ,src2 :dst ,dst
                      :signedp ,signedp
                      :enable ,enable
                      :disable ((:e tau-system)) ; for speed
                      :cases ((feat-32p feat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-and-thm
 :rs1 8
 :rs2 1
 :rd 2
 :src1 #xffaa
 :src2 #x3333
 :dst #x3322
 :enable (exec-and))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-instr-and-thm
 :rs1 4
 :rs2 4
 :rd 4
 :src1 #xabcdef
 :src2 #xabcdef
 :dst #xabcdef
 :enable (exec-and))
