; Copyright (C) 2020 David S. Hardin
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(IN-PACKAGE "RTL")

(INCLUDE-BOOK "rtl/rel11/lib/rac" :DIR :SYSTEM)

(SET-IGNORE-OK T)

(SET-IRRELEVANT-FORMALS-OK T)

(DEFUND ZEROREGS-LOOP-0 (I S)
        (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
        (IF (AND (INTEGERP I) (> I 0))
            (LET ((S (AS 'REGS
                         (AS (- I 1) (BITS 0 63 0) (AG 'REGS S))
                         S)))
                 (ZEROREGS-LOOP-0 (- I 1) S))
            S))

(DEFUND ZEROREGS (S)
        (ZEROREGS-LOOP-0 256 S))

(DEFUND ZERODMEM-LOOP-0 (I S)
        (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
        (IF (AND (INTEGERP I) (> I 0))
            (LET ((S (AS 'DMEM
                         (AS (- I 1) (BITS 0 63 0) (AG 'DMEM S))
                         S)))
                 (ZERODMEM-LOOP-0 (- I 1) S))
            S))

(DEFUND ZERODMEM (S)
        (ZERODMEM-LOOP-0 4096 S))

(DEFUND ZEROCMEM-LOOP-0 (I S)
        (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
        (IF (AND (INTEGERP I) (> I 0))
            (LET ((S (AS 'CMEM
                         (AS (- I 1) (BITS 0 31 0) (AG 'CMEM S))
                         S)))
                 (ZEROCMEM-LOOP-0 (- I 1) S))
            S))

(DEFUND ZEROCMEM (S)
        (ZEROCMEM-LOOP-0 1024 S))

(DEFUND RESETALL (S)
        (LET* ((S (AS 'PC (BITS 0 9 0) S))
               (S (AS 'SP (BITS 0 11 0) S))
               (S (AS 'OPCODE (BITS 1 7 0) S))
               (S (AS 'OP1 (BITS 0 7 0) S))
               (S (AS 'OP2 (BITS 0 7 0) S))
               (S (AS 'OP3 (BITS 0 7 0) S))
               (S (AS 'C (BITS 0 0 0) S))
               (S (AS 'N (BITS 0 0 0) S))
               (S (AS 'Z (BITS 0 0 0) S))
               (S (AS 'V (BITS 0 0 0) S))
               (S (ZEROREGS S))
               (S (ZERODMEM S)))
              (ZEROCMEM S)))

(DEFUND RESETALLBUTCMEM (S)
        (LET* ((S (AS 'PC (BITS 0 9 0) S))
               (S (AS 'SP (BITS 0 11 0) S))
               (S (AS 'OPCODE (BITS 1 7 0) S))
               (S (AS 'OP1 (BITS 0 7 0) S))
               (S (AS 'OP2 (BITS 0 7 0) S))
               (S (AS 'OP3 (BITS 0 7 0) S))
               (S (AS 'C (BITS 0 0 0) S))
               (S (AS 'N (BITS 0 0 0) S))
               (S (AS 'Z (BITS 0 0 0) S))
               (S (AS 'V (BITS 0 0 0) S))
               (S (ZEROREGS S)))
              (ZERODMEM S)))

(DEFUND NEXTINST (S)
        (LET* ((CODEWD (AG (AG 'PC S) (AG 'CMEM S)))
               (S (AS 'OPCODE (BITS CODEWD 31 24) S))
               (S (AS 'OP1 (BITS CODEWD 23 16) S))
               (S (AS 'OP2 (BITS CODEWD 15 8) S))
               (S (AS 'OP3 (BITS CODEWD 7 0) S)))
              (AS 'PC (BITS (+ (AG 'PC S) 1) 9 0) S)))

(DEFUND DO_LDR (S)
        (LET ((ADDR (BITS (LOGAND (AG (AG 'OP2 S) (AG 'REGS S))
                                  4095)
                          11 0)))
             (AS 'REGS
                 (AS (AG 'OP1 S)
                     (AG ADDR (AG 'DMEM S))
                     (AG 'REGS S))
                 S)))

(DEFUND DO_STR (S)
        (LET ((ADDR (BITS (LOGAND (AG (AG 'OP1 S) (AG 'REGS S))
                                  4095)
                          11 0)))
             (AS 'DMEM
                 (AS ADDR (AG (AG 'OP2 S) (AG 'REGS S))
                     (AG 'DMEM S))
                 S)))

(DEFUND DO_ADD (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (+ (AG (AG 'OP2 S) (AG 'REGS S))
                         (AG (AG 'OP3 S) (AG 'REGS S)))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_ADDI (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (+ (AG (AG 'OP2 S) (AG 'REGS S))
                         (AG 'OP3 S))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_CMP (S)
        (LET ((RES (BITS (- (AG (AG 'OP1 S) (AG 'REGS S))
                            (AG (AG 'OP2 S) (AG 'REGS S)))
                         63 0)))
             (IF1 (LOG= RES 0)
                  (LET* ((S (AS 'C (BITS 0 0 0) S))
                         (S (AS 'N (BITS 0 0 0) S))
                         (S (AS 'V (BITS 0 0 0) S)))
                        (AS 'Z (BITS 1 0 0) S))
                  (IF1 (LOG= (LOGAND RES 9223372036854775808)
                             9223372036854775808)
                       (LET* ((S (AS 'C (BITS 0 0 0) S))
                              (S (AS 'N (BITS 1 0 0) S))
                              (S (AS 'V (BITS 0 0 0) S)))
                             (AS 'Z (BITS 0 0 0) S))
                       (LET* ((S (AS 'C (BITS 1 0 0) S))
                              (S (AS 'N (BITS 0 0 0) S))
                              (S (AS 'V (BITS 0 0 0) S)))
                             (AS 'Z (BITS 0 0 0) S))))))

(DEFUND DO_CMPI (S)
        (LET ((RES (BITS (- (AG (AG 'OP1 S) (AG 'REGS S))
                            (AG 'OP2 S))
                         63 0)))
             (IF1 (LOG= RES 0)
                  (LET* ((S (AS 'C (BITS 0 0 0) S))
                         (S (AS 'N (BITS 0 0 0) S))
                         (S (AS 'V (BITS 0 0 0) S)))
                        (AS 'Z (BITS 1 0 0) S))
                  (IF1 (LOG= (LOGAND RES 9223372036854775808)
                             9223372036854775808)
                       (LET* ((S (AS 'C (BITS 0 0 0) S))
                              (S (AS 'N (BITS 1 0 0) S))
                              (S (AS 'V (BITS 0 0 0) S)))
                             (AS 'Z (BITS 0 0 0) S))
                       (LET* ((S (AS 'C (BITS 1 0 0) S))
                              (S (AS 'N (BITS 0 0 0) S))
                              (S (AS 'V (BITS 0 0 0) S)))
                             (AS 'Z (BITS 0 0 0) S))))))

(DEFUND DO_CONST (S)
        (LET ((K (BITS (LOGIOR (ASH (AG 'OP2 S) 8) (AG 'OP3 S))
                       63 0)))
             (AS 'REGS
                 (AS (AG 'OP1 S) K (AG 'REGS S))
                 S)))

(DEFUND DO_LSL (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (ASH (AG (AG 'OP2 S) (AG 'REGS S))
                           (LOGAND (AG 'OP3 S) 63))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_LSR (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (ASH (AG (AG 'OP2 S) (AG 'REGS S))
                           (- (LOGAND (AG 'OP3 S) 63)))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_ASR (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (LOGIOR (ASH (AG (AG 'OP2 S) (AG 'REGS S))
                                   (- (LOGAND (AG 'OP3 S) 63)))
                              (ASH (- 0
                                      (ASH (AG (AG 'OP2 S) (AG 'REGS S))
                                           (- (- 64 1))))
                                   (- 64 (LOGAND (AG 'OP3 S) 63))))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_MUL (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (* (AG (AG 'OP2 S) (AG 'REGS S))
                         (AG (AG 'OP3 S) (AG 'REGS S)))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_SUB (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (- (AG (AG 'OP2 S) (AG 'REGS S))
                         (AG (AG 'OP3 S) (AG 'REGS S)))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_SUBI (S)
        (AS 'REGS
            (AS (AG 'OP1 S)
                (BITS (- (AG (AG 'OP2 S) (AG 'REGS S))
                         (AG 'OP3 S))
                      63 0)
                (AG 'REGS S))
            S))

(DEFUND DO_B (S)
        (IF1 (LOG> (AG 'OP1 S) 127)
             (AS 'PC
                 (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                       9 0)
                 S)
             (AS 'PC
                 (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                 S)))

(DEFUND DO_BEQ (S)
        (IF1 (LOG= (AG 'Z S) 1)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BNE (S)
        (IF1 (LOG= (AG 'Z S) 0)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BLO (S)
        (IF1 (LOG= (AG 'C S) 0)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BLS (S)
        (IF1 (LOGIOR1 (LOG= (AG 'C S) 0)
                      (LOG= (AG 'Z S) 1))
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BHI (S)
        (IF1 (LOGAND1 (LOG= (AG 'C S) 1)
                      (LOG= (AG 'Z S) 0))
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BHS (S)
        (IF1 (LOG= (AG 'C S) 1)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BMI (S)
        (IF1 (LOG= (AG 'N S) 1)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_BPL (S)
        (IF1 (LOG= (AG 'N S) 0)
             (IF1 (LOG> (AG 'OP1 S) 127)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (- (AG 'OP1 S) 256))
                            9 0)
                      S)
                  (AS 'PC
                      (BITS (+ (AG 'PC S) (AG 'OP1 S)) 9 0)
                      S))
             S))

(DEFUND DO_HALT (S)
        (AS 'PC (BITS (- (AG 'PC S) 1) 9 0) S))

(DEFUND DO_NOP (S) S)

(DEFUND
 DO_INST (S)
 (LET
  ((OPC (AG 'OPCODE S)))
  (IF1
   (LOG= OPC 1)
   (DO_NOP S)
   (IF1
    (LOG= OPC 2)
    (DO_HALT S)
    (IF1
     (LOG= OPC 3)
     (DO_ADD S)
     (IF1
      (LOG= OPC 4)
      (DO_ADDI S)
      (IF1
       (LOG= OPC 5)
       (DO_ASR S)
       (IF1
        (LOG= OPC 6)
        (DO_CMP S)
        (IF1
         (LOG= OPC 7)
         (DO_CMPI S)
         (IF1
          (LOG= OPC 8)
          (DO_CONST S)
          (IF1
           (LOG= OPC 9)
           (DO_LSL S)
           (IF1
            (LOG= OPC 10)
            (DO_LSR S)
            (IF1
             (LOG= OPC 11)
             (DO_MUL S)
             (IF1
              (LOG= OPC 12)
              (DO_SUB S)
              (IF1
               (LOG= OPC 13)
               (DO_SUBI S)
               (IF1
                (LOG= OPC 14)
                (DO_LDR S)
                (IF1
                 (LOG= OPC 15)
                 (DO_STR S)
                 (IF1
                  (LOG= OPC 16)
                  (DO_B S)
                  (IF1
                   (LOG= OPC 17)
                   (DO_BEQ S)
                   (IF1
                    (LOG= OPC 18)
                    (DO_BHI S)
                    (IF1
                     (LOG= OPC 19)
                     (DO_BHS S)
                     (IF1
                       (LOG= OPC 20)
                       (DO_BLO S)
                       (IF1 (LOG= OPC 21)
                            (DO_BLS S)
                            (IF1 (LOG= OPC 22)
                                 (DO_BMI S)
                                 (IF1 (LOG= OPC 23)
                                      (DO_BNE S)
                                      (IF1 (LOG= OPC 24)
                                           (DO_BPL S)
                                           (DO_HALT S)))))))))))))))))))))))))))

(DEFUND LEG64STEP (S)
        (DO_INST (NEXTINST S)))

(DEFUND LEG64STEPS-LOOP-0 (I COUNT S)
        (DECLARE (XARGS :MEASURE (NFIX (- I 0))))
        (IF (AND (INTEGERP I) (> I 0))
            (LET ((S (LEG64STEP S)))
                 (LEG64STEPS-LOOP-0 (- I 1) COUNT S))
            S))

(DEFUND LEG64STEPS (S COUNT)
        (LEG64STEPS-LOOP-0 COUNT COUNT S))

(DEFUND SETUPDMEM (BASE S)
        (LET* ((S (AS 'DMEM
                      (AS BASE (BITS 10 63 0) (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 1)
                          (BITS 43 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 2)
                          (BITS 4 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 3)
                          (BITS 22 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 4)
                          (BITS 7 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 5)
                          (BITS 14 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 6)
                          (BITS 43 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 7)
                          (BITS 92 63 0)
                          (AG 'DMEM S))
                      S))
               (S (AS 'DMEM
                      (AS (+ BASE 8)
                          (BITS 22 63 0)
                          (AG 'DMEM S))
                      S)))
              (AS 'DMEM
                  (AS (+ BASE 9)
                      (BITS 43 63 0)
                      (AG 'DMEM S))
                  S)))

(DEFUND DOFACTO3 (N S)
        (LET* ((S (AS 'REGS (AS 0 N (AG 'REGS S)) S))
               (S (AS 'REGS
                      (AS 1 (BITS 1 63 0) (AG 'REGS S))
                      S))
               (K (BITS 0 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 8 255) 24)
                                        (LOGAND N 255))
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 8 255) 24)
                                                (ASH 1 16))
                                        1)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 7 255) 24)
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 21 255) 24)
                                                (ASH 4 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 11 255) 24)
                                                        (ASH 1 16))
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 13 255) 24) 1)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 7 255) 24)
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 23 255) 24)
                                                (ASH 252 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 2 255) 24) 0)
                                31 0)
                          (AG 'CMEM S))
                      S)))
              (LEG64STEPS S (+ (+ 4 (* (- N 1) 4)) 2))))

(DEFUND DOFACT (N S)
        (LET* ((S (AS 'REGS (AS 0 N (AG 'REGS S)) S))
               (S (AS 'REGS
                      (AS 1 (BITS 1 63 0) (AG 'REGS S))
                      S))
               (K (BITS 0 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 8 255) 24)
                                        (LOGAND N 255))
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 8 255) 24)
                                                (ASH 1 16))
                                        1)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 8 255) 24)
                                                (ASH 2 16))
                                        20)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 6 255) 24)
                                                (ASH 2 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 19 255) 24)
                                                (ASH 5 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 7 255) 24) 0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 17 255) 24)
                                                (ASH 3 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 11 255) 24)
                                                        (ASH 1 16))
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 13 255) 24) 1)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 16 255) 24)
                                                (ASH 251 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                                (ASH 1 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 2 255) 24) 0)
                                31 0)
                          (AG 'CMEM S))
                      S)))
              (LEG64STEPS S (+ (+ 5 (* N 5)) 4))))

(DEFUND DOSUMARR (ARR N S)
        (LET* ((S (AS 'REGS (AS 0 ARR (AG 'REGS S)) S))
               (S (AS 'REGS (AS 1 N (AG 'REGS S)) S))
               (K (BITS 0 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                                (ASH 5 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 8 255) 24) 0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 7 255) 24)
                                                (ASH 1 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 17 255) 24)
                                                (ASH 10 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 8 255) 24)
                                                (ASH 2 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 6 255) 24)
                                                        (ASH 1 16))
                                                (ASH 2 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 21 255) 24)
                                                (ASH 7 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                                        (ASH 3 16))
                                                (ASH 2 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 9 255) 24)
                                                        (ASH 3 16))
                                                (ASH 3 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 3 255) 24)
                                                        (ASH 3 16))
                                                (ASH 5 8))
                                        3)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 14 255) 24)
                                                        (ASH 4 16))
                                                (ASH 3 8))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 3 255) 24) 4)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (LOGIOR (ASH (LOGAND 4 255) 24)
                                                        (ASH 2 16))
                                                (ASH 2 8))
                                        1)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (LOGIOR (ASH (LOGAND 16 255) 24)
                                                (ASH 247 16))
                                        0)
                                31 0)
                          (AG 'CMEM S))
                      S))
               (K (BITS (+ K 1) 9 0))
               (S (AS 'CMEM
                      (AS K
                          (BITS (LOGIOR (ASH (LOGAND 2 255) 24) 0)
                                31 0)
                          (AG 'CMEM S))
                      S)))
              (LEG64STEPS S (+ (+ 5 (* N 9)) 3))))

