; Smoke tests for the ARM32 model, run through the test harness
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "harness")

;; Each vector below executes one instruction from a hand-built state and
;; states the expected result, worked out by hand from the ARM Architecture
;; Reference Manual.  The :id gives the assembly for the instruction word in
;; :code.  Registers not mentioned start at 0 and must end unchanged.

(defconst *smoke-vectors*
  '(;; Multiply: r3 = r5 * r4 = 7 * 6.  The S bit is clear, so no flags change.
    (:id "mul r3, r5, r4"
     :pc #x1000 :code (#xE0030495)
     :regs ((4 . 6) (5 . 7))
     :expect (:pc #x1004 :regs ((3 . 42))))

    ;; Add with flags: 0xFFFFFFFF + 1 = 0 with a carry out, so Z and C are set.
    (:id "adds r0, r1, r2"
     :pc #x1000 :code (#xE0910002)
     :regs ((1 . #xFFFFFFFF) (2 . 1))
     :expect (:pc #x1004 :regs ((0 . 0)) :apsr #x60000000))

    ;; Subtract with flags: 0 - 1 = 0xFFFFFFFF.  N is set, and C is clear
    ;; because the subtraction borrowed.
    (:id "subs r0, r1, #1"
     :pc #x1000 :code (#xE2510001)
     :regs ((1 . 0))
     :expect (:pc #x1004 :regs ((0 . #xFFFFFFFF)) :apsr #x80000000))

    ;; Compare equal values: Z is set, and C is set because nothing borrowed.
    (:id "cmp r0, r1"
     :pc #x1000 :code (#xE1500001)
     :regs ((0 . 5) (1 . 5))
     :expect (:pc #x1004 :apsr #x60000000))

    ;; Load a word through a base register plus an immediate offset.  The
    ;; bytes 12 34 56 78 stored at 0x2004 read back as the little-endian word.
    (:id "ldr r0, [r1, #4]"
     :pc #x1000 :code (#xE5910004)
     :regs ((1 . #x2000))
     :mem ((#x2004 4 #x78563412))
     :expect (:pc #x1004 :regs ((0 . #x78563412))))

    ;; Store a word.
    (:id "str r2, [r1]"
     :pc #x1000 :code (#xE5812000)
     :regs ((1 . #x3000) (2 . #xDEADBEEF))
     :expect (:pc #x1004 :mem ((#x3000 4 #xDEADBEEF))))

    ;; Push two registers: the stack pointer drops by 8 and the registers are
    ;; stored in ascending order.
    (:id "push {r4, lr}"
     :pc #x1000 :code (#xE92D4010)
     :regs ((4 . #x44) (13 . #x4000) (14 . #x99))
     :expect (:pc #x1004
              :regs ((13 . #x3FF8))
              :mem ((#x3FF8 4 #x44) (#x3FFC 4 #x99))))

    ;; Unconditional branch forward.  The offset is relative to the
    ;; instruction address plus 8, so 0x1008 + 2*4 = 0x1010.
    (:id "b 0x1010"
     :pc #x1000 :code (#xEA000002)
     :expect (:pc #x1010))

    ;; Conditional branch not taken: with Z set, bne falls through.
    (:id "bne 0x1010 (not taken)"
     :pc #x1000 :code (#x1A000002)
     :apsr #x40000000
     :expect (:pc #x1004 :apsr #x40000000))

    ;; Branch with link: the return address is the next instruction.
    (:id "bl 0x1010"
     :pc #x1000 :code (#xEB000002)
     :expect (:pc #x1010 :regs ((14 . #x1004))))

    ;; An instruction the model does not support yet decodes to an error.
    (:id "sxtb r0, r0 (unsupported)"
     :pc #x1000 :code (#xE6AF0070)
     :expect (:error :decoding-error))

    ;; Before ARMv6, a multiply whose destination equals its first source is
    ;; UNPREDICTABLE, which the model reports as an error.
    (:id "mul r0, r0, r1 on ARMv4"
     :arch 4
     :pc #x1000 :code (#xE0000190)
     :regs ((0 . 3) (1 . 5))
     :expect (:error :unpredictable))))

;; All smoke vectors must pass, and no field may depend on an UNKNOWN.  On
;; failure, the mismatches are printed.
(assert-event
  (mv-let (real unknown-dependent)
    (run-vectors *smoke-vectors*)
    (or (and (null real) (null unknown-dependent))
        (cw "Smoke test failures: real ~x0, unknown-dependent ~x1~%"
            real unknown-dependent))))

;; Two vectors whose results include UNKNOWN values.  The harness runs every
;; vector under two sources of UNKNOWN values and reports the fields that
;; change between the runs as UNKNOWN-dependent.  Here those must be exactly
;; the fields holding UNKNOWN values, and nothing else may mismatch.

(defconst *unknown-vectors*
  '(;; STM with writeback whose base register is in the list but is not the
    ;; lowest: r0 is stored at 0x2000, the word stored at 0x2004 is UNKNOWN,
    ;; and r1 is written back.  The expectation for 0x2004 is a placeholder.
    (:id "stmia r1!, {r0, r1}"
     :pc #x1000 :code (#xE8A10003)
     :regs ((0 . #x11) (1 . #x2000))
     :expect (:pc #x1004
              :regs ((1 . #x2008))
              :mem ((#x2000 4 #x11) (#x2004 4 0))))

    ;; On ARMv4 a flag-setting multiply leaves C UNKNOWN.
    (:id "muls r3, r5, r4 on ARMv4"
     :arch 4
     :pc #x1000 :code (#xE0130495)
     :regs ((4 . 6) (5 . 7))
     :expect (:pc #x1004 :regs ((3 . 42)) :apsr 0))))

(assert-event
  (mv-let (real unknown-dependent)
    (run-vectors *unknown-vectors*)
    (or (and (null real)
             (equal unknown-dependent
                    '(("stmia r1!, {r0, r1}" (:mem #x2004))
                      ("muls r3, r5, r4 on ARMv4" :apsr))))
        (cw "UNKNOWN test failures: real ~x0, unknown-dependent ~x1~%"
            real unknown-dependent))))
