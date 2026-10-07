; Smoke tests for the ARM32 model, run through the test harness
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (non-gcl)

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

    ;; Swap a word: all 32 bits of r1 are stored, bit 31 included, and the
    ;; old word is loaded into r0.
    (:id "swp r0, r1, [r2]"
     :pc #x1000 :code (#xE1020091)
     :regs ((1 . #x87654321) (2 . #x2000))
     :mem ((#x2000 4 #x11223344))
     :expect (:pc #x1004
              :regs ((0 . #x11223344))
              :mem ((#x2000 4 #x87654321))))

    ;; Swap a byte: all 8 bits of the low byte of r1 are stored, and the old
    ;; byte is loaded into r0, zero-extended.
    (:id "swpb r0, r1, [r2]"
     :pc #x1000 :code (#xE1420091)
     :regs ((1 . #x123456AB) (2 . #x2000))
     :mem ((#x2000 1 #x5C))
     :expect (:pc #x1004
              :regs ((0 . #x5C))
              :mem ((#x2000 1 #xAB))))

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

;; Every smoke vector must pass.  The summary is printed either way.
(assert-event
  (let ((summary (summarize-vectors "smoke" *smoke-vectors* nil nil)))
    (prog2$ (print-summary summary 10 nil)
            (equal (cdr (assoc-eq :pass (report-get :counts summary nil)))
                   (len *smoke-vectors*)))))

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
  (let ((summary (summarize-vectors "smoke UNKNOWN" *unknown-vectors* nil nil)))
    (prog2$ (print-summary summary 10 nil)
            (and (check-summary summary)
                 (equal (report-get :unknown summary nil)
                        '(("stmia r1!, {r0, r1}" (:mem #x2004))
                          ("muls r3, r5, r4 on ARMv4" :apsr)))))))

;; Vectors for the GE bits of the APSR, which check-vector compares only from
;; ARMv6 (they are reserved before ARMv6), whatever the :apsr-mask.  MSR
;; APSR_g, r0 writes them from r0 on every version in the model.

(defconst *ge-vectors*
  '(;; Before ARMv6: not compared, so an expected 0 passes.
    (:id "msr APSR_g, r0 on ARMv4, GE of 0 expected"
     :arch 4
     :pc #x1000 :code (#xE124F000)
     :regs ((0 . #x000F0000))
     :expect (:pc #x1004 :apsr 0 :apsr-mask #xF80F0000))

    ;; From ARMv6: compared, so only the written value passes.
    (:id "msr APSR_g, r0 on ARMv6, GE of #xF expected"
     :arch 6
     :pc #x1000 :code (#xE124F000)
     :regs ((0 . #x000F0000))
     :expect (:pc #x1004 :apsr #x000F0000 :apsr-mask #xF80F0000))

    (:id "msr APSR_g, r0 on ARMv6, GE of 0 expected"
     :arch 6
     :pc #x1000 :code (#xE124F000)
     :regs ((0 . #x000F0000))
     :expect (:pc #x1004 :apsr 0 :apsr-mask #xF80F0000))))

(assert-event
  (let ((summary (summarize-vectors "smoke GE" *ge-vectors* nil nil)))
    (prog2$ (print-summary summary 10 nil)
            (and (equal (cdr (assoc-eq :pass (report-get :counts summary nil)))
                        2)
                 (equal (report-get :mismatches summary nil)
                        '(("msr APSR_g, r0 on ARMv6, GE of 0 expected"
                           :msr-register #xE124F000
                           (:apsr :expected 0 :actual #x000F0000))))))))

;; Vectors for the outcome classes that the model's errors decide (see
;; error-class in harness.lisp), and mismatches that waivers excuse or do not.
;; Each expects what another implementation might have done.

(defconst *class-vectors*
  '(;; UNPREDICTABLE on ARMv4, which may trap: pass.
    (:id "mul r0, r0, r1 on ARMv4, trap expected"
     :arch 4
     :pc #x1000 :code (#xE0000190)
     :expect (:trap :undefined))

    ;; UNPREDICTABLE on ARMv4, and the other implementation computed a
    ;; result: unpredictable, since nothing can be compared.
    (:id "mul r0, r0, r1 on ARMv4, result expected"
     :arch 4
     :pc #x1000 :code (#xE0000190)
     :regs ((0 . 3) (1 . 5))
     :expect (:pc #x1004 :regs ((0 . 15))))

    ;; A permanently undefined instruction, which the decoder rejects:
    ;; coverage gap.
    (:id "udf #0, trap expected"
     :pc #x1000 :code (#xE7F000F0)
     :expect (:trap :undefined))

    ;; A supervisor call, which the model does not model: unsupported.
    (:id "svc #0, trap expected"
     :pc #x1000 :code (#xEF000000)
     :expect (:trap :svc))

    ;; An instruction the model executes although a trap is expected:
    ;; mismatch, which the first waiver below excuses.
    (:id "adds r0, r1, r2, trap expected"
     :pc #x1000 :code (#xE0910002)
     :expect (:trap :undefined))

    ;; A store of the PC, expecting the instruction address plus 12, as on
    ;; the ARM7TDMI; the model stores plus 8, which is also permitted before
    ;; ARMv7: mismatch, which the second waiver below excuses.
    (:id "str pc, [r1] on ARMv4, PC+12 expected"
     :arch 4
     :pc #x1000 :code (#xE581F000)
     :regs ((1 . #x3000))
     :expect (:pc #x1004 :mem ((#x3000 4 #x100C))))

    ;; The same store, expecting a value that the second waiver's PC offsets
    ;; do not cover: mismatch, which no waiver excuses.
    (:id "str pc, [r1] on ARMv4, PC+16 expected"
     :arch 4
     :pc #x1000 :code (#xE581F000)
     :regs ((1 . #x3000))
     :expect (:pc #x1004 :mem ((#x3000 4 #x1010))))

    ;; The first store on ARMv7, which requires plus 8, so expecting plus 12
    ;; is wrong: mismatch, which the second waiver's :max-arch keeps it from
    ;; excusing.
    (:id "str pc, [r1] on ARMv7, PC+12 expected"
     :arch 7
     :pc #x1000 :code (#xE581F000)
     :regs ((1 . #x3000))
     :expect (:pc #x1004 :mem ((#x3000 4 #x100C))))

    ;; A store of several registers, the PC among them, expecting the
    ;; instruction address plus 12 in the PC's slot: mismatch, which the
    ;; third waiver below excuses.
    (:id "stmia r1, {r0, pc} on ARMv4, PC+12 expected"
     :arch 4
     :pc #x1000 :code (#xE8818001)
     :regs ((0 . #x5555) (1 . #x3000))
     :expect (:pc #x1004 :mem ((#x3000 4 #x5555) (#x3004 4 #x100C))))

    ;; The same store, expecting also 4 more than r0 in r0's slot.  The third
    ;; waiver excuses the PC's slot but not r0's, whose value is not computed
    ;; from the PC: mismatch.
    (:id "stmia r1, {r0, pc} on ARMv4, r0+4 expected"
     :arch 4
     :pc #x1000 :code (#xE8818001)
     :regs ((0 . #x5555) (1 . #x3000))
     :expect (:pc #x1004 :mem ((#x3000 4 #x5559) (#x3004 4 #x100C))))))

(defconst *class-waivers*
  '((:mask #x0FE00000 :value #x00800000 :field :trap
     :reason :oracle-limitation :cite "smoke.lisp"
     :note "Excuses the ADD above, to test waivers.")
    (:mask #x0C50F000 :value #x0400F000 :field :mem
     :expected-pc-offset 12 :actual-pc-offset 8 :max-arch 6
     :reason :implementation-defined :cite "DDI 0406C.d A2.3, page A2-47"
     :note "Excuses the ARMv4 STR of PC+12 above, but not the ARMv7 one.")
    (:mask #x0E508000 :value #x08008000 :field :mem
     :expected-pc-offset 12 :actual-pc-offset 8 :max-arch 6
     :reason :implementation-defined :cite "DDI 0406C.d A2.3, page A2-47"
     :note "Excuses the PC's slot of the STMs above.")
    (:name :sub-immediate :field :apsr :bits #x20000000
     :reason :oracle-limitation :cite "smoke.lisp"
     :note "Matches nothing, to test the report of unused waivers.")))

(assert-event
  (let ((summary (summarize-vectors "smoke classes" *class-vectors*
                                    *class-waivers* nil)))
    (prog2$ (print-summary summary 10 nil)
            (and (equal (report-get :counts summary nil)
                        '((:pass . 1)
                          (:mismatch . 3)
                          (:waived . 3)
                          (:unknown-dependent . 0)
                          (:coverage-gap . 1)
                          (:unsupported . 1)
                          (:unpredictable . 1)
                          (:skipped . 0)))
                 (equal (report-get :mismatches summary nil)
                        '(("str pc, [r1] on ARMv4, PC+16 expected"
                           :str-immediate #xE581F000
                           ((:mem #x3000) :expected #x1010 :actual #x1008))
                          ("str pc, [r1] on ARMv7, PC+12 expected"
                           :str-immediate #xE581F000
                           ((:mem #x3000) :expected #x100C :actual #x1008))
                          ("stmia r1, {r0, pc} on ARMv4, r0+4 expected"
                           :stm/stmia/stmea #xE8818001
                           ((:mem #x3000) :expected #x5559 :actual #x5555))))
                 (equal (report-get :unused-waivers summary nil)
                        (last *class-waivers*))))))
