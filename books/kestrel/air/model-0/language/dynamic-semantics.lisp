; AIR Library
; Model 0: Dynamic Semantics
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributor: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "abstract-syntax")
(include-book "static-semantics")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/fty/ubyte8" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (model-0)
  :short "Dynamic semantics of Model 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "The dynamic semantics defines how Model 0 programs execute.
     We define the runtime types (8-bit bytes, VM state),
     byte arithmetic with wrap-around,
     and an interpreter that steps through the program."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Byte Arithmetic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-incr ((x ubyte8p))
  :returns (result ubyte8p
                   :hints (("Goal" :in-theory (enable ubyte8p-of-mod-256))))
  :short "Increment a byte with wrap-around."
  :long
  (xdoc::topstring
   (xdoc::p
    "Computes @('(x + 1) mod 256'). When @('x = 255'), the result is 0."))
  (mbe :logic (mod (1+ (nfix x)) 256)
       :exec (mod (1+ x) 256)))

(define byte-decr ((x ubyte8p))
  :returns (result ubyte8p
                   :hints (("Goal" :in-theory (enable ubyte8p-of-mod-256))))
  :short "Decrement a byte with wrap-around."
  :long
  (xdoc::topstring
   (xdoc::p
    "Computes @('(x - 1) mod 256'). When @('x = 0'), the result is 255."))
  (mbe :logic (mod (1- (nfix x)) 256)
       :exec (mod (1- x) 256)))

;; Key properties
(defthm byte-incr-wrap
  (implies (ubyte8p x)
           (equal (byte-incr x)
                  (if (= x 255) 0 (1+ x))))
  :hints (("Goal" :in-theory (enable byte-incr ubyte8p))))

(defthm byte-decr-wrap
  (implies (ubyte8p x)
           (equal (byte-decr x)
                  (if (= x 0) 255 (1- x))))
  :hints (("Goal" :in-theory (enable byte-decr ubyte8p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; VM State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod vm-state
  :short "Fixtype of Model 0 VM states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The VM state consists of:")
   (xdoc::ul
    (xdoc::li "@('pc') - the program counter (a natural number)")
    (xdoc::li "@('acc') - the 8-bit accumulator register")
    (xdoc::li "@('halted') - a flag indicating whether execution has halted")))
  ((pc     natp      :default 0)
   (acc    ubyte8    :default 0)
   (halted booleanp  :default nil))
  :pred vm-state-p)

(define initial-state ((input ubyte8p))
  :returns (st vm-state-p)
  :short "Create an initial Model 0 VM state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial state has @('pc = 0'), @('halted = nil'),
     and the accumulator set to the given input value."))
  (make-vm-state :pc 0 :acc input :halted nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Single-Step Execution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step1 ((st vm-state-p) (prog program-p))
  :returns (new-st vm-state-p)
  :guard (< (vm-state->pc st) (len prog))
  :short "Execute one step of the Model 0 VM."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the VM is halted, the state is unchanged (frozen).
     Otherwise, we fetch the current instruction and execute it:")
   (xdoc::ul
    (xdoc::li "@('INCR') - increment accumulator, advance PC")
    (xdoc::li "@('DECR') - decrement accumulator, advance PC")
    (xdoc::li "@('HALT') - set halted flag, freeze PC and accumulator")))
  (if (vm-state->halted st)
      (vm-state-fix st)
    (let ((op (fetch prog (vm-state->pc st))))
      (opcode-case op
        :incr (make-vm-state
               :pc (1+ (vm-state->pc st))
               :acc (byte-incr (vm-state->acc st))
               :halted nil)
        :decr (make-vm-state
               :pc (1+ (vm-state->pc st))
               :acc (byte-decr (vm-state->acc st))
               :halted nil)
        :halt (make-vm-state
               :pc (vm-state->pc st)
               :acc (vm-state->acc st)
               :halted t))))
  :hooks (:fix))

;; Key property: for well-formed programs, step1 preserves PC bounds.
;; This is needed for guard verification of run.
(defthm step1-preserves-pc-bound
  (implies (and (program-well-formed-p prog)
                (< (vm-state->pc st) (len prog)))
           (< (vm-state->pc (step1 st prog)) (len prog)))
  :hints (("Goal" :in-theory (enable step1 fetch
                                     program-well-formed-p
                                     program-nonempty-p
                                     program-ends-with-halt-p
                                     nth-of-len-minus-1-is-car-last))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multi-Step Execution (Interpreter)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define run ((st vm-state-p) (prog program-p) (limit natp))
  :returns (final-st vm-state-p)
  :measure (nfix limit)
  :guard (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
  :short "Run the Model 0 VM for up to @('limit') steps."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executes steps until either the VM halts or the limit is reached.
     The limit parameter ensures termination of the ACL2 function;
     it does not correspond to any runtime data of the VM."))
  (if (or (zp limit)
          (vm-state->halted st))
      (vm-state-fix st)
    (run (step1 st prog) prog (1- limit)))
  :prepwork ((local (in-theory (enable nfix))))
  :hooks (:fix))

(defruled same-final-halted-state-for-diff-limits
  :short "Different limits that reach halted states reach the same state."
  (implies (and (vm-state->halted (run st prog limit1))
                (vm-state->halted (run st prog limit2)))
           (equal (run st prog limit1)
                  (run st prog limit2)))
  :induct t
  :enable run)

(defruled halted-limit-monotone
  :short "If running with a limit reaches a halted state,
          so does any larger limit."
  (implies (and (>= (nfix limit1)
                    (nfix limit))
                (vm-state->halted (run st prog limit)))
           (vm-state->halted (run st prog limit1)))
  :induct t
  :enable (run nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define run* ((st vm-state-p) (prog program-p) (limit natp))
  :guard (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
  :returns (final-st vm-state-p)
  :short "Alternative definition of running."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee run), but it always performs @('limit') recursions,
     even if a halted state is reached.
     That is, the termination test is just that the limit is 0.")
   (xdoc::p
    "It is functionally equivalent to @(tsee run), as we prove below.
     The reason for introducting it is that
     it facilitates certain induction proofs."))
  (if (zp limit)
      (vm-state-fix st)
    (run* (step1 st prog) prog (1- limit)))
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defruled run*-when-halted
    (implies (vm-state->halted st)
             (equal (run* st prog limit)
                    (vm-state-fix st)))
    :induct t
    :enable step1)

  (defruled run*-is-run
    (equal (run* st prog limit)
           (run st prog limit))
    :induct t
    :enable (run run*-when-halted)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Termination
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define terminates-with-limit-p ((prog program-p) (input ubyte8p) (limit natp))
  :guard (program-well-formed-p prog)
  :returns (yes/no booleanp)
  :short "Check if a program terminates on an input for a limit."
  (vm-state->halted (run (make-vm-state :pc 0 :acc input :halted nil)
                         prog
                         limit))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk terminatesp ((prog program-p) (input ubyte8p))
  :guard (program-well-formed-p prog)
  :returns (yes/no booleanp)
  :short "Check if a program terminates on some input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although programs in M0 always terminate,
     that is not the case for more complex languages.
     We introduce this and related notions for M0,
     in a form that applies to more complex languages."))
  (exists (limit)
          (and (natp limit)
               (terminates-with-limit-p prog input limit)))

  ///

  (fty::deffixequiv-sk terminatesp
    :args ((prog program-p) (input ubyte8p)))

  (defrule natp-of-terminatesp-witness
    (implies (terminatesp prog input)
             (natp (terminatesp-witness prog input)))
    :rule-classes (:rewrite :type-prescription))

  (defrule terminates-with-limit-p-of-terminatesp-witness
    (implies (terminatesp prog input)
             (terminates-with-limit-p prog
                                      input
                                      (terminatesp-witness prog input))))

  (defrule halted-of-run-of-terminatesp-witness
    (implies (terminatesp prog input)
             (vm-state->halted (run (vm-state 0 input nil)
                                    prog
                                    (terminatesp-witness prog input))))
    :enable terminates-with-limit-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define termination-limit ((prog program-p) (input ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input))
  :returns (limit natp :rule-classes (:rewrite :type-prescription))
  :short "A limit that suffices for a terminating program to terminate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially the witness function introduced by @(tsee terminatesp),
     but it has a stronger guard and fixes its inputs."))
  (if (mbt (terminatesp prog input))
      (terminatesp-witness (program-fix prog) (ubyte8-fix input))
    0)
  :hooks (:fix)
  :prepwork ((local (in-theory (disable natp))))

  ///

  (defrule terminates-with-limit-p-of-termination-limit
    (implies (terminatesp prog input)
             (terminates-with-limit-p prog
                                      input
                                      (termination-limit prog input)))
    :use (:instance lemma
                    (prog (program-fix prog))
                    (input (ubyte8-fix input)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (program-p prog)
                     (ubyte8p input)
                     (terminatesp prog input))
                (terminates-with-limit-p prog
                                         input
                                         (termination-limit prog input))))))

  (defrule halted-of-run-of-termination-limit
    (implies (terminatesp prog input)
             (vm-state->halted (run (vm-state 0 input nil)
                                    prog
                                    (termination-limit prog input))))
    :use (:instance lemma
                    (prog (program-fix prog))
                    (input (ubyte8-fix input)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (program-p prog)
                     (ubyte8p input)
                     (terminatesp prog input))
                (vm-state->halted (run (vm-state 0 input nil)
                                       prog
                                       (termination-limit prog input))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-termination-limit ((prog program-p) (input ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input))
  :returns (limit natp)
  :short "Mininum termination limit for a terminating program."
  :long
  (xdoc::topstring
   (xdoc::p
    "While @(tsee termination-limit) returns
     some (unspcified but fixed) limit
     sufficient to run a terminating program to completion,
     here we return the smallest such limit,
     which always exists."))
  (min-termination-limit-loop prog input 0)
  :hooks (:fix)

  :prepwork
  ((define min-termination-limit-loop ((prog program-p)
                                       (input ubyte8p)
                                       (limit natp))
     :guard (and (program-well-formed-p prog)
                 (terminatesp prog input))
     :returns (limit natp)
     :parents nil
     (b* (((unless (mbt (terminatesp prog input))) 0)
          ((when (terminates-with-limit-p prog input limit))
           (nfix limit))
          ((when (>= (nfix limit) (termination-limit prog input)))
           (nfix limit)))
       (min-termination-limit-loop prog input (1+ (nfix limit))))
     :measure (nfix (- (termination-limit prog input) (nfix limit)))
     :hints (("Goal" :in-theory (enable nfix fix)))
     :hooks (:fix)

     ///

     (defrule terminates-with-limit-p-of-min-termination-limit-loop
       (implies (and (terminatesp prog input)
                     (natp limit)
                     (<= limit (termination-limit prog input)))
                (terminates-with-limit-p
                 prog input (min-termination-limit-loop prog input limit)))
       :induct t)

     (defrule halted-of-run-of-min-termination-limit-loop
       (implies (and (terminatesp prog input)
                     (natp limit)
                     (<= limit (termination-limit prog input)))
                (vm-state->halted
                 (run (vm-state 0 input nil)
                      prog
                      (min-termination-limit-loop prog input limit))))
       :induct t
       :enable (run
                terminates-with-limit-p
                nfix))

     (defruled not-halted-at-min-termination-limit-loop-minus-1
       (b* ((min-limit (min-termination-limit-loop prog input limit)))
         (implies (and (terminatesp prog input)
                       (natp limit)
                       (> min-limit limit))
                  (not (vm-state->halted
                        (run (vm-state 0 input nil) prog (1- min-limit))))))
       :induct t
       :enable (terminates-with-limit-p
                fix))

     (defrule min-termination-limit-loop-is-min
       (implies (and (terminates-with-limit-p prog input limit1)
                     (natp limit1)
                     (natp limit)
                     (>= (nfix limit1) (nfix limit)))
                (>= (nfix limit1)
                    (min-termination-limit-loop prog input limit)))
       :rule-classes ((:linear
                       :trigger-terms
                       ((min-termination-limit-loop prog input limit))))
       :induct t)))

  ///

  (defrule terminates-with-limit-p-of-min-termination-limit
    (implies (terminatesp prog input)
             (terminates-with-limit-p
              prog input (min-termination-limit prog input))))

  (defrule halted-of-run-of-min-termination-limit
    (implies (terminatesp prog input)
             (vm-state->halted (run (vm-state 0 input nil)
                                    prog
                                    (min-termination-limit prog input)))))

  (defruled not-halted-at-min-termination-limit-minus-1
    (b* ((min-limit (min-termination-limit prog input)))
      (implies (and (terminatesp prog input)
                    (> min-limit 0))
               (not (vm-state->halted
                     (run (vm-state 0 input nil) prog (1- min-limit))))))
    :enable not-halted-at-min-termination-limit-loop-minus-1)

  (defrule min-termination-limit-is-min
    (implies (terminates-with-limit-p prog input limit)
             (>= (nfix limit)
                 (min-termination-limit prog input)))
    :use (:instance min-termination-limit-loop-is-min
                    (limit1 (nfix limit))
                    (limit 0))
    :disable min-termination-limit-loop-is-min
    :rule-classes ((:linear
                    :trigger-terms
                    ((min-termination-limit prog input))))))
