; AIR Library
; Model 0: Execution Traces
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributor: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "../language/input-output-semantics")

(include-book "kestrel/fty/ubyte8-list" :dir :system)

(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ traces
  :parents (model-0)
  :short "Execution traces for Model 0 AIR."
  :long
  (xdoc::topstring
   (xdoc::p
    "An execution trace is a table where each row represents
     one step of VM execution. The trace captures the complete
     execution history from initial state to halted state.")
   (xdoc::p
    "Trace rows contain the same information as VM states,
     plus the opcode being executed. All values are embedded
     into the Koala Bear field for AIR constraint verification.
     However, the traces that we define here are
     independent from the Koala Bear field, i.e. more general;
     they are expressed in the vocabulary of the M0 language definition,
     without reference to fields.
     Traces are related to prime fields elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace Row
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trace-row
  :short "Fixtype of trace rows."
  :long
  (xdoc::topstring
   (xdoc::p
    "A trace row captures the VM state at one execution step:")
   (xdoc::ul
    (xdoc::li "@('pc') - program counter")
    (xdoc::li "@('acc') - accumulator value (8-bit)")
    (xdoc::li "@('opcode') - instruction being executed")
    (xdoc::li "@('halted') - whether execution has halted")))
  ((pc     natp)
   (acc    ubyte8)
   (opcode opcode)
   (halted booleanp))
  :pred trace-row-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist trace
  :short "Fixtype of execution traces."
  :long
  (xdoc::topstring
   (xdoc::p
    "A trace is a list of trace rows, one per execution step.
     The first row is the initial state; the last row is the halted state."))
  :elt-type trace-row
  :true-listp t
  :elementp-of-nil nil
  :pred trace-p)

(std::defprojection trace-pcs ((x trace-p))
  :returns (pcs nat-listp)
  :short "Lift @(tsee trace-row->pc) to traces."
  (trace-row->pc x)
  ///
  (fty::deffixequiv trace-pcs :args ((x trace-p))))

(std::defprojection trace-accs ((x trace-p))
  :returns (accs ubyte8-listp)
  :short "Lift @(tsee trace-row->acc) to traces."
  (trace-row->acc x)
  ///
  (fty::deffixequiv trace-accs :args ((x trace-p)))

  (defruled last-of-trace-accs
    (equal (last (trace-accs tr))
           (trace-accs (last tr)))
    :induct t
    :enable last))

(std::defprojection trace-opcodes ((x trace-p))
  :returns (opcodes program-p)
  :short "Lift @(tsee trace-row->opcode) to traces."
  (trace-row->opcode x)
  ///
  (fty::deffixequiv trace-opcodes :args ((x trace-p))))

(std::defprojection trace-halteds ((x trace-p))
  :short "Lift @(tsee trace-row->halted) to traces."
  :returns (halteds boolean-listp)
  (trace-row->halted x)
  ///
  (fty::deffixequiv trace-halteds :args ((x trace-p)))

  (defruled butlast-of-trace-halteds
    (equal (butlast (trace-halteds tr) n)
           (trace-halteds (butlast tr n)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define trace-first-row ((tr trace-p))
  :returns (row trace-row-p)
  :guard (consp tr)
  :short "Get the first row of a trace."
  (trace-row-fix (car tr)))

(define trace-last-row ((tr trace-p))
  :returns (row trace-row-p)
  :guard (consp tr)
  :short "Get the last row of a trace."
  (trace-row-fix (car (last tr))))

(define row-to-state ((row trace-row-p))
  :returns (st vm-state-p)
  :short "Extract state from a trace row."
  (vm-state (trace-row->pc row)
            (trace-row->acc row)
            (trace-row->halted row))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trace Generation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define new-trace-row ((st vm-state-p) (prog program-p))
  :returns (row trace-row-p)
  :guard (< (vm-state->pc st) (len prog))
  :short "Create a trace row from a VM state."
  (make-trace-row
   :pc (vm-state->pc st)
   :acc (vm-state->acc st)
   :opcode (fetch prog (vm-state->pc st))
   :halted (vm-state->halted st))
  :hooks (:fix)

  ///

  (defrule row-to-state-of-new-trace-row
    (equal (row-to-state (new-trace-row st prog))
           (vm-state-fix st))
    :enable row-to-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define generate-trace ((st vm-state-p) (prog program-p) (limit natp))
  :returns (tr trace-p)
  :measure (nfix limit)
  :guard (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
  :short "Generate an execution trace."
  :long
  (xdoc::topstring
   (xdoc::p
    "Generates a trace by recording the state at each step
     until the VM halts or the limit is reached.
     Each row captures the state before executing the instruction."))
  (let ((row (new-trace-row st prog)))
    (if (or (zp limit)
            (vm-state->halted st))
        (list row)
      (cons row
            (generate-trace (step1 st prog) prog (1- limit)))))
  :hooks (:fix)

  ///

  (defret all-<-of-trace-pcs-of-generate-trace
    (all-< (trace-pcs tr) (len prog))
    :hyp (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
    :hints (("Goal"
             :induct t
             :in-theory (enable trace-pcs
                                all-<
                                new-trace-row)))))

(defruled last-row-of-generate-trace-is-run
  :short "Relation between trace generation and program running."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last row of a generated trace
     (which always exists because @(tsee generate-trace)
     always returns a non-empty list),
     is the same one obtained from the final state of a run."))
  (equal (car (last (generate-trace st prog limit)))
         (new-trace-row (run st prog limit) prog))
  :induct t
  :enable (generate-trace
           run
           new-trace-row))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variant Trace Generation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define generate-trace* ((st vm-state-p) (prog program-p) (limit natp))
  :guard (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
  :returns (tr trace-p)
  :short "Variant trace generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee generate-trace*),
     but it always generates a trace of length @('limit + 1'),
     by replicating the final halted state row,
     if a halted state is reached.")
   (xdoc::p
    "This is introduced also because
     it facilitates certain induction proofs."))
  (let ((row (new-trace-row st prog)))
    (if (zp limit)
        (list row)
      (cons row
            (generate-trace* (step1 st prog) prog (1- limit)))))
  :hooks (:fix)

  ///

  (defret len-of-generate-trace*
    (equal (len tr)
           (1+ (nfix limit)))
    :hints (("Goal" :induct t :in-theory (enable nfix fix))))

  (defret all-<-of-trace-pcs-of-generate-trace*
    (all-< (trace-pcs tr) (len prog))
    :hyp (and (program-well-formed-p prog)
              (< (vm-state->pc st) (len prog)))
    :hints (("Goal"
             :induct t
             :in-theory (enable trace-pcs
                                all-<
                                new-trace-row))))

  (defruled row-to-state-of-car-of-generate-trace*
    (equal (row-to-state (car (generate-trace* st prog limit)))
           (vm-state-fix st))
    :induct t
    :enable (row-to-state new-trace-row))

  (defrule trace-row->pc-of-car-of-generate-trace*
    (equal (trace-row->pc (car (generate-trace* st prog limit)))
           (vm-state->pc st))
    :induct t
    :enable new-trace-row)

  (defrule trace-row->halted-of-car-of-generate-trace*
    (equal (trace-row->halted (car (generate-trace* st prog limit)))
           (vm-state->halted st))
    :induct t
    :enable new-trace-row))

(defruled last-row-of-generate-trace*-is-run*
  :short "Relation between variant trace generation and program running,
          expressed as @(tsee run*)."
  (equal (car (last (generate-trace* st prog limit)))
         (new-trace-row (run* st prog limit) prog))
  :induct t
  :enable (generate-trace*
           run*
           new-trace-row))

(defruled last-row-of-generate-trace*-is-run
  :short "Relation between variant trace generation and program running,
          expressed as @(tsee run)."
  (equal (car (last (generate-trace* st prog limit)))
         (new-trace-row (run st prog limit) prog))
  :enable (last-row-of-generate-trace*-is-run*
           run*-is-run))

(defruled row-to-state-of-last-of-generate-trace*-is-run*
  :short "Variant formulation of @(tsee last-row-of-generate-trace*-is-run*)."
  (equal (row-to-state (car (last (generate-trace* st prog limit))))
         (run* st prog limit))
  :enable last-row-of-generate-trace*-is-run*)

(defruled row-to-state-of-last-of-generate-trace*-is-run
  :short "Variant formulation of @(tsee last-row-of-generate-trace*-is-run)."
  (equal (row-to-state (car (last (generate-trace* st prog limit))))
         (run st prog limit))
  :enable (row-to-state-of-last-of-generate-trace*-is-run*
           run*-is-run))

(defruled generate-trace*-is-generate-trace
  :short "Relation between trace generation and variant trace generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two are equal when all but possibly the last row
     of the trace generated by @(tsee generate-trace*)
     have the halted flags equal to @('nil').
     That is, each such row can generate another row
     in @(tsee generate-trace), without stopping in a halted state."))
  (b* ((tr (generate-trace* st prog limit)))
    (implies (all-null (butlast (trace-halteds tr) 1))
             (equal tr (generate-trace st prog limit))))
  :induct t
  :enable (generate-trace
           generate-trace*
           fix
           new-trace-row))

(defruled all-null-of-generate-trace*-halteds-when-last-not-halted
  :short "If running with a limit does not reach a halted state,
          all the rows in the corresponding trace are not halted."
  (implies (not (vm-state->halted (run st prog limit)))
           (all-null (trace-halteds (generate-trace* st prog limit))))
  :induct t
  :enable (run
           generate-trace*
           new-trace-row))

(defruled generate-trace*-prefix-of-geq-limit
  :short "The trace generated for a limit is a prefix of
          the one generated by a larger limit,
          specifically the prefix with length the smaller limit plus one."
  (implies (and (natp limit1)
                (natp limit)
                (>= limit1 limit))
           (equal (generate-trace* st prog limit)
                  (take (1+ limit) (generate-trace* st prog limit1))))
  :induct t
  :enable generate-trace*)

(defruled trace-opcodes-of-generate-trace*
  :short "The opcodes of a generated trace can be derived from
          the program counters of the trace and the program."
  (equal (trace-opcodes (generate-trace* st prog limit))
         (fetch-list prog (trace-pcs (generate-trace* st prog limit))))
  :induct t
  :enable (generate-trace*
           new-trace-row))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Minimal Trace Generation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define generate-min-trace ((prog program-p) (input ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input))
  :returns (tr trace-p)
  :short "Create the minimal trace for a terminating program."
  :long
  (xdoc::topstring
   (xdoc::p
    "By starting in the initial state (for the given input),
     and passing the minimum terminating limit,
     we obtain the execution trace,
     without extra no-op steps after the program has halted."))
  (generate-trace (make-vm-state :pc 0 :acc input :halted nil)
                  prog
                  (min-termination-limit prog input))
  :hooks (:fix)

  ///

  (defret all-<-of-trace-pcs-of-generate-min-trace
    (all-< (trace-pcs tr) (len prog))
    :hyp (program-well-formed-p prog)
    :hints (("Goal" :in-theory (enable program-well-formed-p
                                       program-nonempty-p)))))

(defruled generate-min-trace-is-generate-trace*-of-min-termination-limit
  :short "Relation between @(tsee generate-min-trace)
          and @(tsee generate-trace*)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The minimal trace is generated by @(tsee generate-trace*)
     on the minimum termination limit, starting with the initial state."))
  (implies (terminatesp prog input)
           (equal (generate-min-trace prog input)
                  (generate-trace* (vm-state 0 input nil)
                                   prog
                                   (min-termination-limit prog input))))
  :disable butlast
  :enable (generate-min-trace
           generate-trace*-is-generate-trace
           all-null-of-butlast-1-of-generate-trace*-halteds)

  :prep-lemmas

  ((defruled generate-trace*-of-limit-m1-is-butlast-1-of-limit
     (implies (not (zp limit))
              (equal (generate-trace* st prog (1- limit))
                     (butlast (generate-trace* st prog limit) 1)))
     :use ((:instance generate-trace*-prefix-of-geq-limit
                      (limit (1- limit))
                      (limit1 limit))
           (:instance take-of-len-minus-1-is-butlast-1
                      (x (generate-trace* st prog limit)))))

   (defruled all-null-of-butlast-1-of-generate-trace*-halteds
     (implies (terminatesp prog input)
              (all-null (butlast
                         (trace-halteds
                          (generate-trace* (vm-state 0 input nil)
                                           prog
                                           (min-termination-limit prog input)))
                         1)))
     :use ((:instance generate-trace*-of-limit-m1-is-butlast-1-of-limit
                      (st (vm-state 0 input nil))
                      (limit (min-termination-limit prog input)))
           (:instance all-null-of-generate-trace*-halteds-when-last-not-halted
                      (st (vm-state 0 input nil))
                      (limit (1- (min-termination-limit prog input))))
           (:instance not-halted-at-min-termination-limit-minus-1)
           (:instance butlast-of-trace-halteds
                      (tr (generate-trace* (vm-state 0 input nil)
                                           prog
                                           (min-termination-limit prog input)))
                      (n 1))))))

(defrule len-of-generate-min-trace
  :short "The length of a minimal trace is one more than
          the minimum termination limit."
  (implies (terminatesp prog input)
           (equal (len (generate-min-trace prog input))
                  (1+ (min-termination-limit prog input))))
  :enable generate-min-trace-is-generate-trace*-of-min-termination-limit)

(defrule trace-row->acc-of-car-of-generate-min-trace
  :short "The accumulator in the first row of the minimal trace
          is equal to the input from which the trace is generated."
  (implies (terminatesp prog input)
           (equal (trace-row->acc (car (generate-min-trace prog input)))
                  (ubyte8-fix input)))
  :enable (generate-min-trace-is-generate-trace*-of-min-termination-limit
           row-to-state)
  :use (:instance row-to-state-of-car-of-generate-trace*
                  (st (vm-state 0 input nil))
                  (limit (min-termination-limit prog input))))

(defruled trace-opcodes-of-generate-min-trace
  :short "The opcodes of the minimal trace can be derived from
          the program counters of the trace and the program."
  (implies (terminatesp prog input)
           (equal (trace-opcodes (generate-min-trace prog input))
                  (fetch-list prog
                              (trace-pcs (generate-min-trace prog input)))))
  :enable (generate-min-trace-is-generate-trace*-of-min-termination-limit
           trace-opcodes-of-generate-trace*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define execution-path ((prog program-p) (input ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input))
  :returns (pcs nat-listp)
  :short "Execution path of a terminating program."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the sequence of program counters
     in the minimal trace of the program execution."))
  (trace-pcs (generate-min-trace prog input))
  :hooks (:fix)

  ///

  (more-returns
   (pcs consp :rule-classes :type-prescription))

  (defret all-<-of-execution-path
    (all-< pcs (len prog))
    :hyp (program-well-formed-p prog))

  (defret len-of-execution-path
    (equal (len pcs)
           (1+ (min-termination-limit prog input)))
    :hyp (terminatesp prog input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled program-output-as-generate-min-trace
  :short "Characterization of the input/output semantics in terms of traces."
  :long
  (xdoc::topstring
   (xdoc::p
    "Via the @(tsee last-row-of-generate-trace-is-run) property,
     we show that the input/output semantic function
     could be equivalently defined in terms of @(tsee generate-min-trace)."))
  (equal (program-output prog input)
         (trace-row->acc (car (last (generate-min-trace prog input)))))
  :enable (program-output
           generate-min-trace
           last-row-of-generate-trace-is-run
           new-trace-row))
