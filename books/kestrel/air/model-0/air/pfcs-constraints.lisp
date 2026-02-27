; AIR Library
; Model 0: PFCS Constraints
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "traces")
(include-book "field-encoding")

(include-book "kestrel/fty/ubyte8" :dir :system)
(include-book "projects/pfcs/abstract-syntax-operations" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pfcs-constraints
  :parents (model-0)
  :short "PFCS constraints that programs compile to."
  :long
  (xdoc::topstring
   (xdoc::p
    "Programs are compiled to constraints,
     which we define here using the PFCS formalism.")
   (xdoc::p
    "We define fixed PFCS constraints by parsing PFCS concrete syntax.
     We define parameterized PFCS constraints directly in abstract syntax,
     because currently parameterized PFCS do not have concrete syntax.")
   (xdoc::p
    "All the equality constraints have the form @('poly == 0'),
     where @('poly') is a polynomial.
     This is in line with the AIR format.")
   (xdoc::p
    "We use variable names like @('pc') @('acc')
     for program counters and accumulators,
     which are natural numbers, which are also field elements.
     We use variables names like @('op') for field encodings of opcodes,
     while we use variable names @('opcode') for opcodes themselves.
     We use variable names like @('hlt') for bit encodings of halted flags,
     while we use variable names like @('halted') for boolean flags.")
   (xdoc::p
    "We also define an explicit compilation from programs and inputs
     to constraints."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-initial ()
  :returns (pdef pfcs::definitionp)
  :short "Constraints on the initial row of the table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require execution to start at the beginning of the program,
     in a non-halted state."))
  (pfcs::parse-def
   "initial(pc, acc, op, hlt) := {
        pc == 0,
        hlt == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-final ()
  :returns (pdef pfcs::definitionp)
  :short "Constraints on the final row of the table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require execution to have terminated, i.e. the halted flag to be set."))
  (pfcs::parse-def
   "final(pc, acc, op, hlt) := {
        hlt - 1 == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-pc-transition ()
  :returns (pdef pfcs::definitionp)
  :short "Transition constraints on the program counter."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to each pair of consecutive rows.")
   (xdoc::p
    "Unless the halted flag is set or the opcode is HALT,
     the program counter is incremented by one.
     Otherwise, the program counter is unchanged."))
  (pfcs::parse-def
   "pc_transition(pc, op, hlt, pc_next) := {
        hlt * (pc_next - pc) == 0,
        (1 - hlt) * (op - 2) * (pc_next - pc - 1) == 0,
        op * (op - 1) * (pc_next - pc) == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-acc-transition ()
  :returns (pdef pfcs::definitionp)
  :short "Transition constraints on the accumulator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to each pair of consecutive rows.")
   (xdoc::p
    "If the halted flag is clear,
     an INCR instruction increments the accumulator, modulo 256.")
   (xdoc::p
    "If the halted flag is clear,
     a DECR instruction decrements the accumulator, modulo 256.")
   (xdoc::p
    "If the halted flag is clear,
     a HALT instruction leaves the accumulator unchanged.")
   (xdoc::p
    "If the halted flag is set, the accumulator is unchanged."))
  (pfcs::parse-def
   "acc_transition(acc, op, hlt, acc_next) := {
        (1 - hlt) * (op - 1) * (op - 2) *
            (acc + 1 - acc_next) * (256 - (acc + 1 - acc_next)) == 0,
        (1 - hlt) * op * (op - 2) *
            (acc + 255 - acc_next) * (256 - (acc + 255 - acc_next)) == 0,
        (1 - hlt) * op * (op - 1) * (acc_next - acc) ==  0,
        hlt * (acc_next - acc) == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-halted-transition ()
  :returns (pdef pfcs::definitionp)
  :short "Transition constraints on the halted flag."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to each pair of consecutive rows.")
   (xdoc::p
    "Unless the opcode is HALT, the halted flag is maintained.
     Otherwise, the halted flag is set."))
  (pfcs::parse-def
   "halted_transition(op, hlt, hlt_next) := {
        (op - 2) * (hlt_next - hlt) == 0,
        op * (op - 1) * (1 - hlt_next) == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-transition ()
  :returns (pdef pfcs::definitionp)
  :short "Transition constraints on
          program counter, accumulator, and halted flag."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to each pair of consecurive rows."))
  (pfcs::parse-def
   "transition(pc, acc, op, hlt, pc_next, acc_next, op_next, hlt_next) := {
        pc_transition(pc, op, hlt, pc_next),
        acc_transition(acc, op, hlt, acc_next),
        halted_transition(op, hlt, hlt_next)
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-bit ()
  :returns (pdef pfcs::definitionp)
  :short "Bit constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constrains a field element to be a bit, i.e. 0 or 1.
     It is used as part of the byte constraints;
     see motivation there."))
  (pfcs::parse-def
   "bit(x) := {
        x * (1 - x) == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-byte ()
  :returns (pdef pfcs::definitionp)
  :short "Byte constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constrains a field element to be a byte,
     i.e. expressible as the weighted sum of eight bits.")
   (xdoc::p
    "This could be parameterized over the number of bits,
     but for simplicity, and since there are only eight bits,
     we define it as fixed PFCS constraints for now.")
   (xdoc::p
    "This is used to constrain the accumulator values in a trace.
     It is actually not yet clear to us whether this condition
     would be (in a full system) captured as AIR constraints
     or in some other way external to the AIR constraints.
     For now we use AIR constraints for this."))
  (pfcs::parse-def
   "byte(x) := {
        bit(x0),
        bit(x1),
        bit(x2),
        bit(x3),
        bit(x4),
        bit(x5),
        bit(x6),
        bit(x7),
        x0 +
        x1 * 2 +
        x2 * 4 +
        x3 * 8 +
        x4 * 16 +
        x5 * 32 +
        x6 * 64 +
        x7 * 128
        - x == 0
    }"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-table-vars ((n natp))
  :returns (vars pfcs::name-listp)
  :short "List of all the PFCS variables in a table."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the variables for all the rows,
     from index 0 to index @('n').
     Each row has four variables, for
     program counter, accumulator, opcode, and halted flag,
     for which we use PFCS indexed names.
     We group the variables by columns."))
  (append (pfcs::pfnames "pc" (1+ (nfix n)))
          (pfcs::pfnames "acc" (1+ (nfix n)))
          (pfcs::pfnames "op" (1+ (nfix n)))
          (pfcs::pfnames "hlt" (1+ (nfix n))))

  ///

  (defret len-of-pfcs-table-vars
    (equal (len vars)
           (* 4 (1+ (nfix n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-row-expr-vars ((i natp))
  :returns (exprs pfcs::expression-listp)
  :short "List of the four variables for a row, as expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are determined by the index @('i') of the row."))
  (list (pfcs::pfvar (pfcs::pfname "pc" (nfix i)))
        (pfcs::pfvar (pfcs::pfname "acc" (nfix i)))
        (pfcs::pfvar (pfcs::pfname "op" (nfix i)))
        (pfcs::pfvar (pfcs::pfname "hlt" (nfix i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-all-transitions ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "All transition constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are @('n') transitions, one for each pair of consecutive rows;
     there are @('n+1') rows, indexed 0 to @('n').")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "all_transitions(pc[0], ..., pc[n],"
    "                acc[0], .., acc[n],"
    "                op[0], ..., op[n],"
    "                hlt[0], ..., hlt[n]) := {"
    "    transition(pc[0], acc[0], op[0], hlt[0],"
    "               pc[1], acc[1], op[1], hlt[1]),"
    "    ...,"
    "    transition(pc[n-1], acc[n-1], op[n-1], hlt[n-1],"
    "               pc[n], acc[n], op[n], hlt[n]),"
    "}"))
  (b* ((name (pfcs::pfname "all_transitions"))
       (params (pfcs-table-vars n))
       (constrs (pfcs-all-transitions-loop n)))
    (pfcs::definition name params constrs))

  :prepwork
  ((define pfcs-all-transitions-loop ((n natp))
     :returns (constrs pfcs::constraint-listp)
     :parents nil
     (b* (((when (zp n)) nil)
          (constr (pfcs::constraint-relation (pfcs::pfname "transition")
                                             (append (pfcs-row-expr-vars (1- n))
                                                     (pfcs-row-expr-vars n))))
          (constrs (pfcs-all-transitions-loop (1- n))))
       (append constrs (list constr)))
     :prepwork ((local (in-theory (enable nfix)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-execution ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "Execution constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     the initial row constraint,
     all the transition constraints,
     and the final row constraint.
     That is, it covers the execution from beginning to end.")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "execution(pc[0], ..., pc[n],"
    "          acc[0], .., acc[n],"
    "          op[0], ..., op[n],"
    "          hlt[0], ..., hlt[n]) := {"
    "    initial(pc[0], acc[0], op[0], hlt[0]),"
    "    all_transitions(pc[0], ..., pc[n],"
    "                    acc[0], ..., acc[n],"
    "                    hlt[0], ..., hlt[n])"
    "    final(pc[n], acc[n], op[n], hlt[n])"
    "}"))
  (b* ((name (pfcs::pfname "execution"))
       (params (pfcs-table-vars n))
       (initial-constr (pfcs::constraint-relation (pfcs::pfname "initial")
                                                  (pfcs-row-expr-vars 0)))
       (all-transitions-constr (pfcs::constraint-relation
                                (pfcs::pfname "all_transitions")
                                (pfcs::expression-var-list
                                 (pfcs-table-vars n))))
       (final-constr (pfcs::constraint-relation (pfcs::pfname "final")
                                                (pfcs-row-expr-vars n)))
       (constrs (list initial-constr
                      all-transitions-constr
                      final-constr)))
    (pfcs::definition name params constrs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-path ((path nat-listp))
  :returns (pdef pfcs::definitionp)
  :short "Constraints on the execution path."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of program counters that forms the path
     is determined by a particular input to the program
     (for whose execution the zero-knowledge proof is generated),
     and the constraints apply to all the inputs
     whose execution follows the same path as that particular input.")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "path(pc[0], ..., pc[n]) := {"
    "    pc[0] - <pc[0]> == 0,"
    "    ...,"
    "    pc[n] - <pc[n]> == 0,"
    "}"))
  (b* ((name (pfcs::pfname "path"))
       (params (pfcs::pfnames "pc" (len path)))
       (constrs (pfcs-path-loop path 0)))
    (pfcs::definition name params constrs))

  :prepwork
  ((define pfcs-path-loop ((path nat-listp) (i natp))
     :returns (constrs pfcs::constraint-listp)
     :parents nil
     (b* (((when (endp path)) nil)
          (constr (pfcs::pf= (pfcs::pfvar (pfcs::pfname "pc" i))
                             (pfcs::pfconst (nfix (car path)))))
          (constrs (pfcs-path-loop (cdr path) (1+ (nfix i)))))
       (cons constr constrs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-opcodes ((opcodes program-p))
  :returns (pdef pfcs::definitionp)
  :short "Constraints on the opcodes of the program."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of opcodes passed as input to this ACL2 function
     consists of the opcodes in the execution path of the program.
     The path is determined by a particular input to the program
     (for whose execution the zero-knowledge proof is generated),
     and the constraints apply to all the inputs
     whose execution follows the same path as that particular input.")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "opcodes(op[0], ..., op[n]) := {"
    "    op[0] - <encoding of opcode[0]> == 0,"
    "    ...,"
    "    op[n] - <encoding of opcode[n]> == 0,"
    "}"))
  (b* ((name (pfcs::pfname "opcodes"))
       (params (pfcs::pfnames "op" (len opcodes)))
       (constrs (pfcs-opcodes-loop opcodes 0)))
    (pfcs::definition name params constrs))

  :prepwork
  ((define pfcs-opcodes-loop ((opcodes program-p) (i natp))
     :returns (constrs pfcs::constraint-listp)
     :parents nil
     (b* (((when (endp opcodes)) nil)
          (constr (pfcs::pf= (pfcs::pfvar (pfcs::pfname "op" i))
                             (pfcs::pfconst (opcode-to-field (car opcodes)))))
          (constrs (pfcs-opcodes-loop (cdr opcodes) (1+ (nfix i)))))
       (cons constr constrs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-accumulators ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "Constraints on the accumulator of the trace."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each accumulator must be a byte.
     This does not follow from the transition constraints,
     even if the initial accumulator is a byte.
     It is not yet clear whether this is expressed as AIR constraints,
     in typical systems that use AIR constraints for execution traces,
     or whether this kind of constraint is enforced externally;
     this needs further investigation, but for now, for simplicity,
     we capture these byte constraints are AIR constraints.")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "accumulators(acc[0], ..., acc[n]) := {"
    "    byte(acc[0]),"
    "    ...,"
    "    byte(acc[n])"
    "}"))
  (b* ((name (pfcs::pfname "accumulators"))
       (params (pfcs::pfnames "acc" (1+ (nfix n))))
       (constrs (rev (pfcs-accumulators-loop n))))
    (pfcs::definition name params constrs))

  :prepwork
  ((define pfcs-accumulators-loop ((n natp))
     :returns (constrs pfcs::constraint-listp)
     :parents nil
     (b* ((constr (pfcs::constraint-relation
                   (pfcs::pfname "byte")
                   (list (pfcs::expression-var
                          (pfcs::pfname "acc" (nfix n))))))
          ((when (zp n)) (list constr)))
       (cons constr (pfcs-accumulators-loop (1- n))))
     :prepwork ((local (in-theory (enable nfix)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-table ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "Table constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the constraints for a whole table.
     They consists of the execution constraints,
     and of the opcode constraints.")
   (xdoc::p
    "The PFCS definition has the form")
   (xdoc::codeblock
    "table(pc[0], ..., pc[n],"
    "      acc[0], .., acc[n],"
    "      op[0], ..., op[n],"
    "      hlt[0], ..., hlt[n]) := {"
    "    execution(pc[0], ..., pc[n],"
    "              acc[0], ..., acc[n],"
    "              op[0], ..., op[n],"
    "              hlt[0], ..., hlt[n]),"
    "    path(pc[0], ..., pc[n]),"
    "    opcodes(op[0], ..., op[n]),"
    "    accumulators(acc[0], ..., acc[n])"
    "}"))
  (b* ((name (pfcs::pfname "table"))
       (params (pfcs-table-vars n))
       (execution-constr (pfcs::constraint-relation
                          (pfcs::pfname "execution")
                          (pfcs::expression-var-list
                           (pfcs-table-vars n))))
       (path-constr (pfcs::constraint-relation
                     (pfcs::pfname "path")
                     (pfcs::expression-var-list
                      (pfcs::pfnames "pc" (1+ (nfix n))))))
       (opcodes-constr (pfcs::constraint-relation
                        (pfcs::pfname "opcodes")
                        (pfcs::expression-var-list
                         (pfcs::pfnames "op" (1+ (nfix n))))))
       (accumulators-constr (pfcs::constraint-relation
                             (pfcs::pfname "accumulators")
                             (pfcs::expression-var-list
                              (pfcs::pfnames "acc" (1+ (nfix n))))))
       (constrs (list execution-constr
                      path-constr
                      opcodes-constr
                      accumulators-constr)))
    (pfcs::definition name params constrs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pfcs-computation ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "Input/output computation constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "We join the table constraints
     with two constraints that tie input and output to
     the accumulator in the initial and final states:")
   (xdoc::codeblock
    "computation(input, output) := {"
    "    table(pc[0], ..., pc[n],"
    "          acc[0], .., acc[n],"
    "          op[0], ..., op[n],"
    "          hlt[0], ..., hlt[n]),"
    "    input == acc[0],"
    "    output == acc[n]"
    "}"))
  (b* ((name (pfcs::pfname "computation"))
       (params (list (pfcs::pfname "input")
                     (pfcs::pfname "output")))
       (table-constr (pfcs::constraint-relation
                      (pfcs::pfname "table")
                      (pfcs::expression-var-list (pfcs-table-vars n))))
       (input-constr (pfcs::pf= (pfcs::pfvar (pfcs::pfname "input"))
                                (pfcs::pfvar (pfcs::pfname "acc" 0))))
       (output-constr (pfcs::pf= (pfcs::pfvar (pfcs::pfname "output"))
                                 (pfcs::pfvar (pfcs::pfname "acc" n))))
       (constrs (list table-constr
                      input-constr
                      output-constr)))
    (pfcs::definition name params constrs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compile-to-pfcs ((prog program-p) (input0 ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input0))
  :returns (pdefs pfcs::definition-listp)
  :short "Compile a program and an input to constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result of compilation is a list of PFCS definitions,
     which build on each other.
     The top-level definition is for the @('computation') PFCS relation,
     which characterizes the input/output behavior of
     the programs on all the inputs whose execution
     terminates and hits the same execution path as @('input0').
     The opcodes are the ones on that path,
     and the accumulators are constrained to be bytes
     (see @(tsee pfcs-accumulators) for a discussion of this)."))
  (b* ((n (1+ (min-termination-limit prog input0)))
       (path (execution-path prog input0))
       (opcodes (fetch-list prog path)))
    (list (pfcs-initial)
          (pfcs-final)
          (pfcs-pc-transition)
          (pfcs-acc-transition)
          (pfcs-halted-transition)
          (pfcs-transition)
          (pfcs-all-transitions n)
          (pfcs-execution n)
          (pfcs-path path)
          (pfcs-opcodes opcodes)
          (pfcs-accumulators n)
          (pfcs-table n)
          (pfcs-computation n))))
