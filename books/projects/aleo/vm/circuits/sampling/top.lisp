; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "prime-field-macros")
(include-book "equiv")

; These next two are essentially the same, generating the same list structure.
; The first has some code that can be reused.  We can remove it later.
; The second uses the defaggregate's constructor and predicates for return
; type.
;(include-book "gadget-json-to-r1cs-list")
(include-book "gadget-json-to-r1cs-defagg")

; The JSON output from SnarkVM is now going to messages,
; so we need a different parser.  (Btw, this uses parts of "gadget-json-to-r1cs-defagg")
(include-book "gadget-json-message-to-r1cs-defagg")

; v3:
; The JSON output from snarkVM is now run from a shell
; into a raw file, which avoids IntelliJ's processing
; of the output as was done in v2.
(include-book "cargo-test-output")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Links
;; -----

;; Documentation for Aleo instructions:
;;   https://developer.aleo.org/aleo/opcodes

;; circuit source files in Rust are under
;;   snarkvm/circuit/types/

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; NOTE, this directory needs to be reorganized.
; The "Organization" section here is out of date.

;; Organization
;; ------------

;; Operations are in the same order as found in the alphabetized Rust
;; source files.

;; For each operation <typename-opname>, we have four main sections,
;; with a total of 9 definitions/theorems.

;; 1) Operation specification, a functional specification of the operation,
;;    with these components:
;;    * Predicate stating the precondition on the input variables.
;;      <typename-opname>--pre
;;    * Predicate stating the postcondition that the output variables
;;      must satisfy.
;;      <typename-opname>--post
;;    * Main functional specification for the operation.
;;      <typename-opname>--fun

;; 2) Circuit specification, a relational predicate specification of what
;;    the R1CS should do, in terms of the operation specification,
;;    with these components:
;;    * Predicate stating the restrictions on the input and output variables
;;      needed to use the circuit specification.  The input variables
;;      are restricted to xxx-pre but the output variables are only restricted
;;      to be field elements---the postcondition is actually verified in a
;;      theorem later.
;;      <typename-opname>--hyps
;;    * Main relational specification for the operation.
;;      <typename-opname>--spec

;; 3) Circuit implementation, extracted from the Rust code as R1CS (or with
;;    a stand-in until we can get the R1CS):
;;      <typename-opname>--circuit

;; 4) Theorems verifying the circuit:
;;    * Main theorem, checking the equivalence of the circuit specification
;;      and implementation.
;;      The simplest form of this includes both soundness and completeness
;;      in one theorem; more discussion in the next section.
;;      <typename-opname>--equiv
;;    * Postcondition correctness of circuit specification.
;;      <typename-opname>--spec-post
;;    * Postcondition correctness of circuit implementation.
;;      <typename-opname>--circuit-post

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Discussion on functional and relational equivalence.

;; Aleo instruction operations are deterministic functions: for a given input
;; there is only one possible output.  However, an R1CS is a set of equations
;; (constraints) over the input and output and internal (witness) variables,
;; which in general defines a relation.
;;
;; The goals for formally verifying that an Aleo instruction operation is
;; correctly represented in R1CS are:
;;
;;   * Weak Completeness. This is part of completeness, as we define it,
;;     but we mention this separately since it is something that can be checked
;;     independently and there are R1CS static analyzers that do that.
;;     Weak completeness shows that every legal input to the operation is in the
;;     R1CS relation.  In other words, for every legal input, show that there
;;     exist values for the witness and output variables that make
;;     the R1CS equations evaluate correctly.
;;
;;   * Completeness. Show that every legal INPUT/OUTPUT pair of the operation
;;     is in the operation's R1CS relation.  I.e., replace the INPUT and OUTPUT
;;     variables in the operation's R1CS by their values from the function
;;     and make sure the R1CS equations evaluate correctly.
;;     Note that we don't actually iterate over all possible input values
;;     since that is impractical for large inputs.  We use theorem proving to
;;     symbolically cover over all the inputs.
;;
;;   * Soundness.  Show that there is no solution to the R1CS that
;;     associates an incorrect output with a legal input.
;;     In other words, for all solutions (INPUT,OUTPUT,witness) to the R1CS,
;;     make sure that op(INPUT) = OUTPUT.

;; In ACL2, we state completeness and soundness as follows.

;; Because of how the circuit spec relation is defined as the I/O pairs
;; of the circuit spec function, relational equivalence of the circuit spec
;; to the circuit implementation is the same as functional equivalence of
;; the circuit function to the Aleo instruction operation function.

;; Completeness of a circuit means every I/O pair of the function is
;; a valid solution to the circuit's constraint system.  For a binary operation
;; of a and b returning c we write that in terms of the above as follows:
;;   (defrule xxx--completeness
;;      (implies (and (xxx--hyps a b c)
;;                    (xxx--spec a b c))
;;               (xxx--circuit a b c)))

;; Soundness of a circuit means every solution of the circuit's constraint system
;; is a valid I/O pair of the functional specification.  For a binary operation
;; of a and b returning c we can write that as follows:
;;   (defrule xxx--soundness
;;      (implies (and (xxx--hyps a b c)
;;                    (xxx--circuit a b c))
;;               (xxx--spec a b c)))

;; Completeness and soundness can be combined into a single theorem
;; stating equivalence.  For a binary operation of a and b
;; returning c we write that as follows:
;;   (defrule xxx--equiv
;;      (implies (xxx--hyps a b c)
;;               (iff (xxx--circuit a b c)
;;                    (xxx--spec a b c))))

;; Note that the xxx--circuit predicates above operate on the same variables as
;; the xxx--spec predicates.

;; If the circuit has no additional auxiliary internal variables, the xxx--circuit
;; predicate is defined as simply the conjunction of all its R1CS constraints,
;; assuming that x1,...,xn are the input variables and that y1,...,ym are the
;; output variables:
;;   (defun xxx--circuit (x1 ... xn y1 ... ym)
;;     (and <constraint1> <constraint2> ...))

;; If instead the circuit has additional auxiliary internal variables, the
;; xxx--circuit predicate is defined as an existential quantification over a
;; predicate that includes those variables and that is defined as the
;; conjunction of the constraints, where a1,...,aq are the auxialiary variables,
;; where p is the prime, and where (fep a p) says that a is in the prime field
;; defined by p:
;;   (defun xxx--circuit-aux (x1 ... xn y1 ... ym a1 ... aq)
;;     (and <constraint1> <constraint2> ...))
;;   (defun-sk xxx--circuit (x1 ... xn y1 ... ym)
;;     (exists (a1 ... ap)
;;       (and (fep a1 p) ... (fep aq p)
;;            (xxx-circuit x1 ... xn y1 ... ym a1 ... aq))))

;; The above descriptions can become more complicated for various reasons.
;; Some possible reasons include
;;  - data conversions needed between the specification and circuit
;;  - restrictions on witness variables, especially those that cannot
;;    be expressed as a precondition on the input variables
;; Additional descriptions will be added later.
