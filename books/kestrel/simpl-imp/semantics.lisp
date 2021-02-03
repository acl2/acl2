; Simple Programming Language Imp Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Teruhiro Tagomori (NRI SecureTechnologies, Ltd.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; cert_param: (non-acl2r)

(in-package "SIMPL-IMP")

(include-book "abstract-syntax")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/fty/defomap" :dir :system)
(include-book "std/util/define-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (imp-language)
  :short "Semantics of Imp."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since Imp is so simple,
     there is no need to explicitly define a static semantics,
     i.e. constraints for the well-formedness and type correctness
     of Imp programs.
     The separation between the @(tsee aexp) and @(tsee bexp) fixtypes
     provides an implicit typing of all the Imp expressions.
     Therefore, in the context of Imp,
     `semantics' always refer to dynamic (i.e. execution) semantics.")
   (xdoc::p
    "We formalize the variable store as an environment,
     i.e. a finite map from (names of) variables to (integer values).
     Imp commands operate on the environment.")
   (xdoc::p
    "We formalize the computation state as a configuration,
     i.e. a pair consisting of a sequence of zero or more commands
     and an environment.
     The commands are the next ones to be executed, in order.")
   (xdoc::p
    "We formalize expression evaluation via ACL2 functions
     from expressions and environments to values.
     This is possible because
     the evaluation of Imp expressions always terminates.
     We use this modeling approach because it is simple
     and we are currently not interested in
     intermediate computation states during the evaluation of expressions,
     but just in the final result of expression evaluation.
     If we were interested in those intermediate computation states,
     we would have to formalize expression evaluation as a multi-step process,
     similarly to the execution of commands (as explained just below).")
   (xdoc::p
    "We formalize an operational semantics via an ACL2 function
     that maps old configurations to new configurations.
     This function performs one step of computation,
     according to a reasonable level of granularity,
     but it is possible to define finer- or coarser-grained steps;
     for instance,
     if expression evaluation were a multi-step process as mentioned above,
     then we would have a finer-grained execution model.
     We cannot have an always-terminating interpreter of Imp commands,
     because its loops may not terminate.
     Thus, having the step function, each of whose steps always terminates,
     lets us talk about sequences of steps that may or may not terminate.
     The step function captures a small-step operational semantics;
     its sequentialization captures a big-step operational semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap env
  :short "Fixtype of Imp environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "While it may be mathematically more convenient
     to define environments as total functions over all variables,
     in ACL2's first-order logic we need to use finite functions,
     which are captured by omaps.
     We use an omap
     from strings (i.e. variable names)
     to integers (i.e. variable values).")
   (xdoc::p
    "In effect, our semantics will regard all variables to be defined,
     with a default value even if they are not explicitly in the finite map."))
  :key-type string
  :val-type int
  :pred envp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-var ((var stringp) (env envp))
  :returns (val integerp)
  :short "Read a variable's value from the environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is convenient to regard every possible variable
     to be explicitly or implicitly present in the environment,
     by regarding the value associated to a variable not explicitly present
     as 0, as if the variable were explicitly present and had value 0.
     This way, this reading function is total:
     it always yields an integer value for each variable and environment."))
  (b* ((var-val (omap::in (str-fix var) (env-fix env))))
    (if (null var-val)
        0
      (cdr var-val)))
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var ((var stringp) (val integerp) (env envp))
  :returns (new-env envp)
  :short "Write a variable's value to the environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add/overwrite a/the pair for the variable in the omap.
     We do this even if the value is 0;
     in this case, we could instead just remove the pair,
     since @(tsee read-var) treats an absent variable
     the same way as one with value 0.
     But we prefer to always add/overwrite the pair,
     avoiding any ``normalization'' of the environment
     (i.e. avoiding insisting that no variable in the environment has value 0).
     Treating an absent variable as one with value 0
     is a mere convenience for having a total @(tsee read-var)."))
  (omap::update (str-fix var) (ifix val) (env-fix env))
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod config
  :short "Fixtype of Imp configuration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A configuration consists of a command list and an environment.
     When the command list is empty,
     there is nothing left to do, i.e. execution has terminated."))
  ((comms comm-list)
   (env env))
  :layout :list
  :tag :config
  :pred configp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aeval ((exp aexpp) (env envp))
  :returns (int integerp)
  :short "Semantics of Imp arithmetic expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is formalized via an evaluation function that maps
     an arithmetic expression and an envionment to an integer.
     The integer is the value of the expression given the environment.")
   (xdoc::p
    "The (recursive) evaluation of Imp's arithmetic expressions
     always terminates.")
   (xdoc::p
    "This evaluation function is executable."))
  (aexp-case exp
             :const exp.value
             :var (read-var exp.name env)
             :add (+ (aeval exp.left env) (aeval exp.right env))
             :mul (* (aeval exp.left env) (aeval exp.right env)))
  :measure (aexp-count exp)
  :verify-guards :after-returns
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define beval ((exp bexpp) (env envp))
  :returns (bool booleanp)
  :short "Semantics of Imp boolean expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is formalized via an evaluation function that maps
     a boolean expression and an environment to a boolean.
     The boolean is the value of the expression given the environment.")
   (xdoc::p
    "Since boolean expressions may contain arithmetic expressions,
     the evaluation of boolean expressions
     involves the evaluation of arithmetic expressions.")
   (xdoc::p
    "The (recursive) evaluation of Imp's boolean expressions
     always terminates.")
   (xdoc::p
    "This evaluation function is executable."))
  (bexp-case exp
             :const exp.value
             :equal (equal (aeval exp.left env) (aeval exp.right env))
             :less (< (aeval exp.left env) (aeval exp.right env))
             :not (not (beval exp.arg env))
             :and (and (beval exp.left env) (beval exp.right env)))
  :measure (bexp-count exp)
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((cfg configp))
  :guard (consp (config->comms cfg))
  :returns (new-cfg configp)
  :short "Semantics of Imp commands."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the guard, this is defined
     only if there are commands in the configuration,
     i.e. there is something to do.
     Otherwise, execution is in a terminated state.")
   (xdoc::p
    "A step consists in
     taking the first command in the configuration
     and executing it.
     This may modify the environment,
     and the list of the commands in the configuration.")
   (xdoc::p
    "An assignment is executed by evaluating the expression
     and writing the obtained value into the variable.
     The assignment command is removed from the configuration,
     because it is completely executed.")
   (xdoc::p
    "A conditional is executed by evaluating the condition first.
     Based on the obtained value,
     the conditional is replaced by one of its branches.
     This means that conditionals are non-strict in Imp:
     the other branch is eliminated, not executed.")
   (xdoc::p
    "A loop is executed by evaluating the condition first.
     If it is false, the loop command is removed from the configuration:
     the loop is completely executed in this case.
     If the condition is true instead,
     the loop body is added in front of the command list in the configuration,
     without removing the loop command itself:
     since the loop condition is true,
     we need to execute the body at least one more time,
     and then we need to execute the loop as a whole again,
     i.e. re-evaluate the condition (generally in a different environment).")
   (xdoc::p
    "This step function is executable."))
  (b* ((comms (config->comms cfg))
       (env (config->env cfg))
       ((unless (mbt (consp comms))) (config-fix cfg))
       (comm (car comms)))
    (comm-case comm
               :asg (b* ((var comm.var)
                         (val (aeval comm.exp env))
                         (new-env (write-var var val env))
                         (new-comms (cdr comms)))
                      (make-config :comms new-comms :env new-env))
               :if (b* ((cond (beval comm.cond env))
                        (new-comms (append (if cond comm.then comm.else)
                                           (cdr comms))))
                     (make-config :comms new-comms :env env))
               :while (b* ((cond (beval comm.cond env))
                           (new-comms (if cond
                                          (append comm.body comms)
                                        (cdr comms))))
                        (make-config :comms new-comms :env env))))
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepn ((cfg configp) (n natp))
  :returns (new-config configp)
  :short "Bounded repetition of Imp steps."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function repeats the step function at most @('n') times.
     It stops when either @('n') is 0 or the configuration has no commands.")
   (xdoc::p
    "This bounded-repetition-step function is executable."))
  (b* (((when (zp n)) (config-fix cfg))
       ((unless (consp (config->comms cfg))) (config-fix cfg)))
    (stepn (step cfg) (1- n)))
  :measure (nfix n)
  :hooks (:fix)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk terminatingp ((cfg configp))
  :returns (yes/no booleanp)
  :short "Check if a configuration is terminating."
  :long
  (xdoc::topstring
   (xdoc::p
    "If we try to exhaustively apply the step function
     to an initial configuration,
     either we will reach a final configuration with no commands,
     or we will keep stepping forever.
     This function recognizes which situation we are in:
     it is a property of the initial configuration.")
   (xdoc::p
    "This function is not executable.
     It uses an (unbounded) existential quantifier.
     The configuration is terminating if there is a number of steps
     after which the final configuration has no commands."))
  (exists (n)
          (and (natp n)
               (not (consp (config->comms (stepn cfg n))))))
  ///

  (fty::deffixequiv-sk terminatingp
    :args ((cfg configp)))

  (defrule natp-of-terminatingp-witness
    (implies (terminatingp cfg)
             (natp (terminatingp-witness cfg)))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum outcome
  :short "Fixtype of outcomes of exhaustive stepping."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee terminatingp),
     attempting to exhaustively stepping from a configuration
     may terminate or not.
     The values of this fixtype capture these two possible outcomes.
     In case of termination, the outcome includes the final environment;
     note that, by definition, the final configuration has no commands,
     so only its environment component is relevant."))
  (:terminated ((env env)))
  (:nonterminating ())
  :pred outcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step* ((cfg configp))
  :returns (outcome outcomep)
  :short "Exhaustively step from a configuration."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the configuration is terminating,
     we take the witness number of @(tsee terminatingp),
     execute that number of steps,
     and return the resulting environment.
     Otherwise, we return the outcome that indicates nontermination.")
   (xdoc::p
    "This, essentially, formalizes a big-step operational semantics.")
   (xdoc::p
    "This function is not executable,
     because it calls the non-executable function @(tsee terminatingp)."))
  (if (terminatingp cfg)
      (b* ((n (terminatingp-witness (config-fix cfg)))
           (final-cfg (stepn cfg n))
           (final-env (config->env final-cfg)))
        (outcome-terminated final-env))
    (outcome-nonterminating))
  :hooks (:fix)
  :no-function t)
