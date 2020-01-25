; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial

  :parents (atj)

  :short "ATJ tutorial."

  :long

  (xdoc::topstring

   (xdoc::p
    "This tutorial is work in progress,
     but it may be already useful in its current incomplete form.
     This tutorial's goal is to provide user-level information
     on how ATJ works and how to use ATJ effectively.
     The ATJ reference documentation is "
    (xdoc::seeurl "atj" "here")
    ", along with some additional information
     that will likely be moved to this tutorial.")

   (xdoc::p
    "The subtopics of this manual page
     may be navigated sequentially,
     using the `Start', `Next', and `Previous' links.")

   (xdoc::p
    "Start: "
    (xdoc::seetopic "atj-tutorial-motivation" "Motivation"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-motivation

  :parents (atj-tutorial)

  :short "ATJ tutorial: Motivation."

  :long

  (xdoc::topstring

   (xdoc::p
    "A benefit of writing code in a theorem prover like ACL2
     is the ability to prove properties about it,
     such as the satisfaction of requirements specifications.
     A facility to generate code in one or more programming languages
     from an executable subset of the prover's logical language
     enables the possibly verified code to run as, and interoperate with,
     code written in those programming languages.
     Assuming the correctness of code generation
     (whose verification is a separable problem,
     akin to compilation verification)
     the properties proved about the original code
     carry over to the generated code.")

   (xdoc::p
    "ACL2's tight integration with the underlying Lisp platform
     enables the executable subset of the ACL2 logical language
     to run readily and efficiently as Lisp,
     without the need for explicit code generation facilities.
     Nonetheless, some situations may call for
     running ACL2 code in other programming languages:
     specifically, when the ACL2 code must interoperate
     with external code in those programming languages
     in a more integrated and efficient way than afforded
     by inter-language communication via foreign function interfaces
     such as "
    (xdoc::ahref "https://common-lisp.net/project/cffi" "CFFI")
    " and "
    (xdoc::ahref "https://docs.oracle.com/javase/10/docs/specs/jni" "JNI")
    " or by inter-process communication with the ACL2/Lisp runtime
     via mechanisms like "
    (xdoc::seetopic "acl2::bridge" "the ACL2 Bridge")
    ". Using Lisp implementations
     written in the target programming languages,
     such as "
    (xdoc::ahref "https://abcl.org" "ABCL")
    ", involves not only porting ACL2 to them,
     but also including much more runtime code
     than necessary for the target applications.
     Compilers from Lisp to the target programming languages
     may need changes or wrappers,
     because executable ACL2 is not quite a subset of Lisp;
     furthermore, the ability to compile non-ACL2 Lisp code
     is an unnecessary complication as far as ACL2 compilation is concerned,
     making potential verification harder.")

   (xdoc::p
    "ATJ translates ACL2 to Java,
     enabling possibly verified ACL2 code
     to run as, and interoperate with, Java code,
     without much of the ACL2 framework or any of the Lisp runtime.")

   (xdoc::p
    "ATJ is useful
     to generate Java code at the end of an "
    (xdoc::seetopic "apt::apt" "APT")
    " program synthesis derivation.")

   (xdoc::p
    "Generators for ACL2 of code in other programming languages (than Java)
     may be developed similarly to ATJ.")

   (xdoc::p
    "Next: "
    (xdoc::seetopic "atj-tutorial-background" "Background"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-background

  :parents (atj-tutorial)

  :short "ATJ tutorial: Background."

  :long

  (xdoc::topstring

   (xdoc::p
    "In the context of translating from the ACL2 language
     to Java or any other programming language,
     it is important to consider not only ACL2's logical semantics,
     but also ACL2's evaluation semantics.")

   (xdoc::p
    "ACL2 has a precisely defined "
    (xdoc::ahref "http://www.cs.utexas.edu/users/moore/publications/km97a.pdf"
                 "logical semantics")
    ", expressed in terms of syntax, axioms, and inference rules,
     similarly to logic textbooks and other theorem provers.
     This logical semantics applies to @(see logic)-mode functions,
     not @(see program)-mode functions.
     @(csee guard)s are not part of the logic,
     but engender proof obligations in the logic
     when guard verification is attempted.")

   (xdoc::p
    "ACL2 also has a documented "
    (xdoc::seetopic "acl2::evaluation" "evaluation semantics")
    ", which could be formalized
     in terms of syntax, values, states, steps, errors, etc.,
     as is customary for programming languages.
     This evaluation semantics applies
     to both logic-mode and program-mode functions.
     Guards affect the evaluation semantics,
     based on guard-checking settings.
     Even non-executable functions
     (e.g. introduced via @(tsee defchoose) or @(tsee defun-nx))
     degenerately have an evaluation semantics,
     because they do yield error results when called;
     however, the following discussion focuses on executable functions.")

   (xdoc::p
    "Most logic-mode functions have definitions
     that specify both their logical and their evaluation semantics:
     for the former, the definitions are logically conservative axioms;
     for the latter, the definitions provide ``instructions''
     for evaluating calls of the function.
     For a defined logic-mode function,
     the relationship between the two semantics is that,
     roughly speaking,
     evaluating a call of the function yields, in a finite number of steps,
     the unique result value that, with the argument values,
     satisfies the function's defining axiom;
     the actual relationship is slightly more complicated,
     as it may involve guard checking.")

   (xdoc::p
    "The "
    (xdoc::seetopic "acl2::primitive" "primitive functions")
    " are in logic mode and have no definitions;
     they are all built-in.
     Examples are
     @(tsee equal), @(tsee if), @(tsee cons), @(tsee car), and @(tsee binary-+).
     Their logical semantics is specified by axioms of the ACL2 logic.
     Their evaluation semantics is specified by raw Lisp code
     (under the hood).
     The relationship between the two semantics is as in the above paragraph,
     with the slight complication that
     @(tsee pkg-witness) and @(tsee pkg-imports)
     yield error results when called on unknown package names.
     The evaluation of calls of @(tsee if) is non-strict, as is customary.")

   (xdoc::p
    "Most program-mode functions have definitions
     that specify their evaluation semantics,
     similarly to the non-primitive logic-mode functions discussed above.
     Their definitions specify no logical semantics.")

   (xdoc::p
    "The logic-mode functions
     listed in the global variable @('logic-fns-with-raw-code')
     have a logical semantics specified by their ACL2 definitions,
     but an evaluation semantics specified by raw Lisp code.
     (They are disjoint from the primitive functions,
     which have no definitions.)
     For some of these functions, e.g. @(tsee len),
     the raw Lisp code just makes them run faster
     but is otherwise functionally equivalent to the ACL2 definitions.
     Others have side effects,
     carried out by their raw Lisp code
     but not reflected in their ACL2 definitions.
     For example, @(tsee hard-error) prints a message on the screen
     and immediately terminates execution, unwinding the call stack.
     As another example, @(tsee fmt-to-comment-window)
     prints a message on the screen,
     returning @('nil') and continuing execution.
     But the ACL2 definitions of both of these example functions
    just return @('nil').")

   (xdoc::p
    "The program-mode functions
     listed in the global variable @('program-fns-with-raw-code')
     have an evaluation semantics specified by raw Lisp code.
     Their ACL2 definitions appear to have no actual use.")

   (xdoc::p
    "Since "
    (xdoc::seetopic "acl2::stobj" "stobjs")
    " are destructively updated,
     functions that manipulate stobjs may have side effects as well,
     namely the destructive updates.
     Because of single-threadedness,
     these side effects are invisible
     in the end-to-end input/output evaluation of these functions;
     however, they may be visible
     in some formulations of the evaluation semantics,
     such as ones that comprehend interrupts,
     for which updating a record field in place involves different steps
     than constructing a new record value with a changed field.
     The built-in @(tsee state) stobj
     is ``linked'' to external entities,
     e.g.\ the file system of the underlying machine.
     Thus, functions that manipulate @(tsee state)
     may have side effects on these external entities.
     For example, @(tsee princ$) (a member of @('logic-fns-with-raw-code'))
     writes to the stream associated with the output channel argument,
     and affects the file system.")

   (xdoc::p
    "The fact that the side effects of the evaluation semantics
     are not reflected in the logical semantics
     is a design choice
     that makes the language more practical for programming
     while retaining the ability to prove theorems.
     But when generating Java or other code,
     these side effects should be taken into consideration:
     for instance,
     translating @(tsee hard-error) and @(tsee fmt-to-comment-window)
     into Java code that returns (a representation of) @('nil'),
     would be incorrect or at least undesired.
     As an aside,
     a similar issue applies to the use of "
    (xdoc::seetopic "apt::apt" "APT transformations")
    ": for instance,
     using the "
    (xdoc::ahref "https://arxiv.org/abs/1705.01228v1" "@('simplify')")
    " transformation
     to turn calls of @(tsee hard-error) into @('nil'),
     while logically correct and within @('simplify')'s stipulations,
     may be undesired or unexpected.")

   (xdoc::p
    "Previous: "
    (xdoc::seetopic "atj-tutorial-motivation" "Motivation"))))
