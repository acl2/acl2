; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

; (depends-on "images/values.png")
; (depends-on "images/value-classes.png")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::add-resource-directory "kestrel-java-atj-images" "images")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Subtitle of each tutorial page (except the top one).

(defconst *atj-tutorial-motivation*
  "Motivation for Generating Java Code from ACL2")

(defconst *atj-tutorial-background*
  "Background on the Evaluation Semantics of ACL2")

(defconst *atj-tutorial-aij*
  "Relationship with AIJ")

(defconst *atj-tutorial-acl2-values*
  "Java Representation of the ACL2 Values")

(defconst *atj-tutorial-deep-shallow*
  "Deep and Shallow Embedding Approaches")

(defconst *atj-tutorial-deep*
  "Deep Embedding Approach")

(defconst *atj-tutorial-uml*
  "About the Simplified UML Class Diagrams")

(defconst *atj-tutorial-acl2-terms*
  "Java Representation of the ACL2 Terms")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create the :SHORT string for a tutorial page with the given subtitle.

(define atj-tutorial-short ((subtitle stringp))
  :returns (short stringp :hyp :guard)
  (xdoc::topstring "ATJ Tutorial: " subtitle "."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create the 'start' link for a tutorial page,
; with the given topic and and subtitle.

(define atj-tutorial-start ((topic stringp) (subtitle stringp))
  :returns (start xdoc::treep :hyp :guard)
  (xdoc::p "<b>Start:</b> " (xdoc::seetopic topic subtitle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create the 'previous' link for a tutorial page,
; with the given topic and and subtitle.

(define atj-tutorial-previous ((topic stringp) (subtitle stringp))
  :returns (start xdoc::treep :hyp :guard)
  (xdoc::p "<b>Previous:</b> " (xdoc::seetopic topic subtitle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create the 'next' link for a tutorial page,
; with the given topic and and subtitle.

(define atj-tutorial-next ((topic stringp) (subtitle stringp))
  :returns (start xdoc::treep :hyp :guard)
  (xdoc::p "<b>Next:</b> " (xdoc::seetopic topic subtitle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-tutorial

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
    (xdoc::seetopic "atj" "here")
    ", along with some additional information
     that will likely be moved to this tutorial.")

   (xdoc::p
    "The main subtopics of this manual page
     may be navigated sequentially,
     using the `Start', `Next', and `Previous' links.
     The auxiliary subtopics of this manual page
     are referenced from other subtopics when needed.")

   (xdoc::p
    (xdoc::a :href "https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22018.1"
      "This ACL2-2018 Workshop paper")
    " provides an overview of ATJ,
     but ATJ has been significantly extended since then.
     Some of the contents of the paper are being copied to this tutorial,
     and updated as appropriate;
     it is possible that the paper will be completely subsumed by this tutorial
     once the latter is completed.")

   (atj-tutorial-start "atj-tutorial-motivation" *atj-tutorial-motivation*))

  :order-subtopics t

  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main pages of the ATJ turorial, which can be navigated sequentially.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-motivation

  :short (atj-tutorial-short *atj-tutorial-motivation*)

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

   (atj-tutorial-next "atj-tutorial-background" *atj-tutorial-background*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-background

  :short (atj-tutorial-short *atj-tutorial-background*)

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
     e.g. the file system of the underlying machine.
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
    "Macros are normally expanded
     (the expansion being also according to ACL2's evaluation semantics),
     and their expansion is then evaluated.
     However, the macros listed in the global variable @('macros-with-raw-code')
     have an evaluation semantics specified by raw Lisp code.
     The evaluation semantics specified by their raw Lisp code
     may be consistent with the evaluation semantics of their expansion or not,
     due to side effects or apparent circularities.
     For instance, the @(tsee concatenate) macro has raw Lisp code,
     which obviously terminates execution;
     however, the expansion of @(tsee concatenate) calls @(tsee string-append),
     whose @(':exec') part calls @(tsee concatenate),
     and therefore execution may not terminate.
     Thus, macros with raw Lisp code may also need to be taken into account
     when translating ACL2 code to Java or other programming languages.")

   (atj-tutorial-previous "atj-tutorial-motivation" *atj-tutorial-motivation*)

   (atj-tutorial-next "atj-tutorial-aij" *atj-tutorial-aij*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-aij

  :short (atj-tutorial-short *atj-tutorial-aij*)

  :long

  (xdoc::topstring

   (xdoc::p
    (xdoc::seetopic "aij" "AIJ")
    " is related to, but independent from, ATJ.
     ATJ generates Java code that needs at least part of AIJ to run:
     in this sense, ATJ depends on AIJ.
     Although the development of AIJ has been motivated by ATJ,
     AIJ does not need or depend on ATJ:
     it can be used independently.
     However, AIJ's main use is as support for ATJ.")

   (xdoc::p
    "See "
    (xdoc::seetopic "aij" "the AIJ manual page")
    " for information about AIJ as a stand-alone entity,
     independent from ATJ.
     However, this ATJ tutorial will describe many aspects of AIJ
     that are necessary or useful to understand and use ATJ.")

   (atj-tutorial-previous "atj-tutorial-background" *atj-tutorial-background*)

   (atj-tutorial-next "atj-tutorial-acl2-values" *atj-tutorial-acl2-values*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-acl2-values

  :short (atj-tutorial-short *atj-tutorial-acl2-values*)

  :long

  (xdoc::topstring

   (xdoc::p
    "In order to translate from ACL2 to Java,
     there must be a Java representation of the ACL2 values. "
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " provides a default representation,
     described in this tutorial page.
     More advanced representations are discussed later.")

   (xdoc::p
    "The set of values of the ACL2 evaluation semantics
     is the union of the sets depicted below:
     (i) integers, recognized by @(tsee integerp);
     (ii) ratios, i.e. rationals that are not integers,
     with no built-in recognizer
     (the term `ratio' is used in "
    (xdoc::ahref
     "https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node18.html"
     "Section 2.1.2 of the Common Lisp specification")
    ");
     (iii) complex rationals, recognized by @(tsee complex-rationalp);
     (iv) characters, recognized by @(tsee characterp);
     (v) strings, recognized by @(tsee stringp);
     (vi) symbols, recognized by @(tsee symbolp); and
     (vii) @(tsee cons) pairs, recognized by @(tsee consp).
     Integers and ratios form the rationals, recognized by @(tsee rationalp).
     Rationals and complex rationals form the Gaussian rationals,
     which are all the numbers in ACL2,
     recognized by @(tsee acl2-numberp)
     (this discussion does not apply to "
    (xdoc::seetopic "acl2::real" "ACL2(r)")
    ").
     The logical semantics of ACL2 allows additional values called `bad atoms',
     and consequently @(tsee cons) pairs
     that may contain them directly or indirectly;
     however, such values cannot be constructed in evaluation.")

   (xdoc::img :src "res/kestrel-java-atj-images/values.png")

   (xdoc::p
    "AIJ represents ACL2 values
     as immutable objects of class @('Acl2Value') and its subclasses
     in the "
    (xdoc::seetopic "atj-tutorial-simplified-uml"
                    "simplified UML class diagram")
    " below.
     Each class in the diagram, except @('Acl2PackageName'),
     corresponds to a set
     in the picture of ACL2 values above.
     The subset relationships in that picture
     match the inheritance relationships in the UML diagram above.
     The sets of values that are unions of other sets of values
     correspond to abstract classes;
     the other sets correspond to concrete classes.
     All these classes are public,
     except for the package-private ones for ratios and complex rationals:
     ratios and complex rationals are built indirectly via AIJ's API,
     by building
     rationals that are not integers and numbers that are not rationals.")

   (xdoc::img :src "res/kestrel-java-atj-images/value-classes.png")

   (xdoc::p
    "The information about the represented ACL2 values
     is stored in fields of the non-abstract classes.
     @('Acl2Integer') stores
     the numeric value as a @('java.math.BigInteger').
     @('Acl2Ratio') stores
     the numerator and denominator as @('Acl2Integer')s,
     in reduced form
     (i.e. their greatest common divisor is 1
     and the denominator is greater than 1).
     @('Acl2ComplexRational') stores
     the real and imaginary parts as @('Acl2Rational')s.
     @('Acl2Character') stores
     the 8-bit code of the character as a @('char') below 256.
     @('Acl2String') stores
     the codes and order of the characters as a @('java.lang.String')
     whose @('char')s are all below 256.
     @('Acl2Symbol') stores
     the symbol's package name as a @('Acl2PackageName')
     (a wrapper of @('java.lang.String')
     that enforces the ACL2 constraints on package names)
     and the symbol's name as a @('Acl2String').
     @('Acl2ConsPair') stores the component @('Acl2Value')s.
     All these fields are private,
     thus encapsulating the internal representation choices
     and enabling their localized modification.
     ACL2 numbers, strings, and symbols have no preset limits,
     but the underlying Lisp runtime may run out of memory.
     Their Java representations (e.g. @('java.math.BigInteger'))
     have very large limits,
     whose exceedance could be regarded as running out of memory.
     If needed, the Java representations could be changed
     to overcome the current limits
     (e.g. by using lists of @('java.math.BigInteger')s).")

   (xdoc::p
    "The public classes for ACL2 values and package names
     in the UML diagram above
     provide public static factory methods to build objects of these classes.
     For example, @('Acl2Character.make(char)')
     returns a @('Acl2Character') with the supplied argument as code,
     throwing an exception if the argument is above 255.
     As another example, @('Acl2ConsPair.make(Acl2Value,Acl2Value)')
     returns a @('Acl2ConsPair') with the supplied arguments as components.
     Some classes provide overloaded variants,
     e.g. @('Acl2Integer.make(int)')
     and @('Acl2Integer.make(java.math.BigInteger)').
     All these classes provide no public Java constructors,
     thus encapsulating the details of object creation and re-use,
     which is essentially transparent to external code
     because these objects are immutable.")

   (xdoc::p
    "The public classes for ACL2 values in the UML diagram above
     provide public instance getter methods
     to unbuild (i.e. extract information from) instances of these classes.
     For example, @('Acl2Character.getJavaChar()')
     returns the code of the character
     as a @('char') that is always below 256.
     As another example,
     @('Acl2ConsPair.getCar()') and @('Acl2ConsPair.getCdr()')
     return the component @('Acl2Value')s of the \acl{cons') pair.
     Some classes provide variants,
     e.g. @('Acl2Integer.getJavaInt()')
     (which throws an exception if the integer does not fit in an @('int'))
     and @('Acl2Integer.getJavaBigInteger()').")

   (xdoc::p
    "Thus, AIJ provides a public API to
     build and unbuild Java representations of ACL2 values:
     the API consists of the factory and getter methods described above.
     When talking about AIJ,
     this tutorial calls `build' and `unbuild'
     what is often called `construct' and `destruct' in functional programming,
     because in object-oriented programming the latter terms
     may imply object allocation and deallocation,
     which is not necessarily what the AIJ API does.")

   (xdoc::p
    "For more details on AIJ's implementation and API of ACL2 values,
     see the Javadoc in AIJ's Java code.")

   (atj-tutorial-previous "atj-tutorial-aij" *atj-tutorial-aij*)

   (atj-tutorial-next "atj-tutorial-deep-shallow" *atj-tutorial-deep-shallow*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-deep-shallow

  :short (atj-tutorial-short *atj-tutorial-deep-shallow*)

  :long

  (xdoc::topstring

   (xdoc::p
    "Translating ACL2 to Java involves
     not only "
    (xdoc::seetopic "atj-tutorial-acl2-values"
                    "representing the ACL2 values in Java")
    " but also representing the ACL2 language constructs
     (function definitions, conditionals, etc.)
     in Java in some way so that they can be executed in Java.
     There are generally two approaches
     to representing a language in another language:
     deep embedding and shallow embedding.
     ATJ supports both.")

   (xdoc::p
    "In the deep embedding approach,
     both the syntax and (evaluation) semantics of ACL2
     are represented explicitly in Java.
     There are Java data structures
     that correspond to the ACL2 language constructs,
     and there is Java code that executes these constructs
     consistently with ACL2's semantics.
     In other words,
     there is an interpreter of the ACL2 language
     written in the Java language.")

   (xdoc::p
    "In the shallow embedding approach,
     there is no such explicit representation
     of ACL2's syntax and (evaluation) semantics in Java.
     Instead, the ACL2 constructs are mapped to Java constructs
     in a way that Java's semantics corresponds to ACL2's semantics.")

   (xdoc::p
    "Compilers and code generators
     normally follow the shallow embedding approach.
     ATJ's initial version supported the deep embedding approach,
     because of its simplicity and assurance.
     ATJ's later versions added the shallow embedding approach,
     which provides more readable and performant Java code.
     The shallow embedding is the preferred approach,
     but support for the deep embedding has been retained
     and there are no plans to remove it.")

   (xdoc::p
    "In the following manual pages,
     first we describe the deep embedding approach,
     because it is simple
     and because some of the concepts also apply
     to the shallow embedding approach.")

   (atj-tutorial-previous "atj-tutorial-acl2-values"
                          *atj-tutorial-acl2-values*)

   (atj-tutorial-next "atj-tutorial-deep" *atj-tutorial-deep*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-deep

  :short (atj-tutorial-short *atj-tutorial-deep*)

  :long

  (xdoc::topstring

   (xdoc::p
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " not only provides "
    (xdoc::seetopic "atj-tutorial-acl2-values"
                    "a default Java representation of the ACL2 values")
    ": it is a "
    (xdoc::seetopic "atj-tutorial-deep-shallow"
                    "deep embedding of ACL2 in Java")
    "; more precisely, a deep embedding of the
     executable, "
    (xdoc::seetopic "atj-tutorial-background" "side-effect")
    "-free,
     non-"
    (xdoc::seetopic "acl2::stobj" "stobj")
    "-accessing
     subset of the ACL2 language without guards.
     AIJ includes a "
    (xdoc::seetopic "atj-tutorial-acl2-terms"
                    "Java representation of the ACL2 terms")
    " (in "
    (xdoc::seetopic "acl2::term" "translated")
    " form)
     and a Java representation of the ACL2 environment,
     consisting of "
    (xdoc::seetopic "defun" "function definitions")
    " and "
    (xdoc::seetopic "defpkg" "package definitions")
    ". AIJ also includes
     a Java implementation of the ACL2 "
    (xdoc::seetopic "acl2::primitive" "primitive functions")
    ", and an ACL2 "
    (xdoc::seetopic "atj-tutorial-background" "evaluator")
    " written in Java.")

   (xdoc::p
    "Besides an "
    (xdoc::seetopic "atj-tutorial-acl2-values"
                    "API to build and unbuild ACL2 values")
    ", AIJ also provides
     an API to build an ACL2 environment
     (i.e. to build ACL2 function and package definitions),
     and an API to evaluate calls of ACL2 primitive and defined functions
     without checking guards.
     External Java code could use this whole API as follows
     (see picture below):")
   (xdoc::ol
    (xdoc::li
     "Build the ACL2 environment:"
     (xdoc::ol
      (xdoc::li
       "Define the ACL2 packages of interest,
        both built-in and user-defined,
        in the order in which they appear in the ACL2 @(see world).")
      (xdoc::li
       "Define the ACL2 functions of interest,
        both built-in and user-defined (except the primitive ones),
        in any order.")))
    (xdoc::li
     "Evaluate ACL2 function calls:"
     (xdoc::ol
      (xdoc::li
       "Build the name of the ACL2 function to call,
        as well as zero or more ACL2 values to pass as arguments,
        via the factory methods of the "
       (xdoc::seetopic "atj-tutorial-acl2-values" "value classes")
       ".")
      (xdoc::li
       "Call the @('Acl2NamedFunction.call(Acl2Value[])') method
        on the function name with the (array of) arguments.")
      (xdoc::li
       "Unbuild the returned @('Acl2Value') as needed to inspect and use it,
        using the getter methods of the "
       (xdoc::seetopic "atj-tutorial-acl2-values" "value classes")
       "."))))

   (xdoc::img :src "res/kestrel-java-atj-images/aij-api.png")

   (xdoc::p
    "ATJ automates the first part of the protocol described above,
     namely the building of the ACL2 environment
     (see picture below).
     ATJ generates Java code
     that uses the AIJ API to build the ACL2 environment
     and that provides a wrapper API
     for external Java code to evaluate ACL2 function calls.
     The external Java code must still directly use the AIJ API
     to build and unbuild ACL2 values
     passed to and received from function calls.")

   (xdoc::img :src "res/kestrel-java-atj-images/atj-aij-api.png")

   (xdoc::p
    "For example, consider the following factorial function:")
   (xdoc::codeblock
    "(defun fact (n)"
    "  (declare (xargs :guard (natp n)))"
    "  (if (zp n)"
    "      1"
    "    (* n (fact (1- n)))))")

   (xdoc::p
    "To generate Java code for that function,
     include ATJ via")
   (xdoc::codeblock
    "(include-book \"kestrel/java/atj/top\" :dir :system)")
   (xdoc::p
    "and call ATJ via")
   (xdoc::codeblock
    "(java::atj fact :deep t :guards nil)")
   (xdoc::p
    "where @(':deep t') specifies the deep embedding approach
     and @(':guards nil') specifies not to assume the guards' satisfaction
     (more on this later).")

   (xdoc::p
    "As conveyed by the message shown on the screen by ATJ,
     a single Java file @('Acl2Code.java') is generated,
     in the current directory.
     Opening the file reveals that it contains
     a single Java public class called @('Acl2Code').
     The file imports all the (public) AIJ classes,
     which are in the @('edu.kestrel.acl2.aij') Java package,
     and a few classes from the Java standard library.")

   (xdoc::p
    "The class starts with a static initializer that calls
     a number of methods to define ACL2 packages
     and a number of methods to define ACL2 functions.
     The packages are all the known ones in the ACL2 @(see world)
     at the time that ATJ is called:
     the method names are derived from the package names,
     as should be apparent.
     The functions are @('fact') and all the ones
     called directly or indirectly by @('fact'),
     except for the "
    (xdoc::seetopic "acl2::primitive" "primitive functions")
    ". In this case, the functions are
     @('fact'), @(tsee zp), and @(tsee not):")
   (xdoc::ul
    (xdoc::li
     "@('fact') calls @(tsee zp), which calls @(tsee not).")
    (xdoc::li
     "@('fact') also calls @(tsee *) and @(tsee 1-),
      but these are macros whose expansions call
      the primitive functions @(tsee binary-*) and @(tsee binary-+).")
    (xdoc::li
     "@(tsee zp) also calls the primitive function @(tsee if),
      and the macro @(tsee <=), whose expansion calls @(tsee not)
      and the primitive function @(tsee <).")
    (xdoc::li
     "@(tsee not) calls the primitive function @(tsee if)."))
   (xdoc::p
    "ATJ looks at the "
    (xdoc::seetopic "acl2::term" "translated")
    " bodies of the functions,
     where macros, and also named constants, are expanded already.")

   (xdoc::p
    "The static initializer is followed by
     the declarations of the (private) methods that it calls.
     The package definition methods
     build the packages' import lists (some quite long)
     and pass them to the AIJ method to define packages;
     the code that builds the import lists is generated by ATJ,
     based on the results of @(tsee pkg-imports) on the known packages.
     The function definition methods
     build the functions' names, formal parameter, and bodies,
     and pass them to the AIJ method to define functions;
     the code that builds formal parameters and bodies is generated by ATJ,
     based on the @('formals') and @('unnormalized-body') properties
     of the function symbols.
     The details of all these methods are unimportant here.")

   (xdoc::p
    "At the end of the class declaration (and file)
     there are two public methods,
     which form the API to the ATJ-generated Java code
     illustrated in the picture above.
     The @('initialize()') method has an empty body,
     but its purpose is to ensure the initialization of the class,
     and therefore the execution of the static initializer,
     which defines all the ACL2 packages and functions of interest.
     The @('call()') method evaluates an ACL2 function call,
     by invoking the relevant AIJ method (the details are unimportant here).")

   (xdoc::p
    "External Java code must call @('initialize()')
     not only before calling @('call()'),
     but also before using AIJ's API to build
     the @('Acl2Symbol') and @('Acl2Value')s
     to pass to @('call()').
     The reason is that the building of @('Acl2Symbol')s
     depends on the definitions of the known packages being in place,
     just as in ACL2.")

   (xdoc::p
    "The following is a simple example of external Java code
     that uses the ATJ-generated and AIJ:")
   (xdoc::codeblock
    "import edu.kestrel.acl2.aij.*;"
    ""
    "public class Test {"
    "    public static void main(String[] args)"
    "        throws Acl2UndefinedPackageException {"
    "        Acl2Code.initialize();"
    "        Acl2Symbol function = Acl2Symbol.make(\"ACL2\", \"FACT\");"
    "        Acl2Value argument = Acl2Integer.make(100);"
    "        Acl2Value[] arguments = new Acl2Value[]{argument};"
    "        Acl2Value result = Acl2Code.call(function, arguments);"
    "        System.out.println(\"Result: \" + result + \".\");"
    "    }"
    "}")
   (xdoc::p
    "This code initializes the ACL2 environment,
     creates the function symbol `@('acl2::fact')',
     creates a singleton array of arguments with the ACL2 integer 100,
     calls the factorial function,
     and prints the resulting value.
     (AIJ's API includes @('toString()') methods
     to convert ACL2 values to Java strings.)
     The @('Acl2UndefinedPackageException') must be declared
     because @('call()') may throw it in general,
     even though it will not in this case.")

   (xdoc::p
    "If the code above is in a file @('Test.java')
     in the same directory where @('Acl2Code.java') was generated,
     it can be compiled via")
   (xdoc::codeblock
    "javac -cp [books]/kestrel/java/aij/java/out/artifacts/AIJ_jar/AIJ.jar \\"
    "      Acl2Code.java Test.java")
   (xdoc::p
    "where @('[books]/...') must be replaced with
     a proper path to the AIJ jar file
     (see the documentation of "
    (xdoc::seetopic "aij" "AIJ")
    "for instructions on how to obtain that jar file.")

   (xdoc::p
    "After compiling, the code can be run via")
   (xdoc::codeblock
    "java -cp [books]/kestrel/java/aij/java/out/artifacts/AIJ_jar/AIJ.jar:. \\"
    "      Test")
   (xdoc::p
    "where again @('[books]/...') must be replaced with a proper path.
     A fairly large number will be printed on the screen.
     Some ACL2 has just been run in Java.")

   (atj-tutorial-previous "atj-tutorial-deep-shallow"
                          *atj-tutorial-deep-shallow*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Auxiliary pages of the ATJ tutorial, which are referenced from the main ones.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-simplified-uml

  :short (atj-tutorial-short *atj-tutorial-uml*)

  :long

  (xdoc::topstring

   (xdoc::p
    "This tutorial uses simplified "
    (xdoc::ahref "http://uml.org" "UML")
    " class diagrams
     to illustrate the "
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " Java classes.")

   (xdoc::p
    "Each class is depicted as a box containing its name.
     Abstract classes have italicized names.
     Public classes have names preceded by @('+'),
     while package-private classes have names preceded by @('~').
     Inheritance (`is a') relationships
     are indicated by lines with hollow triangular tips.
     Composition (`part of') relationships
     are indicated by lines with solid rhomboidal tips,
     annotated with
     the names of the containing class instances' fields
     that store the contained class instances,
     and with the multiplicity of the contained instances
     for each containing instance
     (@('0..*') means `zero or more').")

   (xdoc::p
    "The dashed boxes are just replicas to avoid clutter.
     These UML class diagrams are simplified because
     the class boxes do not contain fields and methods,
     as they should in a full UML class diagram.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-acl2-terms

  :short (atj-tutorial-short *atj-tutorial-acl2-terms*)

  :long

  (xdoc::topstring

   (xdoc::p
    "For the "
    (xdoc::seetopic "atj-tutorial-deep" "deep embedding approach")
    ", "
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " provides a Java representation of the ACL2 terms.
     Since ACL2 terms are also ACL2 values,
     in principle the "
    (xdoc::seetopic "atj-tutorial-acl2-values"
                    "Java representation of the ACL2 values")
    "provided by AIJ could be used to represent the ACL2 terms as well.
     However, it is more convenient to use
     a more specialized representation,
     described in this tutorial page.")

   (xdoc::p
    "The set of ACL2 "
    (xdoc::seetopic "acl2::term" "translated")
    " terms consists of
     (i) variables',
     which are symbols,
     (ii) quoted constants,
     which are lists @('(quote value)') where @('value') is a value,
     and (iii) function applications,
     which are lists @('(fn arg1 ... argn)')
     where @('fn') is a function
     and @('arg1'), ..., @('argn') are zero or more terms.
     A function @('fn') used in a term is
     (i) a named function,
     which is a symbol,
     or (ii) a lambda expression,
     which is a list @('(lambda (var1 ... varm) body)')
     where @('var1'), ..., @('varm') are zero or more symbols
     and @('body') is a term,
     whose free variables are all among @('var1'), ..., @('varm')
     (i.e. lambda expressions are always closed).")

   (xdoc::p
    "AIJ represents ACL2 terms in a manner similar to ACL2 values,
     as objects of class @('Acl2Term') and its subclasses in the "
    (xdoc::seetopic "atj-tutorial-simplified-uml"
                    "simplified UML class diagram")
    " below.
     Functions are represented
     as objects of class @('Acl2Function') and its subclasses
     in the same diagram.
     The classes with subclasses are abstract,
     while classes without subclasses are concrete.
     All these classes are public, except @('Acl2DefinedFunction').
     The information about the represented ACL2 terms (and functions)
     is stored in private fields.")

   (xdoc::img :src "res/kestrel-java-atj-images/term-classes.png")

   (xdoc::p
    "@('Acl2Variable') is a wrapper of @('Acl2Symbol'), and
     @('Acl2QuotedConstant') is a wrapper of @('Acl2Value');
     these wrappers place @('Acl2Symbol') and @('Acl2Value')
     into the class hierarchy of @('Acl2Term'),
     given that Java does not support multiple class inheritance
     (e.g. @('Acl2Symbol') could not be
     both a subclass of @('Acl2Value') and a subclass of @('Acl2Term')).
     An @('Acl2FunctionCall') stores
     an @('Acl2Function') and zero or more @('Acl2Term')s.")

   (xdoc::p
    "An @('Acl2LambdaExpression') stores
     zero or more @('Acl2Variable')s and an @('Acl2Term').
     @('Acl2NamedFunction') is a wrapper of @('Acl2Symbol'),
     placing @('Acl2Symbol') into the class hierarchy of @('Acl2Function').
     AIJ's Java representation of named functions
     differentiates between native and defined functions.
     An @('Acl2DefinedFunction') stores a definition
     consisting of zero or more formal parameters (@('Acl2Symbol')s)
     and of a body (a @('Acl2Term')),
     which are put together into a lambda expression
     (as in a higher-order equality @('(equal fn (lambda ...))')).
     An @('Acl2NativeFunction') represents an ACL2 function
     that is implemented natively via Java code,
     not via (a Java representation of) an ACL2 definiens.
     Here `native' is with respect to ACL2, not Java;
     it has nothing to do with "
    (xdoc::ahref "https://docs.oracle.com/javase/10/docs/specs/jni" "JNI")
    ". There is an instance of @('Acl2NativeFunction')
     for each "
    (xdoc::seetopic "acl2::primitive" "ACL2 primitive function")
    ": these could not be instances of @('Acl2DefinedFunction'),
     because they have "
    (xdoc::seetopic "atj-tutorial-background" "no ACL2 definition")
    ". There are also instances of @('Acl2NativeFunction')
     for other built-in ACL2 functions,
     and more may be added in the future,
     particularly for execution efficiency.")

   (xdoc::p
    "The classes for ACL2 terms (and functions) provide
     public static factory methods to build instances of these classes,
     but no public Java constructors,
     similarly to "
    (xdoc::seetopic "atj-tutorial-acl2-values" "the classes for ACL2 values")
    ". In the "
    (xdoc::seetopic "atj-tutorial-deep" "deep embedding approach")
    ", the Java code generated by ATJ
     uses these factory methods to build the terms in the definientia
     of the ACL2 functions that are being translated to Java.
     Note that since @('Acl2QuotedConstant') wraps @('Acl2Value'),
     the ATJ-generated Java code also uses
     the factory methods of the classes of ACL2 values.")

   (xdoc::p
    "The classes for ACL2 terms (and functions) do not provide
     getter methods to extract information,
     unlike the classes for the ACL2 values.
     The reason is that code external to AIJ
     (including the code generated by ATJ)
     only need to build terms, not unbuild them.
     In contrast, code external to AIJ,
     and to ATJ-generated code,
     may need to unbuild the results obtained by evaluating
     calls of ACL2 functions.")

   (xdoc::p
    "For more details on AIJ's implementation and API of ACL2 terms,
     see the Javadoc in AIJ's Java code.")))
