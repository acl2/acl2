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

(defconst *atj-tutorial-customization*
  "Customization Options for Generated Code")

(defconst *atj-tutorial-uml*
  "About the Simplified UML Class Diagrams")

(defconst *atj-tutorial-acl2-terms*
  "Java Representation of the ACL2 Terms")

(defconst *atj-tutorial-acl2-environment*
  "Java Representation of the ACL2 Environment")

(defconst *atj-tutorial-native*
  "Native Java Implementations of ACL2 Functions")

(defconst *atj-tutorial-evaluator*
  "ACL2 Evaluator Written in Java")

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
    "This tutorial consists of this top-level page,
     a set of <i>main</i> pages,
     and a set of <i>auxiliary</i> pages.
     Both main and auxiliary pages are subtopics of this top-level page.
     The main pages may be navigated sequentially,
     using the `Start', `Next', and `Previous' links;
     these pages should contain all the user-level information
     that is necessary to use ATJ effecively.
     The auxiliary pages are referenced from the main pages as needed;
     they contain additional information
     that may not be strictly necessary to ATJ users,
     such as implementation details;
     however, this information may be useful,
     and thus users are encouraged to read the auxiliary pages as well.")

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
     and a "
    (xdoc::seetopic "atj-tutorial-acl2-environment"
                    "Java representation of the ACL2 environment")
    ", consisting of "
    (xdoc::seetopic "defun" "function definitions")
    " and "
    (xdoc::seetopic "defpkg" "package definitions")
    ". AIJ also includes a "
    (xdoc::seetopic "atj-tutorial-native-functions"
                    "Java implementation of the ACL2 primitive functions")
    ", and an "
    (xdoc::seetopic "atj-tutorial-evaluator"
                    "ACL2 evaluator written in Java")
    ".")

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
     (If the file already exists, it is overridden.)
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
     The @('call(Acl2Symbol, Acl2Value[])') method
     evaluates an ACL2 function call,
     by invoking the relevant AIJ method (the details are unimportant here).")

   (xdoc::p
    "External Java code must call @('initialize()')
     not only before calling @('call(Acl2Symbol, Acl2Value[])'),
     but also before using AIJ's API to build
     the @('Acl2Symbol') and @('Acl2Value')s
     to pass to @('call(Acl2Symbol, Acl2Value[])').
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
     because @('call(Acl2Symbol, Acl2Value[])') may throw it in general,
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
    " for instructions on how to obtain that jar file.")

   (xdoc::p
    "After compiling, the code can be run via")
   (xdoc::codeblock
    "java -cp [books]/kestrel/java/aij/java/out/artifacts/AIJ_jar/AIJ.jar:. \\"
    "     Test")
   (xdoc::p
    "where again @('[books]/...') must be replaced with a proper path.
     A fairly large number will be printed on the screen.
     Some ACL2 has just been run in Java.")

   (xdoc::p
    "If the @('100') passed to the factorial function call
     is increased to a sufficiently large value,
     the execution of the Java code will result in a stack overflow
     (this is just the JVM running out of stack memory;
     it has nothing to do with type unsafety and security exploits).
     This is unavoidable, because in the deep embedding approach
     the ACL2 functions are evaluated via "
    (xdoc::seetopic "atj-tutorial-evaluator" "AIJ's recursive interpreter")
    ". Note also that recursive method calls in the JVM
     may not be as efficiently implemented as recursive function calls in Lisp,
     given that Java is an imperative language
     and thus loops are the preferred way to repeat computations.
     This stack overflow issue may be mitigated
     by passing a larger stack size to the JVM,
     via the @('-Xss) option to the @('java') command.
     For example,")
   (xdoc::codeblock
    "java -cp [books]/kestrel/java/aij/java/out/artifacts/AIJ_jar/AIJ.jar:. \\"
    "     -Xss1G \\"
    "     Test")
   (xdoc::p
    "runs the factorial program with 1 GiB of stack space,
     which should be larger than the defaut.")

   (atj-tutorial-previous "atj-tutorial-deep-shallow"
                          *atj-tutorial-deep-shallow*)

   (atj-tutorial-next "atj-tutorial-customization"
                      *atj-tutorial-customization*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-customization

  :short (atj-tutorial-short *atj-tutorial-customization*)

  :long

  (xdoc::topstring

   (xdoc::p
    "ATJ provides some options to customize the generated Java code,
     in the form of keyword inputs, which are listed in "
    (xdoc::seetopic "atj" "the reference documentation")
    ". This tutorial page covers the simpler options,
     which apply to both "
    (xdoc::seetopic "atj-tutorial-deep-shallow"
                    "deep and shallow embedding approaches")
    ". The more complex options are covered elsewhere in this tutorial.")

   (xdoc::h3 "Java Package")

   (xdoc::p
    "The Java code generated for the factorial function in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    " has no @('package') declaration [JLS:7.4],
     which means that the generated class is in an unnamed package [JLS:7.4.2].
     This (i.e. the absence of a @('package') declaration) is the default,
     which can be overridden via ATJ's @(':java-package') option.")

   (xdoc::p
    "For the example in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    ", the ATJ call")
   (xdoc::codeblock
    "(java::atj fact :deep t :guards nil :java-package \"mypkg\")")
   (xdoc::p
    "generates a file @('Acl2Code.java') that is the same as before
     but with the package declaration")
   (xdoc::codeblock
    "package mypkg;")
   (xdoc::p
    "at the beginning.")

   (xdoc::p
    "Now that the generated code is in the @('mypkg') package,
     the external Java code exemplified in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    " must be adapted, e.g. by putting it into @('mypkg') as well,
     or by referencing the generated Java class
     via the fully qualified name @('mypkg.Acl2Code'),
     or by importing the class via a declaration @('import mypkg.Acl2Code;').")

   (xdoc::p
    "The string passed as the @(':java-package') option
     must be not only a valid Java package name,
     but also consist only of ASCII characters.
     ATJ does not support the generation of
     package names with non-ASCII characters.")

   (xdoc::p
    "Note that the file is generated in the current directory,
     not in a @('mypkg') directory,
     as may be expected based on Java's typical source file organization.
     The directory where the file is generated
     can be customized via the @(':output-dir') option, described below.")

   (xdoc::h3 "Java Class")

   (xdoc::p
    "The Java class generated for the factorial function in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    " is called @('Acl2Code');
     the generated file is called @('Acl2Code.java'),
     thus satisfying the constraint that a public class resides in a file
     whose name is obtained by adding the @('.java') extension
     to the class name [JLS:7.6].
     This class (and thus file) name is the default,
     which can be overridden via ATJ's @(':java-class') option.")

   (xdoc::p
    "For the example in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    ", the ATJ call")
   (xdoc::codeblock
    "(java::atj fact :deep t :guards nil :java-class \"Fact\")")
   (xdoc::p
    "generates a file @('Fact.java') that is the same as before
     but with @('Fact') as the name of the class.")

   (xdoc::p
    "Now that the generated class is called @('Fact'),
     the external Java code exemplified in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    " must be adapted, by referencing the generated Java class as @('Fact').")

   (xdoc::p
    "The string passed as the @(':java-class') option
     must be not only a valid Java class name,
     but also consist only of ASCII characters.
     ATJ does not support the generation of
     class names with non-ASCII characters.")

   (xdoc::h3 "Output Directory")

   (xdoc::p
    "The Java file generated for the factorial function in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    " resides in the current directory.
     This is the default,
     which can be overridden via ATJ's @(':output-dir') option.")

   (xdoc::p
    "For the example in "
    (xdoc::seetopic "atj-tutorial-deep" "this tutorial page")
    ", the ATJ call")
   (xdoc::codeblock
    "(java::atj fact :deep t :guards nil :output-dir \"java\")")
   (xdoc::p
    "generates the same file @('Acl2Code.java') as before
     but in a subdirectory @('java') of the current directory.
     The subdirectory must already exist; ATJ does not create it.")

   (xdoc::p
    "Needless to say, the invocations of the @('javac') and @('java') commands
     must be adapted to the local of the @('.java') and @('.class') files.")

   (xdoc::p
    "The string must be a valid absolute or relative path
     in the file system of the underlying operating system.
     If it is a relative path, it is relative to the current directory.
     When running ATJ interactively from the ACL2 shell,
     the current directory is the one returned by @(':cbd').
     When running ATJ as part of book certification,
     the current directory should be the same one
     where the @('.lisp') file with the ATJ call resides.")

   (xdoc::p
    "If the @(':java-package') option is also used (see above),
     the @(':output-dir') option can be used to generate the file
     in a subdirectory consistent with the package name,
     according to the typical organization of Java source files.
     For example, if @(':java-package') is @('\"mypkg\"'),
     @(':output-dir') can be set to @('\"mypkg\"') as well.
     As another example, if @(':java-package') is @('\"my.new.pkg\"'),
     @(':output-dir') can be set to @('\"my/new/pkg\"\'),
     assuming a Unix-like operating system
     with forward slashes that separate file path elements.
     As already noted above, all these directories must exist;
     ATJ does not create them.")

   (atj-tutorial-previous "atj-tutorial-deep" *atj-tutorial-deep*)))

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
     (i) variables,
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
     that is "
    (xdoc::seetopic "atj-tutorial-native-functions"
                    "implemented natively via Java code")
    ", not via (a Java representation of) an ACL2 definiens.
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-acl2-environment

  :short (atj-tutorial-short *atj-tutorial-acl2-environment*)

  :long

  (xdoc::topstring

   (xdoc::p
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " provides a Java representation of the ACL2 environment.
     For the "
    (xdoc::seetopic "atj-tutorial-deep" "deep embedding approach")
    ", this environment consists of "
    (xdoc::seetopic "defpkg" "ACL2 package definitions")
    " and "
    (xdoc::seetopic "defun" "ACL2 function definitions")
    "; for the shallow embedding approach,
     this environment consists of package definitions only,
     because in this approach functions are represented as methods
     outside of AIJ.")

   (xdoc::p
    "AIJ represents ACL2 packages
     as objects of the class @('Acl2Package') in the "
    (xdoc::seetopic "atj-tutorial-simplified-uml"
                    "simplified UML class diagram")
    " below.
     An @('Acl2PackageName') is a wrapper of @('java.lang.String')
     that enforces the restrictions of valid package names
     described in @(tsee defpkg).
     An @('Acl2Package') stores, in private fields,
     a name and a list of 0 or more imported symbols.
     A @(tsee defpkg) may also include a documentation string,
     but this is not represented in @('Acl2Package').")

   (xdoc::img :src "res/kestrel-java-atj-images/package-classes.png")

   (xdoc::p
    "The @('Acl2Package') class also has a private static field
     that contains all the packages defined so far,
     as a @('java.util.Map<Acl2PackageName,Acl2Package>') object.
     This map is initially empty;
     it is extended, one package definition at a time,
     via the static method
     @('Acl2Package.define(Acl2PackageName, List<Acl2Symbol>)').
     This method ensures that the first three packages defined are
     @('\"KEYWORD\"'), @('\"COMMON-LISP\"'), and @('\"ACL2\"'),
     in that order;
     these are the first three packages, in that order,
     that appear in the ACL2 @(see world).
     The method also checks that
     @('\"KEYWORD\"') and @('\"COMMON-LISP\"') have empty import lists,
     and that @('\"ACL2\"') only imports symbols from @('\"COMMON-LISP\"').
     These properties, which can be easily checked in an ACL2 shell,
     help guarantee the well-formedness of certain @('Acl2Symbol') instances
     that are pre-created when the class @('Acl2Symbol') is initialized
     (i.e. before any other symbol can be created).
     See AIJ's Java code and Javadoc for more details.")

   (xdoc::p
    "The Java code generated by ATJ repeatedly calls the method
     @('Acl2Package.define(Acl2PackageName, List<Acl2Symbol>)')
     to define all the ACL2 packages
     that are known when ATJ was called to generate the Java code.")

   (xdoc::p
    "AIJ represents ACL2 functions as decribed in "
    (xdoc::seetopic "atj-tutorial-acl2-terms"
                    "AIJ's representation of ACL2 terms")
    ". The "
    (xdoc::seetopic "atj-tutorial-simplified-uml"
                    "simplified UML class diagram")
    " there shows that instances of @('Acl2DefinedFunction')
     have lambda expressions as definientia,
     where each lambda expression consists of
     zero or more formal parameters and a body.
     An ACL2 function definition has additional information,
     such as the guard of the function;
     none of this additional information is currently present
     in AIJ's Java representation.")

   (xdoc::p
    "The @('Acl2DefinedFunction') class also has a private static field
     that contains all the functions defined so far,
     as a @('java.util.Map<Acl2Symbol, Acl2DefinedFunction>') object.
     This map is initially empty;
     it is extended, one function definition at a time,
     via the instance method
     @('Acl2NamedFunction.define(Acl2Symbol[], Acl2Term)'),
     which is abstract in the public class @('Acl2NamedFunction')
     and implemented in the non-public class @('Acl2DefinedFunction').
     Objects of @('Acl2NamedFunction') are interned,
     i.e. there is a unique instance for each function name:
     this is ensured by the public factory method
     @('Acl2NamedFunction.make(Acl2Symbol)'),
     which is the only way for code external to AIJ
     to build @('Acl2NamedFunction') objects.
     Thus, calling the instance method
     @('Acl2NamedFunction.define(Acl2Symbol[], Acl2Term)')
     always defines that unique instance;
     the method sets the private instance field @('definiens').")

   (xdoc::p
    "In the "
    (xdoc::seetopic "atj-tutorial-deep" "deep embedding approach")
    ", the Java code generated by ATJ repeatedly
     builds @('Acl2NamedFunction') instances
     via @('Acl2NamedFunction.make(Acl2Symbol)')
     for all the ACL2 defined functions to be translated to Java,
     and defines each such function by calling
     @('Acl2NamedFunction.define(Acl2Symbol[], Acl2Term)')
     on those instances.
     The ATJ-generated code also uses @('Acl2NamedFunction.make(Acl2Symbol)')
     to build function names as part of the ACL2 terms
     that form the bodies of defined functions;
     there is just one instance for each name, as explained above,
     to which the definition is attached.
     The ATJ-generated code also builds @'Acl2NamedFunction') instances
     for functions that are implemented natively in Java
     (e.g. for the "
    (xdoc::seetopic "acl2::primitive" "ACL2 primitive functions")
    ", which have no definition),
     i.e. for instances of the @('Acl2NativeFunction') class.
     The factory method @('Acl2NamedFunction.make(Acl2Symbol)')
     knows which function symbols have native Java implementations
     and accordingly returns
     either @('Acl2NativeFunction') or @('Acl2DefinedFunction') instances.
     The ATJ-generated code calls
     @('Acl2NamedFunction.define(Acl2Symbol[], Acl2Term)')
     only on instances of @('Acl2DefinedFunction');
     ATJ also knows which ACL2 functions have native Java implementations
     (the implementing method in @('Acl2NativeFunction')
     of @('Acl2NamedFunction.define(Acl2Symbol[], Acl2Term)')
     throws an exception.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-native-functions

  :short (atj-tutorial-short *atj-tutorial-native*)

  :long

  (xdoc::topstring

   (xdoc::p
    "The "
    (xdoc::seetopic "acl2::primitive" "ACL2 primitive functions")
    " have no definition.
     Thus, they cannot be translated to Java
     in the same way as functions with defining bodies can. "
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " provides native Java implementations
     of the ACL2 primitive functions,
     i.e. implementations of the ACL2 primitive functions
     written directly in Java.
     (Here `native' is with respect to ACL2, not Java;
     it has nothing to do with "
    (xdoc::ahref "https://docs.oracle.com/javase/10/docs/specs/jni" "JNI")
    ".)
     These native implementations are used in both "
    (xdoc::seetopic "atj-tutorial-deep-shallow"
                    "the deep and shallow embedding approaches")
    ".")

   (xdoc::p
    "These native implementations are run via
     the public static methods @('Acl2NativeFunction.exec...(...)');
     this class is part of "
    (xdoc::seetopic "atj-tutorial-acl2-terms"
                    "the Java representation of ACL2 terms")
    ". For instance, @('Acl2NativeFunction.execStringp(Acl2Value)')
     natively implements @(tsee stringp).
     Some of these methods have overloaded variants,
     whose purpose is explained elsewhere;
     for now, just consider the ones with all @('Acl2Value') arguments.")

   (xdoc::p
    "Besides native implementations of the ACL2 primitive functions,
     there are also native implementations of other built-in ACL2 functions,
     e.g. @('Acl2NativeFunction.execStringAppend(Acl2Value, Acl2Value)')
     for @(tsee string-append).
     The main motivation is efficiency:
     a native Java implementation can be faster than
     mimicking ACL2's execution (in either the deep or shallow embedding).
     In fact, this is also why some built-in ACL2 functions have "
    (xdoc::seetopic "atj-tutorial-background" "raw Lisp code")
    ", i.e. native Lisp implementations.
     Another motivation is to avoid "
    (xdoc::seetopic "atj-tutorial-background" "circularities")
    " that exist in the ACL2 definitions
     unless the raw Lisp code is taken into account.
     More native Java implementations can be added to AIJ as needed;
     it could be argued that all the ACL2 functions with raw Lisp code
     should be implemented natively in Java in AIJ, for symmetry.
     The only drawback, besides the effort to do that,
     is a weakening of the assurance argument;
     however, for true assurance,
     the primitive function implementations will have to be formally verified,
     and if the machinery to do that is in place,
     formally verifying the non-primitive function implementations
     may not entail significantly more effort,
     or at least not ``superlinear'' effort.")

   (xdoc::p
    "Generally, AIJ's native Java implementations of ACL2 functions
     are realized by methods in @('Acl2Value') and its subclasses,
     called by the @('Acl2NativeFunction.exec...(...)') methods.
     This takes advantage of Java's dynamic dispatch
     to avoid checking types at run time.
     For example, to implement @(tsee stringp),
     the @('Acl2Value.stringp()') method returns
     (the Java representation of) @('nil');
     this default implementation is inherited
     by all the @('Acl2Value') subclasses except for @('Acl2String'),
     which overrides it to return @('t') instead.
     @('Acl2NativeFunction.execStringp(Acl2Value)')
     invokes @('stringp()') on its argument:
     this selects, in constant time,
     either the default implementation or the overriding one,
     based on the run-time type type of the argument @('Acl2Value').
     As another example, to implement @(tsee char-code),
     the @('Acl2Value.charCode()') method returns 0,
     because this function's completion axiom says that
     this function returns 0 on non-characters;
     this default implementation is inherited
     by all the @('Acl2Value') subclasses except for @('Acl2Character'),
     which overrides it to return the character's code instead.
     @('Acl2NativeFunction.execCharCode(Acl2Value)')
     invokes @('charCode()') on its argument:
     this selects, in constant time,
     either the default implementation or the overriding one,
     based on the run-time type type of the argument @('Acl2Value').
     The ACL2 primitive functions for arithmetic (e.g. @(tsee binary-+))
     are implemented by methods in @('Acl2Value') and subclasses
     that exhibit interesting patterns of dynamic dispatch
     and interplay among the methods for different operations;
     see AIJ's code and Javadoc for details.")

   (xdoc::p
    "Instead of taking advantage of dynamic dispatch,
     an alternative implementation strategy could use
     run-time type checks and casts.
     For example, @('Acl2NativeFunction.execStringp(Acl2Value)')
     could test whether the argument is an instance of @('Acl2String'),
     and return @('t') or @('nil') accordingly.
     As another example, @('Acl2NativeFunction.execCharCode(Acl2Value)')
     could test whether the argument is an instance of @('Acl2Character'),
     and return the character's code or 0 accordingly.
     It is not clear which approach is more efficient
     (dynamic dispatch or type checks/casts):
     on the one hand, it seems that dynamic dispatch should be more efficient;
     on the other hand, since type checks/casts are relatively frequent in Java,
     they are presumably realized efficiently in Java implementations.
     In any case, the dynamic dispatch approach looks elegant
     and is appropriate to Java's object-oriented paradigm.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-tutorial-evaluator

  :short (atj-tutorial-short *atj-tutorial-evaluator*)

  :long

  (xdoc::topstring

   (xdoc::p
    "For the "
    (xdoc::seetopic "atj-tutorial-deep" "deep embedding approach")
    ", "
    (xdoc::seetopic "atj-tutorial-aij" "AIJ")
    " provides an ACL2 evaluator written in Java.
     This evaluator is realized via
     the implementing methods of the abstract methods
     @('Acl2Term.eval(Acl2Value[])') and @('Acl2Function.eval(Acl2Value[])';
     The implementing methods are
     in subclasses of @('Acl2Term') and @('Acl2Function').
     Recall that all these classes provide "
    (xdoc::seetopic "atj-tutorial-acl2-terms"
                    "the Java representation of ACL2 terms")
    ".")

   (xdoc::p
    "In early versions of AIJ,
     the @('eval') methods in @('Acl2Term') and subclasses
     took a @('java.lang.Map<Acl2Symbol, Acl2Value>') as argument,
     instead of an @('Acl2Value[]') as in the current version of AIJ.
     Such a map was a binding of variables (i.e. symbols) to values,
     with respect to which quoted constants, variables, and function calls
     were evaluated:")
   (xdoc::ul
    (xdoc::li
     "Evaluating a quoted constant returned its value,
      independently from the binding of variables to values.")
    (xdoc::li
     "Evaluating a variable returned the value associated to the variable,
      which was looked up in the binding.")
    (xdoc::li
     "Evaluating a function call caused
      first the recursive evaluation of all the arguments of the call,
      and then the application of the function to the resulting values.
      (See below.)"))
   (xdoc::p
    "The @('apply') methods in @('Acl2Function') and subclasses
     took an @('Acl2Value[]') argument in all versions of AIJ.
     The array is the sequence of values to apply the function to.
     Function application proceeded as follows:")
   (xdoc::ul
    (xdoc::li
     "Applying a lambda expression returned the result of
      recursively evaluating the body of the lambda expression
      with a binding of the parameters of the lambda expressions
      to the argument values.
      (Recall that lambda expressions are always closed
      in ACL2 " (xdoc::seetopic "acl2::term" "translated terms") ",
      so each lambda expression body is evaluated in a new binding.)")
    (xdoc::li
     "Applying a "
     (xdoc::seetopic "atj-tutorial-native-functions"
                     "natively implemented function")
     " returned the result of executing the native Java implementation
      on the argument values.")
    (xdoc::li
     "Applying a function with an ACL2 definition returned the result of
      recursively evaluating the body of the function
      with a binding of the parameters of the function
      to the argument values."))
   (xdoc::p
    "This simple and typical evaluation algorithm worked,
     but the evaluation of each variable involved a map lookup.
     The use of hash maps made this lookup essentially constant-time,
     but still a relatively large constant.
     Thus, the current version of AIJ uses a more optimized approach,
     described as follows.")

   (xdoc::p
    "Each @('Acl2Variable') instance includes
     a numeric index, in a private field.
     The index is initially -1 (when the object is created),
     which means that it is not set yet.
     When AIJ's public API is used to provide a function definition
     (which is added to the Java representation of the ACL2 environment),
     AIJ sets all the indices in the @('Acl2Variable')s
     that occur the definiens of the function.
     The setting of indices starts with the parameters and body of the function:
     the 0-based position of each parameter in the parameter list
     is the value to which all the occurrences of that variables are set;
     when a lambda expression is encountered,
     the variables in its body are given indices
     based on the parameters of the lambda expression,
     ignoring the outer indices
     (recall that lambda expressions are always closed
     in ACL2 " (xdoc::seetopic "acl2::term" "translated terms") ").
     In assigning these indices,
     AIJ ensures that the definiens of the function is well-formed,
     e.g. that it does not include variables that are not parameters.
     Because the same ACL2 variable
     may have different indices in different contexts,
     generally the @('Acl2Term') instances passed to AIJ to define functions
     must not share any @('Acl2Variable') instances;
     AIJ throws an exception if, during the index setting recursion,
     it encounters an @('Acl2Variable') whose index is already set.")

   (xdoc::p
    "Given these variable indices, a binding or variables to values
     can be represented as a map from indices (i.e. natural numbers) to values
     instead of a map from symbols to values.
     But a map from indices to values can be represented as an array,
     and that is why the @('eval') methods of @('Acl2Term') and subclasses
     take an @('Acl2Value[]') as argument:
     that argument is still a binding of variables to values,
     but the variables are represented by indices.
     An array access is much faster than a hash map access.")

   (xdoc::p
    "The evaluation algorithm on terms is still the one described above,
     except that the bindings are represented as arrays instead of maps.
     The evaluation of terms is mutually recursive with
     the application of functions to values.
     This ACL2 evaluation is ``in the logic'':
     guards are completely ignored,
     and in fact not even currently represented in AIJ.")

   (xdoc::p
    "See the AIJ code and Javadoc for more details on the ACL2 evaluator.")))
