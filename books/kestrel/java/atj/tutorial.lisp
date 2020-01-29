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

(defconst *atj-tutorial-uml*
  "About the Simplified UML Class Diagrams")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

   (atj-tutorial-previous "atj-tutorial-motivation" *atj-tutorial-motivation*)

   (atj-tutorial-next "atj-tutorial-motivation" *atj-tutorial-motivation*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     as immutable objects of class @('Value') and its subclasses
     in the "
    (xdoc::seetopic "atj-tutorial-simplified-uml"
                    "simplified UML class diagram")
    " below.")

   (xdoc::p
    "In AIJ's actual code,
     each class name is prefixed with `@('Acl2')' (e.g. @('Acl2Value')),
     so that external code can reference these classes unambiguously
     without AIJ's package name @('edu.kestrel.acl2.aij').
     This tutorial omits the prefix for brevity,
     and uses fully qualified names for the Java standard classes
     to avoid ambiguities,
     e.g. @('java.lang.String') is the Java standard string class,
     as distinguished from @('String') in the UML diagram above.")

   (xdoc::img :src "res/kestrel-java-atj-images/value-classes.png")

   (xdoc::p
    "Each class in the UML diagram above, except @('PackageName'),
     corresponds to a set
     in the earlier picture of ACL2 values (in blue).
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

   (xdoc::p
    "The information about the represented ACL2 values
     is stored in fields of the non-abstract classes.
     @('Integer') stores
     the numeric value as a @('java.math.BigInteger').
     @('Ratio') stores
     the numerator and denominator as @('Integer')s,
     in reduced form
     (i.e. their greatest common divisor is 1
     and the denominator is greater than 1).
     @('ComplexRational') stores
     the real and imaginary parts as @('Rational')s.
     @('Character') stores
     the 8-bit code of the character as a @('char') below 256.
     @('String') stores
     the codes and order of the characters as a @('java.lang.String')
     whose @('char')s are all below 256.
     @('Symbol') stores
     the symbol's package name as a @('PackageName')
     (a wrapper of @('java.lang.String')
     that enforces the ACL2 constraints on package names)
     and the symbol's name as a @('String').
     @('Cons') stores the component @('Value')s.
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
     For example, @('Character.make(char)')
     returns a @('Character') with the supplied argument as code,
     throwing an exception if the argument is above 255.
     As another example, @('Cons.make(Value,Value)')
     returns a @('Cons') with the supplied arguments as components.
     Some classes provide overloaded variants,
     e.g. @('Integer.make(int)') and @('Integer.make(java.math.BigInteger)').
     All these classes provide no public Java constructors,
     thus encapsulating the details of object creation and re-use,
     which is essentially transparent to external code
     because these objects are immutable.")

   (xdoc::p
    "The public classes for ACL2 values in the UML diagram above
     provide public instance getter methods
     to unbuild (i.e. extract information from) instances of these classes.
     For example, @('Character.getJavaChar()')
     returns the code of the character
     as a @('char') that is always below 256.
     As another example, @('Cons.getCar()') and @('Cons.getCdr()')
     return the component @('Value')s of the \acl{cons') pair.
     Some classes provide variants,
     e.g. @('Integer.getJavaInt()')
     (which throws an exception if the integer does not fit in an @('int'))
     and @('Integer.getJavaBigInteger()').")

   (xdoc::p
    "Thus, AIJ provides a public API to
     build and unbuild Java representations of ACL2 values.
     When talking about AIJ,
     this tutorial calls `build' and `unbuild'
     what is often called `construct' and `destruct' in functional programming,
     because in object-oriented programming the latter terms
     may imply object allocation and deallocation,
     which is not necessarily what the AIJ API does.")

   (xdoc::p
    "For more details on AIJ's implementation and API of ACL2 values,
     see the Javadoc in AIJ's Java code.")

   (atj-tutorial-previous "atj-tutorial-aij" *atj-tutorial-aij*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
