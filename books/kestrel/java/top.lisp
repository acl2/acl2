; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the JAVA topic below:
(include-book "aij/top")
(include-book "atj/top")
(include-book "language/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ java
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this library contains:")
   (xdoc::ul
    (xdoc::li
     "A deep embedding of ACL2 in Java.")
    (xdoc::li
     "A Java code generator for ACL2.")
    (xdoc::li
     "A formalization in ACL2 of some aspects of the Java language."))
   (xdoc::p
    "It is expected that this library will be extended with more
     Java-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The "
     (xdoc::a :href "https://docs.oracle.com/javase/specs/jls/se13/html"
       "Java language specification")
     ", referenced as `[JLS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JLS:4.2]' references Section 4.2 of [JLS].")
    (xdoc::li
     "The "
     (xdoc::a :href "https://docs.oracle.com/javase/specs/jvms/se13/html"
       "Java Virtual Machine specification")
     ", referenced as `[JVMS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JVMS:5.5]' references Section 5.5 of [JVMS].")
    (xdoc::li
     "The "
     (xdoc::a :href "https://docs.oracle.com/en/java/javase/13/docs/api"
       "Java API specification")
     ", referenced as `[JAPIS]' in the documentation of this library."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc aij-atj-paper
  :parents (aij atj)
  :short "ACL2-2018 Workshop paper on AIJ and ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::a :href "https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22018.1"
      "ACL2-2018 Workshop paper on AIJ and ATJ")
    " provides an overview of AIJ and ATJ,
     along with some performance measurements.
     The presentation of the Workshop talk is available "
    (xdoc::a
     :href "https://www.cs.utexas.edu/users/moore/acl2/workshop-2018/program.html"
      "here")
    ".")
   (xdoc::p
    "As AIJ and ATJ are being extended and improved over time,
     some of the contents of the paper and presentation are becoming outdated.
     This manual provides up-to-date information about AIJ and ATJ.
     The following differences exist
     between the current version of AIJ and ATJ
     and the version described in the paper and presentation:")
   (xdoc::ul
    (xdoc::li
     "The Java class @('Acl2Constant')
      has been renamed to @('Acl2QuotedConstant').")
    (xdoc::li
     "The Java class @('Acl2Cons')
      has been renamed to @('Acl2ConsPair').")
    (xdoc::li
     "The Java class @('Acl2FunctionApplication')
      has been renamed to @('Acl2FunctionCall').")
    (xdoc::li
     "AIJ's evaluator has been extended
      to recognize a ``pseudo-function'' @('or')
      and to execute it non-strictly,
      as an optimized version of an @(tsee if)
      whose test and `then' branch are the same.
      Accordingly, ATJ has been extended
      to recognize translated terms of the form @('(if a a b)')
      and to generate Java code to represent them as @('(or a b)').")
    (xdoc::li
     "The Java representation of ACL2 variables
      has been optimized to include numeric indices
      derived from the position of variables
      in the lists of parameters
      in named function definitions and lambda expressions.
      These indices are set in the body of each function definition
      as the function definition is added to
      the Java representation of the ACL2 environment.
      The AIJ evaluator has been optimized to use
      Java arrays of ACL2 values as bindings,
      instead of hash maps from ACL2 symbols to values,
      enabling faster lookup of variables in bindings.")
    (xdoc::li
     "The Java representation of ACL2 named functions
      has been changed to consist of native and defined functions.
      The former have a native Java implementation,
      while the latter have a definition
      in the Java representation of the ACL2 environment.
      All the ACL2 primitive functions are represented as native functions,
      the ``pseudo-function'' @('or') is represented like that as well,
      and other built-in ACL2 functions could be represented like that as well
      in the future.
      Each native function has its own unique Java class and instance:
      its application to values is now handled via Java's dynamic dispatch
      rather than by cases analysis, thus optimizing evaluation.
      Each defined function has its own unique instance as well
      (so, all the ACL2 named functions are interned),
      and its representation includes its definition,
      so that evaluation no longer needs to
      look up the function definition in the environment,
      resulting in increased execution speed.")
    (xdoc::li
     "The Java class @('Acl2Environment') has been eliminated.
      The information about the function definitions
      is now stored directly with the function themselves.
      The information about the package definitions
      is now stored directly into instances of a Java class @('Acl2Package')
      that has been added for this purpose;
      this class also contains the information about the package witness name.")
    (xdoc::li
     "The package witness name,
      i.e. the content of the @('*pkg-witness-name*') constant,
      is now stored in a final static field,
      which therefore no longer needs to be initialized
      by code external to AIJ.
      The consistency of this Java value with the actual ACL2 value
      is checked via an assertion in a newly added file
      @('[books]/kestrel/java/aij/assumptions.lisp').")
    (xdoc::li
     "The return types of some of the native Java implementation methods
      of the ACL2 primitive functions in AIJ
      have been made more precise than the general type @('Acl2Value'),
      e.g. now the method for @(tsee equal) returns @('Acl2Symbol').")
    (xdoc::li
     "Some native Java implementations of ACL2 primitive functions
      have been optimized.")
    (xdoc::li
     "Public static methods have been added
      to execute the native implementations of ACL2 functions
      from outside AIJ.
      This is in support of the shallow embedding approach (see below).")
    (xdoc::li
     "Some variant native implementations of ACL2 functions
      have been added that assume the satisfaction of the guards.
      This is in support of the shallow embedding approach (see below)
      when assuming that the guards are satisfied (see below).")
    (xdoc::li
     "AIJ has been extended with the ability to validate statically that
      all the function calls reference existing functions
      and have a number of arguments that matches the function arity.
      AIJ provides a new public API method
      to validate all the currently defined functions.
      AIJ can thus avoid these checks at run time,
      resulting in increased execution speed.")
    (xdoc::li
     "ATJ has been extended with a facility to generate Java code
      to execute tests that compare
      results obtained via evaluation in ACL2
      with results obtained via evaluation in AIJ.")
    (xdoc::li
     "ATJ has been extended with a facility to generate Java code
      according to a shallow embedding approach,
      in addition to the deep embedding approach described in the paper.")
    (xdoc::li
     "ATJ has been extended with a facility to generate Java code
      assuming that all the guards are satisfied.
      This facility is available for
      both the deep and shallow embedding approaches."))
   (xdoc::p
    "The last two bullet points above provide a major extension of ATJ,
     which produces much more readable and efficient Java code,
     including Java code that manipulates Java primitive types and arrays.")))
