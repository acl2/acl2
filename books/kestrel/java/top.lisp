; Java Library
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ java
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Java."
  :long
  (xdoc::topapp
   (xdoc::p
    "Currently this library contains:")
   (xdoc::ul
    (xdoc::li
     "A deep embedding of ACL2 in Java.")
    (xdoc::li
     "A Java code generator for ACL2."))
   (xdoc::p
    "It is expected that this library will be extended with more
     Java-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/specs/jls/se10/html\"
      >Java language specification</a>,
      referenced as `[JLS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JLS:4.2]' references Section 4.2.")
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/specs/jvms/se10/html\"
      >Java Virtual Machine specification</a>,
      referenced as `[JVMS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JVMS:5.5]' references Section 5.5.")
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/10/docs/api\"
      >Java API specification</a>,
      referenced as `[JAPIS]' in the documentation of this library."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc aij-atj-paper
  :parents (aij atj)
  :short "ACL2-2018 Workshop paper on AIJ and ATJ."
  :long
  (xdoc::topapp
   (xdoc::p
    "The <a href=\"https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22018.1\"
     >ACL2-2018 Workshop paper on AIJ and ATJ</a>
     provides an overview of AIJ and ATJ,
     along with some performance measurements.
     The presentation of the Workshop talk is available
     <a href=\"https://www.cs.utexas.edu/users/moore/acl2/workshop-2018/program.html\"
     >here</a>.")
   (xdoc::p
    "As AIJ and ATJ are being extended and improved over time,
     some of the contents of the paper and presentation are becoming outdated.
     This manual provides up-to-date information about AIJ and ATJ.
     The following differences exist
     between the current version of AIJ and ATJ
     and the contents of the paper and presentation:")
   (xdoc::ul
    (xdoc::li
     "The Java class @('Acl2Constant')
      has been renamed to @('Acl2QuotedConstant').")
    (xdoc::li
     "The Java class @('Acl2Cons')
      has been renamed to @('Acl2ConsPair').")
    (xdoc::li
     "AIJ's evaluator has been extended
      to recognize a ``primitive pseudo-function'' @('or')
      and to execute it non-strictly,
      as an optimized version of an @(tsee if)
      whose test and ``then'' branch are the same.
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
      enabling faster lookup of variables in bindings.
      These optimizations provide roughly a 2x speedup
      on the examples in the paper
      (except for the factorial example,
      where big integer multiplication dominates).")
    (xdoc::li
     "ATJ has been extended with a facility to generate Java code
      to execute tests that compare
      results obtained via evaluation in ACL2
      with results obtained via evaluation in AIJ."))))
