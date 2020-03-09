; Simple Programming Language Imp Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SIMPL-IMP")

(include-book "abstract-syntax")
(include-book "semantics")
(include-book "interpreter")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imp-language
  :parents (acl2::projects acl2::kestrel-books)
  :short "An ACL2 library for the simple programming language Imp."
  :long
  (xdoc::topstring
   (xdoc::p
    "Imp is a simple programming language,
     used mainly for didactic purposes.
     It is found (with small variations) in textbooks and course materials,
     such as "
    (xdoc::ahref
     "https://www.cs.cmu.edu/~mfredrik/15414/lectures/10-semantics.pdf"
     "these lecture slides")
    " and "
    (xdoc::ahref
     "https://softwarefoundations.cis.upenn.edu/current/lf-current/Imp.html"
     "this textbook")
    ".")
   (xdoc::p
    "This library contains a formalization of Imp in ACL2,
     and is expected to be extended with additional material
     related to formal verification and synthesis of Imp programs.
     The package name of this library, @('\"SIMPL-IMP\"'),
     consists of `SIMPL' for `Simple Programming Language'
     (where the `P' can be in either word)
     and `IMP' for `Imp'.
     ACL2 libraries for other simple programming languages could use
     a similar package @('\"SIMPL-...\"') package naming scheme.")
   (xdoc::p
    "Imp is informally defined by the following elements:")
   (xdoc::ul
    (xdoc::li
     "Arithmetic expressions,
      consisting of
      integer constants (of any size),
      variables (i.e. symbolic names),
      and a few arithmetic operators like addition multiplication.
      These expressions are always integer-valued,
      without any size limitations;
      the arithmetic operators are exact, i.e. not modular.")
    (xdoc::li
     "Boolean expressions,
      consisting of
      boolean constants (one for truth and one for falsehood),
      equalities and inequalities of arithmetic expressions,
      boolean negation,
      and boolean conjunction.
      These expressions are always boolean-valued.")
    (xdoc::li
     "Commands (i.e. statements),
      consisting of
      assignments of arithmetic expressions to variables,
      sequencing (i.e. following a command with another command),
      conditionals (`if-then-else'),
      and loops.
      These commands operate on a state consisting of
      values stored in variables."))
   (xdoc::p
    "Imp does not have user-defined functions or procedures.
     An Imp program is a command, which operates on a variable store.
     Variables always contain integers (of any size);
     they do not contain booleans."))
  :order-subtopics t)
