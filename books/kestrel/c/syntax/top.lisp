; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc syntax-for-tools
  :parents (c::c)
  :short "A syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an abstract syntax of C
     for use by tools that manipulate C code, e.g. C code generators.
     This abstract syntax preserves (i.e. does not abstract away)
     much of the information in the concrete syntax,
     in order to afford more control on
     the form of the code produced by those tools.")
   (xdoc::p
    "Currently this abstract syntax covers all of C after preprocessing,
     but we plan to extend it to include
     at least some forms of preprocessing constructs and comments,
     to afford even more control on the code produced by tools.
     Supporting all possible forms of preprocessing constructs and comments
     would be challenging in an abstract syntax,
     but certain constructs are relatively simple
     (such as @('#include') directives at the top level,
     or comments accompanying function definitions),
     and increasingly elaborate forms can be introduced incrementally.
     We may even add some information about file layout,
     if that turns out to be useful.")
   (xdoc::p
    "The idea of this tool-oriented abstract syntax is also discussed in
     @(see c::abstract-syntax) and @(see c::atc-abstract-syntax).
     We plan to have ATC use this new tool-oriented abstract syntax.")
   (xdoc::p
    "Accompanying this tool-oriented abstract syntax,
     we plan to add a concrete syntax, based on an ABNF grammar.
     This is not a different syntax for C,
     but just a different formulation of the syntax of C,
     motivated by the fact that we want this tool-oriented syntax
     to be neither before nor after preprocessing,
     but to incorporate constructs from both forms of the C code;
     the grammar in [C] is organized differently,
     with preprocessing being a distinguished translation phase
     [C:5.1.1.2].")
   (xdoc::p
    "We also plan to add a parser and a pretty-printer
     that connect these tool-oriented concrete and abstract syntax.
     We also plan to add a checker on the abstract syntax
     for the static constraints on C code (i.e. type checker etc.),
     which may result in an elaboration of the abstract syntax,
     e.g. to enhance the abstract syntax with types and other information
     after successful checking.")
   (xdoc::p
    "We also plan to prove theorems connecting this tool-oriented syntax
     with the language formalization in @(see c::language).")))
