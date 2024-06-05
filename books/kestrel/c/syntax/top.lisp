; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")
(include-book "abstract-syntax-operations")
(include-book "concrete-syntax")
(include-book "preprocess-file")
(include-book "parser")
(include-book "read-files")
(include-book "parse-files")
(include-book "print-files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-for-tools
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
     we also introduce a concrete syntax, based on an ABNF grammar.
     This is not a different syntax for C,
     but just a different formulation of the syntax of C,
     motivated by the fact that we want this tool-oriented syntax
     to be neither before nor after preprocessing,
     but to incorporate constructs from both forms of the C code;
     the grammar in [C] is organized differently,
     with preprocessing being a distinguished translation phase
     [C:5.1.1.2].")
   (xdoc::p
    "We also provide a parser from the concrete syntax to the abstract syntax.
     The parser is an initial version;
     it covers all of the C constructs after preprocessing,
     but has limitations in the handling of
     certain inherently ambiguous constructs
     that are notoriously complex in C;
     we will improve our parser in this respect soon.")
   (xdoc::p
    "In order to process typical C code,
     we also provide an ACL2 tool to invoke a C preprocessor.
     The tool can be run on headers and source files,
     to obtain preprocessed source files,
     which can be then parsed by our parser.")
   (xdoc::p
    "We also provide a (pretty-)printer that turns our abstract syntax
     into concrete syntax that is valid C code.
     Like the parser and the abstract syntax,
     our printer covers all the C constructs after preprocessing.")
   (xdoc::p
    "We also plan to add a checker on the abstract syntax
     for the static constraints on C code (i.e. type checker etc.),
     which may result in an elaboration of the abstract syntax,
     e.g. to enhance the abstract syntax with types and other information
     after successful checking.")
   (xdoc::p
    "We also plan to prove theorems connecting this tool-oriented syntax
     with the language formalization in @(see c::language).")
   (xdoc::p
    "All the items described above form a sub-library of our ACL2 library for C,
     in the directory @('[books]/kestrel/c/syntax').
     For this sub-library, we use a different package from @('C'),
     in particular to separate otherwise possibly homonymous types and functions
     in this tool-oriented abstract syntax as opposed to
     the abstract syntax used for the language formalization
     under @('[books]/kestrel/c/language').
     We pick the name @('C$') for this sub-library,
     where the @('$') conveys the idea of `syntax'.
     This package naming pattern could be used for
     ACL2 libraries (and sub-libraries) for other programming languages."))
  :order-subtopics (abstract-syntax
                    concrete-syntax
                    preprocessing
                    parser
                    printer
                    read-files
                    parse-files
                    print-files))
