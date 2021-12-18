; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "grammar-old")
(include-book "grammar-new")

(include-book "lexer")
(include-book "tokenizer")
(include-book "parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (language)
  :short "Concrete syntax of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete syntax is defined by an ABNF grammar based on the grammar in [Yul].
     We parse the ABNF grammar into an ACL2 representation.")
   (xdoc::p
    "More precisely, there are currently two published grammars of Yul:
     one is in [Yul: Specification of Yul];
     the other is part of the Solidity grammar in "
    (xdoc::ahref "https://docs.soliditylang.org/en/latest/grammar.html"
                 "this section of the Solidity documentation")
    ". The Yul team has told us that the former is older than the latter,
     and that the plan is to have a separate Yul grammar
     along the lines of the one that is part of the Solidity grammar.
     For now, we formalize both grammars in ABNF,
     and we parse both grammars into ACL2.
     (The reason is somewhat accidental:
     we initially formalized and parsed the old grammar,
     after which we were told that the other grammar is new;
     but since we have the old one formalized and parsed already,
     we like to keep it for now, along with the new one.")
   (xdoc::p
    "The old and new grammar have the following differences:")
   (xdoc::ul
    (xdoc::li
     "The old grammar allows dots in identifiers,
      while the new grammar does not.
      However, the new grammar introduces a notion of path,
      which is a sequence of one or more dot-separated identifiers;
      paths can be used as expressions and can be assigned to.")
    (xdoc::li
     "The old grammar includes type names, defined as identifiers,
      while the new grammar does not have that notion.
      In particular, no optional types are allowed by the new grammar
      for literals, declared variables, and function inputs and outputs.")
    (xdoc::li
     "The old grammar allows any expression as statement,
      while the new grammar allows only function calls.")
    (xdoc::li
     "The old grammar allows any expression
      to initialize multiple variables or to assign to multiple variables,
      while the new grammar allows only function calls.")
    (xdoc::li
     "The old grammar allows leading zeros in decimal numbers,
      while the new grammar disallows them.")
    (xdoc::li
     "The old and new grammar have
      somewhat different definitions of string literals.
      In particular, the new grammar clarifies the underlying character set,
      which was implicit in the old grammar due to the use of
      a complement and a wildcard.
      The old grammar only allows surrounding double quotes,
      while the new grammar also allows surrounding single quotes.")
    (xdoc::li
     "The new grammar adds hex strings to the possible literals.")))
  :order-subtopics t)
