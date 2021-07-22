; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (yul)
  :short "Concrete syntax of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of an ABNF grammar based on the grammar in [Yul].
     We parse the ABNF grammar into an ACL2 representation.")
   (xdoc::p
    "More precisely, there are currently two published grammar of Yul:
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
     we like to keep it for now, along with the new one."))
  :order-subtopics t)
