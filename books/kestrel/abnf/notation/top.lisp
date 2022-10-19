; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "abstract-syntax")
(include-book "semantics")
(include-book "convenience-constructors")
(include-book "core-rules")
(include-book "core-rules-validation")
(include-book "concrete-syntax-rules")
(include-book "concrete-syntax-rules-validation")
(include-book "concrete-syntax")
(include-book "concrete-syntax-validation")
(include-book "syntax-abstraction")
(include-book "meta-circular-validation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ notation
  :parents (abnf)
  :short "A fornalization of the ABNF notation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the syntax and semantics of the ABNF notation.")
   (xdoc::p
    "We start with an "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " of ABNF, derived from the concrete syntax.
     Even though the concrete syntax is specified in ABNF,
     we do not use ABNF to specify this abstract syntax,
     thus avoiding the meta-circularity.")
   (xdoc::p
    "Then we define a @(see semantics) of ABNF based on the abstract syntax,
     in terms of matching relations
     between (concrete syntax) trees
     and abstract syntactic entities.")
   (xdoc::p
    "With a formal semantics in hand, we proceed to formalize the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    " of ABNF using ABNF itself, as follows.")
   (xdoc::p
    "The files @('concrete-syntax-rules.abnf') and @('core-rules.abnf')
     contain the ABNF grammar of ABNF, along with the core rules.
     The latter are more general than the ABNF grammar of ABNF,
     but in a way they are a part of the ABNF notation,
     so it seems appropriate for the core rules to be here.")
   (xdoc::p
    "Since at this point of the bottom-up development of the formalization
     we do not yet have a formalization of the concrete syntax of ABNF,
     we cannot directly use the contents of those two files
     to formalize the concrete syntax of ABNF,
     again for meta-circular reasons.
     We break that circularity by writing those rules in abstract syntax,
     deriving them from the contents of the files.")
   (xdoc::p
    "To make the rules written in abstract syntax
     look more like if they were written in concrete syntax,
     we introduce some "
    (xdoc::seetopic "convenience-constructors" "convenience constructors")
    " for ABNF abstract syntax.
     We use them to define, in abstract syntax, the "
    (xdoc::seetopic "core-rules" "core rules")
    " and the "
    (xdoc::seetopic "concrete-syntax-rules" "concrete syntax rules")
    ". We perform some "
    (xdoc::seetopic "core-rules-validation"
                    "validation of the core rules")
    " and some "
    (xdoc::seetopic "concrete-syntax-rules-validation"
                    "validation of the concrete syntax rules")
    ", using some of the "
    (xdoc::seetopic "operations" "grammar operations")
    ".")
   (xdoc::p
    "We put concrete syntax rules and (the used) core rules together
     to formalize the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ", making use of the ABNF @(see semantics)
     applied to the grammar of ABNF
     (in its abstract syntax form,
     which is what the semantics is defined on).")
   (xdoc::p
    "To complete the formalization of the ABNF notation,
     we formalize the relation between concrete and abstract syntax via a "
    (xdoc::seetopic "syntax-abstraction"
                    "syntax abstraction mapping")
    " from concrete syntax trees of ABNF to abstract syntax tree of ABNF.")
   (xdoc::p
    "We also perform some "
    (xdoc::seetopic "concrete-syntax-validation"
                    "validation of the concrete syntax")
    ", via some of the "
    (xdoc::seetopic "operations" "grammar operations")
    ".")
   (xdoc::p
    "With a formalization of the ABNF notation in hand,
     we develop a "
    (xdoc::seetopic "grammar-parser" "verified parser of ABNF grammars")
    ", whose verification rests on the formalization of the ABNF notation.
     The parser is not part of the formalization of the ABNF notation,
     but we use it to "
    (xdoc::seetopic "meta-circular-validation" "validate the meta-circularity")
    " with which [RFC] defines the syntax of ABNF."))
  :order-subtopics t)
