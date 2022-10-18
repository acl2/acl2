; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-parser/executable")
(include-book "syntax-abstraction")

; (depends-on "../notation/core-rules.abnf")
; (depends-on "../notation/concrete-syntax-rules.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ meta-circular-validation
  :parents (abnf)
  :short "A validation of the meta-circularity in
          the concrete syntax definition of ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "[RFC] defines the concrete syntax of ABNF meta-circularly, using ABNF.
     Our formalization of the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    " of ABNF is not meta-circular,
     because it would be impossible in a theorem prover like ACL2.
     Nonetheless, here we provide a validation of the meta-circularity.")
   (xdoc::p
    "We use the "
    (xdoc::seetopic "grammar-parser" "verified grammar parser")
    " and the "
    (xdoc::seetopic "syntax-abstraction" "executable syntax abstractor")
    " to parse and abstract the core rules and the concrete syntax rules,
     from the respective grammar files,
     and we show that we obtain exactly the same rules, in abstract syntax,
     that we manually define for "
    (xdoc::seetopic "core-rules" "the core rules")
    " and for "
    (xdoc::seetopic "concrete-syntax-rules" "the concrete syntax rules")
    ". In other words, the same grammar rules that we write manually
     are obtained by correctly processing the grammar files
     (where `correctly' refers to the fact that
     the grammar parser is verified)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *core-rules-parsed*
  :short "Parse tree of the text that contains the core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('core-rules.abnf') contains
     the definition of the core rules of ABNF
     using the concrete syntax of ABNF itself,
     copied and pasted from [RFC].
     Calling @(tsee parse-grammar-from-file) on that file yields a parse tree.
     This shows that the executable grammar parser
     parses the core rules of ABNF without errors.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (make-event
   (mv-let (tree state)
       (parse-grammar-from-file
        (string-append (cbd) "../notation/core-rules.abnf")
        state)
     (value `(progn
               (defconst *core-rules-parsed* ',tree)
               (add-const-to-untranslate-preprocess *core-rules-parsed*)
               (defthm treep-of-*core-rules-parsed*
                 (treep *core-rules-parsed*)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *concrete-syntax-rules-parsed*
  :short "Parse tree of the text that contains
          the concrete syntax rules of ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('concrete-syntax-rules.abnf') contains
     the definition of the concrete syntax of ABNF
     using the concrete syntax of ABNF itself,
     copied and pasted from [RFC].
     Calling @(tsee parse-grammar-from-file) on that file yields a parse tree.
     This shows that the executable grammar parser
     parses the definition of the concrete syntax of ABNF without errors.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (make-event
   (mv-let (tree state)
       (parse-grammar-from-file
        (string-append (cbd) "../notation/concrete-syntax-rules.abnf")
        state)
     (value `(progn
               (defconst *concrete-syntax-rules-parsed*
                 ',tree)
               (add-const-to-untranslate-preprocess
                *concrete-syntax-rules-parsed*)
               (defthm treep-of-*concrete-syntax-rules-parsed*
                 (treep *concrete-syntax-rules-parsed*)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *core-rules-parsed-and-abstracted*
  :short "Rule list that @(tsee *core-rules-parsed*) abstracts to."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applying the grammar abstractor to the parse tree
     obtained by applying the grammar parser to the file @('core-rules.abnf'),
     yields a list of rules.
     This shows that the abstractor
     abstracts the parsed definition of the core rules of ABNF
     without errors.")
   (xdoc::p
    "Furthermore, the rule list thus obtained
     is identical @(tsee *core-rules*),
     which is the definition of the concrete syntax of ABNF
     written manually using the abstract syntax of ABNF.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (abstract-rulelist *core-rules-parsed*)
  ///

  (add-const-to-untranslate-preprocess *core-rules-parsed-and-abstracted*)

  (defrule *core-rules-parsed-and-abstracted*-correct
    (equal *core-rules-parsed-and-abstracted* *core-rules*)
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *concrete-syntax-rules-parsed-and-abstracted*
  :short "Rule list that
          @(tsee *concrete-syntax-rules-parsed*) abstracts to."
  :long
  (xdoc::topstring
   (xdoc::p
    "Applying the grammar abstractor to the parse tree
     obtained by applying the grammar parser
     to the file @('concrete-syntax-rules.abnf'),
     yields a list of rules.
     This shows that the abstractor
     abstracts the parsed definition of the concrete syntax of ABNF
     without errors.")
   (xdoc::p
    "Furthermore, the rule list thus obtained
     is identical to @(tsee *concrete-syntax-rules*),
     which is the definition of the concrete syntax of ABNF
     written manually using the abstract syntax of ABNF.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (abstract-rulelist *concrete-syntax-rules-parsed*)
  ///

  (add-const-to-untranslate-preprocess *concrete-syntax-rules-parsed-and-abstracted*)

  (defrule *concrete-syntax-rules-parsed-and-abstracted*-correct
    (equal *concrete-syntax-rules-parsed-and-abstracted*
           *concrete-syntax-rules*)
    :rule-classes nil))
