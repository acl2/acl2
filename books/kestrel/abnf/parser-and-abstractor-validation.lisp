; ABNF -- Parser and Abstractor Validation
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "parser")
(include-book "abstractor")

; (depends-on "core-rules.txt")
; (depends-on "concrete-syntax-rules.txt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-and-abstractor-validation
  :parents (abnf)
  :short "A validation of the parser and abstractor."
  :long
  "<p>
   Running the parser and abstractor
   on the concrete syntax of the core rules and of the concrete syntax rules
   causes no error
   and yields the same abstract syntax
   of the core rules and of the concrete syntax rules
   directly defined in the formalization of the
   <see topic='@(url concrete-syntax)'>concrete syntax</see>.
   This provides a testing validation of the parser and abstractor.
   </p>"
  :order-subtopics t)

(defsection *core-rules-parse-tree*
  :parents (parser-and-abstractor-validation)
  :short "Parse tree of the text that contains the core rules."
  :long
  "<p>
   The file @('core-rules.txt') contains
   the definition of the core rules of ABNF
   using the concrete syntax of ABNF itself,
   copied and pasted from [RFC].
   Calling @(tsee parse-grammar-from-file) on that file yields a parse tree.
   This shows that the executable grammar parser
   parses the core rules of ABNF without errors.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "core-rules.txt") state)
     (value `(progn
               (defconst *core-rules-parse-tree* ',tree)
               (add-const-to-untranslate-preprocess *core-rules-parse-tree*)
               (defthm treep-of-*core-rules-parse-tree*
                 (treep *core-rules-parse-tree*)))))))

(defsection *concrete-syntax-rules-parse-tree*
  :parents (parser-and-abstractor-validation)
  :short "Parse tree of the text that contains
          the concrete syntax rules of ABNF."
  :long
  "<p>
   The file @('concrete-syntax-rules.txt') contains
   the definition of the concrete syntax of ABNF
   using the concrete syntax of ABNF itself,
   copied and pasted from [RFC].
   Calling @(tsee parse-grammar-from-file) on that file yields a parse tree.
   This shows that the executable grammar parser
   parses the definition of the concrete syntax of ABNF without errors.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "concrete-syntax-rules.txt")
                              state)
     (value `(progn
               (defconst *concrete-syntax-rules-parse-tree*
                 ',tree)
               (add-const-to-untranslate-preprocess
                *concrete-syntax-rules-parse-tree*)
               (defthm treep-of-*concrete-syntax-rules-parse-tree*
                 (treep *concrete-syntax-rules-parse-tree*)))))))

(defval *core-rules-abstracted*
  :parents (parser-and-abstractor-validation)
  :short "Rule list that @(tsee *core-rules-parse-tree*) abstracts to."
  :long
  "<p>
   Applying the grammar abstractor to the parse tree
   obtained by applying the grammar parser to the file @('core-rules.txt'),
   yields a list of rules.
   This shows that the abstractor
   abstracts the parsed definition of the core rules of ABNF
   without errors.
   </p>
   <p>
   Furthermore, the rule list thus obtained
   is identical @(tsee *core-rules*),
   which is the definition of the concrete syntax of ABNF
   written manually using the abstract syntax of ABNF.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
  (abstract-rulelist *core-rules-parse-tree*)
  ///

  (add-const-to-untranslate-preprocess *core-rules-abstracted*)

  (defrule *core-rules-abstracted*-correct
    (equal *core-rules-abstracted* *core-rules*)
    :rule-classes nil))

(defval *concrete-syntax-rules-abstracted*
  :parents (parser-and-abstractor-validation)
  :short "Rule list that
          @(tsee *concrete-syntax-rules-parse-tree*) abstracts to."
  :long
  "<p>
   Applying the grammar abstractor to the parse tree
   obtained by applying the grammar parser
   to the file @('concrete-syntax-rules.txt'),
   yields a list of rules.
   This shows that the abstractor
   abstracts the parsed definition of the concrete syntax of ABNF
   without errors.
   </p>
   <p>
   Furthermore, the rule list thus obtained
   is identical to @(tsee *concrete-syntax-rules*),
   which is the definition of the concrete syntax of ABNF
   written manually using the abstract syntax of ABNF.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
  (abstract-rulelist *concrete-syntax-rules-parse-tree*)
  ///

  (add-const-to-untranslate-preprocess *concrete-syntax-rules-abstracted*)

  (defrule *concrete-syntax-rules-abstracted*-correct
    (equal *concrete-syntax-rules-abstracted*
           *concrete-syntax-rules*)
    :rule-classes nil))
