; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

; (depends-on "grammar/all.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "An ABNF grammar (family) of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the conrete syntax varies slightly based on "
    (xdoc::seetopic "c::versions" "the C version")
    ", we actually define a family of grammars,
     parameterized over the C version.
     The grammar family is defined using the files @('grammar/*.abnf'),
     which contain various components which are parsed into ACL2 representations
     and combined into full grammars parameterized by the versions.
     This parameterization is work in progress:
     currently there is a single grammar file,
     but we plan to split and differentiate it soon.")
   (xdoc::p
    "The ABNF notation can capture well
     the notation described in [C23:6.1].
     Our ABNF grammar rules are as similar as possible to
     the grammar rules in [C17] and [C23], for the standard constructs.
     The GCC constructs are captured based on [GCCM] [GCCL],
     but these documents do not use a grammar notation,
     so the relationship is less direct than for the standard constructs.
     Currently the grammar only mentions GCC extensions,
     but most of them also apply to Clang;
     we plan to assess and explicate the Clang extensions.
     However, we depart from the official syntax
     when needed to fulfill the purpose of our C syntax for tools;
     see @(tsee syntax-for-tools).")
   (xdoc::p
    "[C23] presents a lexical grammar] [C23:A.2]
     and a phrase structure grammar [C23:A.3].
     This is a typical two-level grammar structure for programming languages:
     the first grammar describes how a sequence of characters
     is organized into lexical units (identifiers, constants, etc.),
     and the second grammar describes how the sequence of those lexical units
     is organized into higher-level constructs (expressions, statements, etc.).
     In C, the lexical organization is more complicated than other languages,
     because of preprocessing [C23:A.4] and other features.
     In fact, the complete syntactic (and semantic) processing of code
     is described as consisting of 8 translation phases [C23:5.2.1.2].")
   (xdoc::p
    "We regard our grammar rules as defining three phases:
     one for the lexical organization,
     one for preprocessing (which preserves certain preprocessing constructs),
     and one for a phrase structure that includes some preprocessing constructs.
     The details are in the documentation that accompanies the grammar rules.")
   (xdoc::p
    "Our ABNF grammar rules doe not consider
     the translation of trigraph sequences
     handled in the first phase in [C23:5.2.1.2]
     and the splicing of lines in the second phase in [C23:5.2.1.2].
     These are simple transformations that can be performed
     prior to the language recognition described by our ABNF grammar rules,
     along with UTF-8 decoding of bytes into Unicode scalar values.
     Our ABNF grammar rules do not capture the requirement that
     a non-empty file ends with a new-line character
     (see phase 3 in [C23:5.2.1.2]);
     this can be easily enforced outside the grammar as well;
     furthermore, GCC relaxes that requirement "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html"
                 "[CPPM:1.2]")
    ", so we do that as well, when GCC extensions are enabled,
     or also when Clang extensions are enabled,
     since Clang expressly aims at being compatible with GCC
     (and running Clang confirms that).")
   (xdoc::p
    "Phase 6 in [C23:5.2.1.2] requires that
     adjacent string literals are concatenated.
     This does not affect the lexing of the code,
     since string literals are tokens,
     but the parser needs to accept adjacent string literals.
     In our (phrase structure) grammar, we accommodate this
     by allowing one or more string literals
     where the grammar in [C23] allows one
     (the phrase grammar in [C23] corresponds to translation phase 7,
     which comes after adjacent string literal concatenation in phase 6).")
   (xdoc::p
    "See the documentation comments in the files @('grammar/*.abnf')
     for more specific details about the grammar rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The ABNF grammar represented in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our verified grammar parser and our abstractor
     to turn the grammar in the @('grammar/all.abnf') file
     into an ACL2 representation.")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output.")
   (xdoc::p
    "We show that the grammar is well-formed, closed, and Unicode."))
  :file "grammar/all.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled unicode-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar*
                                 (acl2::integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e acl2::integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar* :prefix cst)
