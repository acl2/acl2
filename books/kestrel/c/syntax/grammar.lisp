; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../language/implementation-environments/dialects")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "projects/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

(acl2::controlled-configuration)

; (depends-on "grammar/characters.abnf")
; (depends-on "grammar/characters-c17.abnf")
; (depends-on "grammar/characters-c23.abnf")
; (depends-on "grammar/comments.abnf")
; (depends-on "grammar/keywords.abnf")
; (depends-on "grammar/keywords-c17.abnf")
; (depends-on "grammar/keywords-c23.abnf")
; (depends-on "grammar/keywords-c17-noext.abnf")
; (depends-on "grammar/keywords-c17-gcc.abnf")
; (depends-on "grammar/keywords-c17-clang-nocheri.abnf")
; (depends-on "grammar/keywords-c17-clang-cheri.abnf")
; (depends-on "grammar/keywords-c23-noext.abnf")
; (depends-on "grammar/keywords-c23-gcc.abnf")
; (depends-on "grammar/keywords-c23-clang-nocheri.abnf")
; (depends-on "grammar/keywords-c23-clang-cheri.abnf")
; (depends-on "grammar/identifiers.abnf")
; (depends-on "grammar/identifiers-c17.abnf")
; (depends-on "grammar/identifiers-c23.abnf")
; (depends-on "grammar/identifier-lists.abnf")
; (depends-on "grammar/universal-character-names.abnf")
; (depends-on "grammar/integer-constants.abnf")
; (depends-on "grammar/integer-constants-c17.abnf")
; (depends-on "grammar/integer-constants-c23.abnf")
; (depends-on "grammar/floating-constants.abnf")
; (depends-on "grammar/floating-constants-c17.abnf")
; (depends-on "grammar/floating-constants-c23.abnf")
; (depends-on "grammar/floating-constants-c17-nogcc.abnf")
; (depends-on "grammar/floating-constants-c23-nogcc.abnf")
; (depends-on "grammar/floating-constants-c17-gcc.abnf")
; (depends-on "grammar/floating-constants-c23-gcc.abnf")
; (depends-on "grammar/enumeration-constants.abnf")
; (depends-on "grammar/encoding-prefixes.abnf")
; (depends-on "grammar/character-constants.abnf")
; (depends-on "grammar/character-constants-c17.abnf")
; (depends-on "grammar/character-constants-c23.abnf")
; (depends-on "grammar/simple-escapes-std.abnf")
; (depends-on "grammar/simple-escapes-ext.abnf")
; (depends-on "grammar/constants-c17.abnf")
; (depends-on "grammar/constants-c23.abnf")
; (depends-on "grammar/string-literals-c17.abnf")
; (depends-on "grammar/string-literals-c23.abnf")
; (depends-on "grammar/punctuators-c17.abnf")
; (depends-on "grammar/punctuators-c23.abnf")
; (depends-on "grammar/header-names.abnf")
; (depends-on "grammar/preprocessing-numbers-c17.abnf")
; (depends-on "grammar/preprocessing-numbers-c23.abnf")
; (depends-on "grammar/preprocessing-tokens-c17.abnf")
; (depends-on "grammar/preprocessing-tokens-c23.abnf")
; (depends-on "grammar/preprocessing-lexemes.abnf")
; (depends-on "grammar/preprocessing-expressions.abnf")
; (depends-on "grammar/preprocessing-expressions-c17.abnf")
; (depends-on "grammar/preprocessing-expressions-c23.abnf")
; (depends-on "grammar/preprocessing-directives.abnf")
; (depends-on "grammar/preprocessing-directives-c17.abnf")
; (depends-on "grammar/preprocessing-directives-c23.abnf")
; (depends-on "grammar/standard-pragmas.abnf")
; (depends-on "grammar/standard-pragmas-c17.abnf")
; (depends-on "grammar/standard-pragmas-c23.abnf")
; (depends-on "grammar/tokens.abnf")
; (depends-on "grammar/lexemes.abnf")
; (depends-on "grammar/expressions.abnf")
; (depends-on "grammar/expressions-std.abnf")
; (depends-on "grammar/expressions-ext.abnf")
; (depends-on "grammar/grammar-rest.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "An ABNF grammar (family) of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the concrete syntax varies slightly based on "
    (xdoc::seetopic "c::dialects" "the C dialect")
    ", we actually define a family of grammars,
     parameterized over the C dialect.
     The grammar family is defined using the files @('grammar/*.abnf'),
     which contain various components which are parsed into ACL2 representations
     and combined into full grammars parameterized by the dialects.
     This parameterization is work in progress:
     currently we have only some of the needed component files.")
   (xdoc::p
    "[C17:5.2.1] provides requirements on the source character set,
     i.e. the character set used to write the C code,
     but the details of this character set are implementation-dependent;
     see @('[books]/kestrel/c/language/character-sets.lisp')
     for a formalization of the requirements in [C17:5.2.1].
     In particular, [C17:5.2.1] does not prescribe ASCII or Unicode.
     Our grammar assumes Unicode, which is a very general assumption these days;
     other (uncommon) character sets should be also easily encodable in Unicode,
     should our tools ever need to handle such character sets.")
   (xdoc::p
    "The ABNF notation can capture well
     the notation described in [C23:6.1], which is the same in [C17:6.1].
     Our ABNF grammar rules are as similar as possible to
     the grammar rules in [C17] and [C23], for the standard constructs.
     The GCC constructs are captured based on [GCCM] and [GCCL],
     but these documents do not use a grammar notation,
     so the relationship is less direct than for the standard constructs.
     Currently the grammar only mentions GCC extensions,
     but most of them also apply to Clang;
     we plan to assess and explicate the Clang extensions.
     However, we depart from the official syntax
     when needed to fulfill the purpose of our C syntax for tools;
     see @(tsee syntax-for-tools).")
   (xdoc::p
    "[C23] presents a lexical grammar [C23:A.2]
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
    "Our ABNF grammar rules do not consider
     the translation of trigraph sequences
     handled in the first phase in [C17:5.1.1.2]
     (which, incidentally, has been removed in [C23:5.2.1.2]),
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

(defmacro defgrammar (name description)
  (declare (xargs :guard (and (symbolp name) (stringp description))))
  (b* ((const (packn-pos (list '*grammar- name '*) 'grammar))
       (file (str::cat "grammar/"
                       (str::downcase-string (symbol-name name))
                       ".abnf"))
       (short (str::cat "Grammar rules for " description ".")))
    `(abnf::defgrammar ,const
       :short ,short
       :file ,file
       :untranslate t
       :well-formed t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar characters
  "the source character set that are common to all the C dialects")

(defgrammar characters-c17
  "the source character set that are specific to the C17 dialects")

(defgrammar characters-c23
  "the source character set that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar comments "comments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar keywords "keywords that form subsets for the various C dialects")

(defgrammar keywords-c17 "keywords that are specific to the C17 dialects")

(defgrammar keywords-c23 "keywords that are specific to the C23 dialects")

(defgrammar keywords-c17-noext
  "keywords that are specific to the C17 dialect without extensions")

(defgrammar keywords-c23-noext
  "keywords that are specific to the C23 dialect without extensions")

(defgrammar keywords-c17-gcc
  "keywords that are specific to
   the C17 dialect with GCC and without CHERI extensions")

(defgrammar keywords-c23-gcc
  "keywords that are specific to
   the C23 dialect with GCC and without CHERI extensions")

(defgrammar keywords-c17-clang-nocheri
  "keywords that are specific to
   the C17 dialect with Clang and without CHERI extensions")

(defgrammar keywords-c23-clang-nocheri
  "keywords that are specific to
   the C23 dialect with Clang and without CHERI extensions")

(defgrammar keywords-c17-clang-cheri
  "keywords that are specific to
   the C17 dialect with Clang and CHERI extensions")

(defgrammar keywords-c23-clang-cheri
  "keywords that are specific to
   the C23 dialect with Clang and CHERI extensions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar identifiers "identifiers that are common to all the C dialects")

(defgrammar identifiers-c17 "identifiers that are specific to the C17 dialects")

(defgrammar identifiers-c23 "identifiers that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar identifier-lists "lists of identifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar universal-character-names "universal character names")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar integer-constants
  "integer constants that are common to all the C dialects")

(defgrammar integer-constants-c17
  "integer constants that are specific to the C17 dialects")

(defgrammar integer-constants-c23
  "integer constants that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar floating-constants
  "floating constants that are common to all the C dialects")

(defgrammar floating-constants-c17
  "floating constants that are specific to C17 dialects")

(defgrammar floating-constants-c23
  "floating constants that are specific to C23 dialects")

(defgrammar floating-constants-c17-nogcc
  "floating constants that are specific to C17 dialects without GCC extensions")

(defgrammar floating-constants-c23-nogcc
  "floating constants that are specific to C23 dialects without GCC extensions")

(defgrammar floating-constants-c17-gcc
  "floating constants that are specific to C17 dialect with GCC extensions")

(defgrammar floating-constants-c23-gcc
  "floating constants that are specific to C23 dialect with GCC extensions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar enumeration-constants "enumeration constants")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar encoding-prefixes "encoding prefixes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar character-constants
  "character constants that are common to all the C dialects")

(defgrammar character-constants-c17
  "character constants that are specific to the C17 dialects")

(defgrammar character-constants-c23
  "character constants that are specific to the C23 dialects")

(defgrammar simple-escapes-std
  "simple escapes that are specific to
   the dialects without GCC or Clang extensions")

(defgrammar simple-escapes-ext
  "simple escapes that are specific to
   the dialects with GCC or Clang extensions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar constants-c17
  "constants that are specific to the C17 dialects")

(defgrammar constants-c23
  "constants that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar string-literals-c17
  "string literals that are specific to the C17 dialects")

(defgrammar string-literals-c23
  "string literals that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar punctuators-c17
  "punctuators that are specific to the C17 dialects")

(defgrammar punctuators-c23
  "punctuators that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar header-names
  "header names that are specific to the C17 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar preprocessing-numbers-c17
  "preprocessing numbers that are specific to the C17 dialects")

(defgrammar preprocessing-numbers-c23
  "preprocessing numbers that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar preprocessing-tokens-c17
  "preprocessing tokens that are specific to the C17 dialects")

(defgrammar preprocessing-tokens-c23
  "preprocessing tokens that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar preprocessing-lexemes "preprocessing lexemes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar preprocessing-expressions
  "preprocessing expressions that are common to all the C dialects")

(defgrammar preprocessing-expressions-c17
  "preprocessing expressions that are specific to the C17 dialects")

(defgrammar preprocessing-expressions-c23
  "preprocessing expressions that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar preprocessing-directives
  "preprocessing directives that are common to all the C dialects")

(defgrammar preprocessing-directives-c17
  "preprocessing directives that are specific to the C17 dialects")

(defgrammar preprocessing-directives-c23
  "preprocessing directives that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar standard-pragmas
  "standard pragmas that are common to all the C dialects")

(defgrammar standard-pragmas-c17
  "standard pragmas that are specific to the C17 dialects")

(defgrammar standard-pragmas-c23
  "standard pragmas that are specific to the C23 dialects")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar tokens "tokens")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar lexemes "lexemes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar expressions
  "standard pragmas that are common to all the C dialects")

(defgrammar expressions-std
  "standard pragmas that are specific to the standard C dialects")

(defgrammar expressions-ext
  "standard pragmas that are specific to the GCC and Clang extensions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar-rest*
  :short "Rest of the grammar rules."
  :file "grammar/grammar-rest.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-for ((dialect c::dialectp))
  :returns (grammar abnf::rulelistp
                    :hints (("Goal" ; for speed:
                             :in-theory (disable abnf::rulelistp-of-append
                                                 abnf::rulelistp-of-cons))))
  :short "Grammar for a given C dialect."
  (b* (((c::dialect dialect) dialect))
    (append
     ;; characters:
     *grammar-characters*
     (c::standard-case dialect.std
                       :c17 *grammar-characters-c17*
                       :c23 *grammar-characters-c23*)
     ;; comments:
     *grammar-comments*
     ;; keywords:
     *grammar-keywords*
     (c::standard-case
      dialect.std
      :c17 (append *grammar-keywords-c17*
                   (cond (dialect.gcc *grammar-keywords-c17-gcc*)
                         (dialect.clang (if dialect.cheri
                                            *grammar-keywords-c17-clang-cheri*
                                          *grammar-keywords-c17-clang-nocheri*))
                         (t *grammar-keywords-c17-noext*)))
      :c23 (append *grammar-keywords-c23*
                   (cond (dialect.gcc *grammar-keywords-c23-gcc*)
                         (dialect.clang (if dialect.cheri
                                            *grammar-keywords-c23-clang-cheri*
                                          *grammar-keywords-c23-clang-nocheri*))
                         (t *grammar-keywords-c23-noext*))))
     ;; identifiers:
     *grammar-identifiers*
     (c::standard-case dialect.std
                       :c17 *grammar-identifiers-c17*
                       :c23 *grammar-identifiers-c23*)
     ;; identifier lists:
     *grammar-identifier-lists*
     ;; universal character names:
     *grammar-universal-character-names*
     ;; integer constants:
     *grammar-integer-constants*
     (c::standard-case dialect.std
                       :c17 *grammar-integer-constants-c17*
                       :c23 *grammar-integer-constants-c23*)
     ;; floating constants:
     *grammar-floating-constants*
     (c::standard-case
      dialect.std
      :c17 (append *grammar-floating-constants-c17*
                   (if dialect.gcc
                       *grammar-floating-constants-c17-gcc*
                     *grammar-floating-constants-c17-nogcc*))
      :c23 (append *grammar-floating-constants-c23*
                   (if dialect.gcc
                       *grammar-floating-constants-c23-gcc*
                     *grammar-floating-constants-c23-nogcc*)))
     ;; enumeration constants:
     *grammar-enumeration-constants*
     ;; encoding prefixes:
     *grammar-encoding-prefixes*
     ;; character-constants:
     *grammar-character-constants*
     (c::standard-case dialect.std
                       :c17 *grammar-character-constants-c17*
                       :c23 *grammar-character-constants-c23*)
     (if (or dialect.gcc dialect.clang)
         *grammar-simple-escapes-ext*
       *grammar-simple-escapes-std*)
     ;; constants:
     (c::standard-case dialect.std
                       :c17 *grammar-constants-c17*
                       :c23 *grammar-constants-c23*)
     ;; string literals:
     (c::standard-case dialect.std
                       :c17 *grammar-string-literals-c17*
                       :c23 *grammar-string-literals-c23*)
     ;; punctuators:
     (c::standard-case dialect.std
                       :c17 *grammar-punctuators-c17*
                       :c23 *grammar-punctuators-c23*)
     ;; header names:
     *grammar-header-names*
     ;; preprocessing numbers:
     (c::standard-case dialect.std
                       :c17 *grammar-preprocessing-numbers-c17*
                       :c23 *grammar-preprocessing-numbers-c23*)
     ;; preprocessing tokens:
     (c::standard-case dialect.std
                       :c17 *grammar-preprocessing-tokens-c17*
                       :c23 *grammar-preprocessing-tokens-c23*)
     ;; preprocessing lexemes:
     *grammar-preprocessing-lexemes*
     ;; preprocessing expressions:
     *grammar-preprocessing-expressions*
     (c::standard-case dialect.std
                       :c17 *grammar-preprocessing-expressions-c17*
                       :c23 *grammar-preprocessing-expressions-c23*)
     ;; preprocessing directives:
     *grammar-preprocessing-directives*
     (c::standard-case dialect.std
                       :c17 *grammar-preprocessing-directives-c17*
                       :c23 *grammar-preprocessing-directives-c23*)
     ;; standard pragmas:
     *grammar-standard-pragmas*
     (c::standard-case dialect.std
                       :c17 *grammar-standard-pragmas-c17*
                       :c23 *grammar-standard-pragmas-c23*)
     ;; tokens:
     *grammar-tokens*
     ;; lexemes:
     *grammar-lexemes*
     ;; expressions:
     *grammar-expressions*
     (if (or dialect.gcc dialect.clang)
         *grammar-expressions-ext*
       *grammar-expressions-std*)
     ;; rest (TODO: modularize):
     *grammar-rest*))

  ///

  (defruled rulelist-wfp-of-grammar-for
    (abnf::rulelist-wfp (grammar-for dialect))
    :enable abnf::rulelist-wfp)

  (defruled rulelist-closedp-of-grammar-for
    (abnf::rulelist-closedp (grammar-for dialect))
    :enable abnf::rulelist-closedp)

  ;; The next theorem fails with the default 1000 limit.
  ;; It is still fast (about 1.25 seconds on a fast machine),
  ;; even with this higher limit.
  (set-rewrite-stack-limit 2000) ; implicitly local

  (defruled unicode-only-grammar-for
    (abnf::rulelist-in-termset-p (grammar-for dialect)
                                 (acl2::integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e acl2::integers-from-to))))
