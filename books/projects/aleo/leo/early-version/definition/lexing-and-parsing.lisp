; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "unicode")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexing-and-parsing
  :parents (concrete-syntax)
  :short "Lexing and parsing of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the requirements for lexing and parsing
     Unicode character sequences to Leo CSTs.")
   (xdoc::p
    "We formalize these requirements for Leo (code) files,
     for Leo input files,
     and for Leo putput files.
     We plan to extend this to cover Leo configuration files.")
   (xdoc::p
    "The lexing specification is common for
     code files, input files, and output files.
     The parsing specification differs between them.")
   (xdoc::p
    "We plan to prove that lexing and parsing are unambiguous."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-lexp ((ucodes unicode-listp) (trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Grammatical lexing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lexical grammar specifies
     how a sequence of Unicode characters
     can be organized into a sequence of lexemes;
     more precisely, into a sequence of lexeme CSTs.
     This is the case when the fringe of the lexeme CSTs
     is the Unicode character sequence.")
   (xdoc::p
    "Given a Unicode character sequence @('ucodes')
     there may be zero or one or more CST sequences
     that satisfy this predicate.
     If there is zero, @('ucodes') is not syntactically valid Leo code.
     If there is one or more,
     @('ucodes') may be syntactically valid Leo code,
     if additional requirements are satisfied.")
   (xdoc::p
    "If for each @('ucodes') there were always at most one @('trees')
     such that this predicate holds,
     the lexical grammar would be unambiguous,
     and lexing requirements would be completely defined by this predicate.
     However, the lexical grammar is ambiguous:
     for example, @('**') could form
     either two @('*') symbol tokens
     or a single @('**') symbol token.
     It is common for lexical grammars of programming languages to be ambiguous,
     and to be disambiguated by extra-grammatical requirements,
     similar to the ones formalized later."))
  (and (abnf-tree-list-with-root-p (abnf::tree-list-fix trees) "lexeme")
       (equal (unicode-list->codepoint-list ucodes)
              (abnf::tree-list->string trees)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define longest-lexp ((trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Longest lexeme rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some ambiguities in the lexical grammar arise
     because some lexemes are concatenations of others.
     In the example in @(tsee grammar-lexp),
     @('**') is the concatenation of @('*') and @('*').")
   (xdoc::p
    "These ambiguities are eliminated
     by imposing the extra-grammatical requirement that
     lexing always take the longest possible sequence of characters
     that may constitute a lexeme,
     regardless of what follows.
     In particular, this requirement applies even when
     taking the longest sequence of characters causes
     subsequent lexing and parsing to fail,
     whereas taking a shorter sequence would let
     subsequent lexing and parsing succeed.
     For example, @('functionf') is lexed as
     the single identifier @('functionf')
     even though lexing it as
     the keyword @('function')
     followed by the identifier @('f')
     may cause the rest of the code to be successfully lexed and parsed.")
   (xdoc::p
    "This longest lexeme rule is formalized by this predicate,
     which applies to the CST sequence @('trees')
     that @(tsee grammar-lexp) relates to Unicode character sequence.
     This predicate says that,
     for each CST @('tree') in @('trees') except the last one,
     there must exist no other CST @('tree1') for a lexeme whose fringe
     (i) properly extends the fringe of @('tree')
     (i.e. the latter is a prefix of the former, and they are not equal)
     and (ii) is a prefix of the fringe of @('tree') and subsequent CSTs.
     In other words,
     after lexing the fringe of the CSTs that precede @('tree') in @('trees'),
     @('tree') is the CST for the longest possible lexeme
     starting at the fringe of @('tree') and subsequent CSTs:
     there is no other possible CST at that point for a longer lexeme.")
   (xdoc::p
    "Given a Unicode character sequence @('ucodes'),
     if we restrict the CST sequence @('trees')
     for which @(tsee grammar-lexp) holds
     to additionally satisfy @('longest-lexp'),
     lexing is still ambiguous.
     There is some overlap between the grammatical definitions of
     keywords, boolean literals, address literals, and identifiers.
     Even though the rule for @('identifier')
     include an ABNF comment indicating the exclusion of
     keywords
     and boolean literals
     and anything equal to or starting with @('aleo1'),
     the actual ABNF definitions allow that:
     grammatically, a keyword is also an identifier,
     a boolean literal is also an identifier,
     and an identifier may be or start with @('aleo1')."))
  (or (endp trees)
      (endp (cdr trees))
      (and  (not (exist-longer-lexeme-p (car trees) trees))
            (longest-lexp (cdr trees))))
  :hooks (:fix)

  :prepwork
  ((define-sk exist-longer-lexeme-p ((tree abnf::treep)
                                     (trees abnf::tree-listp))
     :returns (yes/no booleanp)
     :parents nil
     (exists (tree1)
             (and (abnf-tree-with-root-p tree1 "lexeme")
                  (prefixp (abnf::tree->string tree)
                           (abnf::tree->string tree1))
                  (not (equal (abnf::tree->string tree)
                              (abnf::tree->string tree1)))
                  (prefixp (abnf::tree->string tree1)
                           (abnf::tree-list->string trees))))
     ///
     (fty::deffixequiv-sk exist-longer-lexeme-p
       :args ((tree abnf::treep) (trees abnf::tree-listp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines identifier-lexp
  :short "Lexing of Identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ambiguity, mentioned in @(tsee longest-lexp),
     deriving from the fact that, grammatically,
     keywords and boolean literals are also identifiers,
     and that identifiers may be or start with @('aleo1'),
     is eliminated by imposing the extra-grammatical requirement
     that identifiers are not keywords or boolean literals
     and are not and do not start with @('aleo1').
     This is formalized by this predicate,
     which holds on ((sequences of) sequences of) CSTs
     that are not, and do not contain any,
     identifier CSTs whose fringe is the same as
     the CST of some keyword or boolean literal,
     or has @('aleo1') as prefix."))

  (define identifier-lexp ((tree abnf::treep))
    :returns (yes/no booleanp)
    (abnf::tree-case
     tree
     :leafterm t
     :leafrule nil ; never happens
     :nonleaf (if (equal tree.rulename? (abnf::rulename "identifier"))
                  (and (not (identifier-or-boolean-fringe-p tree))
                       (not (prefixp (string=>nats "aleo1")
                                     (abnf::tree->string tree))))
                (identifier-lexp-list-list tree.branches)))
    :measure (abnf::tree-count tree))

  (define identifier-lexp-list ((trees abnf::tree-listp))
    :returns (yes/no booleanp)
    (or (endp trees)
        (and (identifier-lexp (car trees))
             (identifier-lexp-list (cdr trees))))
    :measure (abnf::tree-list-count trees))

  (define identifier-lexp-list-list ((treess abnf::tree-list-listp))
    :returns (yes/no booleanp)
    (or (endp treess)
        (and (identifier-lexp-list (car treess))
             (identifier-lexp-list-list (cdr treess))))
    :measure (abnf::tree-list-list-count treess))

  :prepwork
  ((define-sk identifier-or-boolean-fringe-p ((tree abnf::treep))
     :returns (yes/no booleanp)
     :parents nil
     (exists (tree1)
             (and (or (abnf-tree-with-root-p tree1 "keyword")
                      (abnf-tree-with-root-p tree1 "boolean-literal"))
                  (equal (abnf::tree->string tree1)
                         (abnf::tree->string tree))))
     ///
     (fty::deffixequiv-sk identifier-or-boolean-fringe-p
       :args ((tree abnf::treep)))))

  ///

  (fty::deffixequiv-mutual identifier-lexp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexp ((ucodes unicode-listp) (trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :short "Declarative specification of lexing."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sequence of Unicode characters
     can be lexed to a sequence of lexeme CSTs
     iff
     the fringe of the CST sequence is the Unicode sequence,
     the longest lexeme rule holds,
     and identifiers are lexed correctly.
     There should be at most one CST sequence satisfying these requirements,
     but this remains to be formally proved."))
  (and (grammar-lexp ucodes trees)
       (longest-lexp trees)
       (identifier-lexp-list trees))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define filter-tokens ((trees abnf::tree-listp))
  :returns (token-trees abnf::tree-listp)
  :short "Token filtering."
  :long
  (xdoc::topstring
   (xdoc::p
    "As formalized in @(tsee lexp),
     lexing organizes a Unicode character sequence into a sequence of lexemes.
     Comments and whitespace are discarded for parsing,
     which only applies to tokens.
     This process of discarding comments and whitespace
     is formalized via this function,
     which goes through a sequence of CSTs
     and only retains the ones for tokens.")
   (xdoc::p
    "We ignore any CST that is not a lexeme,
     but this never happens for a list of lexeme CSTs.
     We could strengthen the guard of this function
     to require lexeme CSTs."))
  (b* (((when (endp trees)) nil)
       (tree (car trees))
       ((unless (and (abnf::tree-case tree :nonleaf)
                     (equal (abnf::tree-nonleaf->rulename? tree)
                            (abnf::rulename "lexeme"))))
        (filter-tokens (cdr trees))) ; ignore the CST if not a lexeme
       (tree (caar (abnf::tree-nonleaf->branches tree))))
    (if (abnf-tree-with-root-p tree "token")
        (cons tree (filter-tokens (cdr trees)))
      (filter-tokens (cdr trees))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk keyword-abnf-stringp ((string nat-listp))
  :returns (yes/no booleanp)
  :short "Check if an ABNF string (i.e. a list of natural numbers)
          is the fringe of a tree for a keyword."
  (exists (tree)
          (and (abnf-tree-with-root-p tree "keyword")
               (equal (nat-list-fix string)
                      (abnf::tree->string tree))))
  ///

  (defrule treep-of-keyword-abnf-stringp-witness
    (implies (keyword-abnf-stringp string)
             (abnf::treep (keyword-abnf-stringp-witness string))))

  (fty::deffixequiv-sk keyword-abnf-stringp :args ((string nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk symbol-abnf-stringp ((string nat-listp))
  :returns (yes/no booleanp)
  :short "Check if an ABNF string (i.e. a list of natural numbers)
          is the fringe of a tree for a symbol."
  (exists (tree)
          (and (abnf-tree-with-root-p tree "symbol")
               (equal (nat-list-fix string)
                      (abnf::tree->string tree))))
  ///

  (defrule treep-of-symbol-abnf-stringp-witness
    (implies (symbol-abnf-stringp string)
             (abnf::treep (symbol-abnf-stringp-witness string))))

  (fty::deffixequiv-sk symbol-abnf-stringp :args ((string nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk identifier-abnf-stringp ((string nat-listp))
  :returns (yes/no booleanp)
  :short "Check if an ABNF string (i.e. a list of natural numbers)
          is the fringe of a tree for an identifier."
  (exists (tree)
          (and (abnf-tree-with-root-p tree "identifier")
               (identifier-lexp tree)
               (equal (nat-list-fix string)
                      (abnf::tree->string tree))))
  ///

  (defrule treep-of-identifier-abnf-stringp-witness
    (implies (identifier-abnf-stringp string)
             (abnf::treep (identifier-abnf-stringp-witness string))))

  (fty::deffixequiv-sk identifier-abnf-stringp :args ((string nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines token-fringe
  :short "Token fringe."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parsing organizes the sequence of tokens resulting from lexing
     into expressions, statements, etc.
     It would be thus natural to define the parsing of a Leo file
     via a parsing predicate that, analogously to @(tsee grammar-lexp),
     relates a sequence of token CSTs to a file CST
     by saying that the sequence of token CSTs
     is at the fringe of the file CST.")
   (xdoc::p
    "However, the function @(tsee abnf::tree->string)
     returns a sequence of naturals, not a sequence of token CSTs.
     Thus, we need to define a function that returns
     the sequence of token CSTs at the fringe of a CST;
     this could be defined similarly to @(tsee abnf::tree->string),
     but stopping the recursion when a token tree is encountered,
     instead of stopping the recursion when a leaf tree is encountered.")
   (xdoc::p
    "But this function cannot be defined exactly as described,
     because token CSTs do not actually appear in file CSTs.
     Instead, a file CST has subtrees of token CST,
     such as identifier CSTs;
     the reason should be clear looking at the syntactic grammar,
     which never references @('token') directly,
     but rather @('identifier') and other kinds of tokens.
     This means that the function must stop the recursion
     at these CSTs instead,
     and must also complete them to be token CSTs.")
   (xdoc::p
    "The following function, and its mutually recursive companions,
     formalizes the token fringe of a CST in the sense explained above:")
   (xdoc::ul
    (xdoc::li
     "A leaf CST that is a sequence of naturals
      that are a possible fringe of a keyword CST
      (i.e. a Unicode character sequence forming a keyword)
      yields the singleton sequence of the token CST
      whose subtree is the keyword subtree
      whose subtree is the original leaf CST.")
    (xdoc::li
     "A leaf CST that is a sequence of naturals
      that are a possible fringe of a symbol CST
      (i.e. a Unicode character sequence forming a symbol)
      yields the singleton sequence of the token CST
      whose subtree is the symbol subtree
      whose subtree is the initial leaf CST.")
    (xdoc::li
     "A leaf CST that is a sequence of naturals
      that are a possible fringe of an identifier CST
      (i.e. a Unicode character sequence forming an identifier)
      among a list explicitly passed to this ACL2 function
      yields the singleton sequence of the token CST
      whose subtree is the identifier subtree
      whose subtree is the original leaf CST.")
    (xdoc::li
     "For any other leaf CST,
      that is either a sequence of naturals or a rule name,
      we return @('nil'),
      but this never happens in the course of a recursion
      that starts with a file CST.")
    (xdoc::li
     "An identifier or atomic literal or numeral CST yields
      a singleton sequence of the token CST
      whose subtree is the original CST.")
    (xdoc::li
     "Any other CST yields the token fringe of its subtrees
      (the recursion does not stop at the CST).")
    (xdoc::li
     "The token fringe of a list of CSTs is
      the concatenation of the token fringes of the CSTs.")
    (xdoc::li
     "The token fringe of a list of lists of CSTs is
      the concatenation of the token fringes of the CST lists."))
   (xdoc::p
    "Note that the special treatment, explained above,
     of leaf CSTs whose strings are identifiers
     (when the list of identifiers is not empty)
     does not affect the treatment of identifier CSTs,
     which are not leaf CSTs.
     For concrete motivations for this special treatment,
     see @(tsee input-file-parsep) and @(tsee output-file-parsep)."))

  (define token-fringe ((tree abnf::treep)
                        (identifiers string-listp))
    :returns (token-trees abnf::tree-listp)
    (abnf::tree-case
     tree
     :leafterm
     (cond ((keyword-abnf-stringp tree.get)
            (list
             (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "token")
              :branches (list
                         (list
                          (keyword-abnf-stringp-witness tree.get))))))
           ((symbol-abnf-stringp tree.get)
            (list
             (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "token")
              :branches (list
                         (list
                          (symbol-abnf-stringp-witness tree.get))))))
           ((and (identifier-abnf-stringp tree.get)
                 (unsigned-byte-listp 8 tree.get)
                 (member-equal (nats=>string tree.get)
                               (str::string-list-fix identifiers)))
            (list
             (abnf::make-tree-nonleaf
              :rulename? (abnf::rulename "token")
              :branches (list
                         (list
                          (identifier-abnf-stringp-witness tree.get))))))
           (t nil)) ; never happens
     :leafrule nil ; never happens
     :nonleaf
     (cond ((or (equal tree.rulename? (abnf::rulename "identifier"))
                (equal tree.rulename? (abnf::rulename "atomic-literal"))
                (equal tree.rulename? (abnf::rulename "numeral")))
            (list (abnf::make-tree-nonleaf
                   :rulename? (abnf::rulename "token")
                   :branches (list (list (abnf::tree-fix tree))))))
           (t (token-fringe-list-list tree.branches identifiers))))
    :measure (abnf::tree-count tree))

  (define token-fringe-list ((trees abnf::tree-listp)
                             (identifiers string-listp))
    :returns (token-trees abnf::tree-listp)
    (cond ((endp trees) nil)
          (t (append (token-fringe (car trees) identifiers)
                     (token-fringe-list (cdr trees) identifiers))))
    :measure (abnf::tree-list-count trees))

  (define token-fringe-list-list ((treess abnf::tree-list-listp)
                                  (identifiers string-listp))
    :returns (token-trees abnf::tree-listp)
    (cond ((endp treess) nil)
          (t (append (token-fringe-list (car treess) identifiers)
                     (token-fringe-list-list (cdr treess) identifiers))))
    :measure (abnf::tree-list-list-count treess))

  ///

  (fty::deffixequiv-mutual token-fringe))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-parsep ((tokens abnf::tree-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Parsing of Leo files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relates a list of token CSTs to a CST.
     The predicate holds iff the CST is for a file and
     the list of token CSTs is the token fringe of the file CST."))
  (and (abnf-tree-with-root-p (abnf::tree-fix file) "file")
       (equal (token-fringe file nil)
              (abnf::tree-list-fix tokens)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk file-lex-parse-p ((ucodes unicode-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Lexing and parsing of Leo files."
  :long
  (xdoc::topstring
   (xdoc::p
    "The complete lexing and parsing requirements for Leo files
     are formalized via the following predicate,
     which combines the lexing and parsing predicates defined above.
     It says that the Unicode character sequence @('ucodes')
     is lexed and parsed into a CST @('file') iff
     the characters are lexed into a CST sequence @('lexemes'),
     and the tokens filtered from the latter can be parsed into a @('file').")
   (xdoc::p
    "It should be the case that this lexing and parsing is unambiguous,
     i.e. that for every list of Unicode characters
     there is at most one CST for which the predicate holds;
     but this remains to be formally proved.
     If none exists, the Unicode character list
     does not form a syntactically valid Leo file.
     If one exists, the Unicode character sequence
     forms a syntactically valid Leo file,
     organized according to that CST."))
  (exists (lexemes)
          (and (abnf::tree-listp lexemes)
               (lexp ucodes lexemes)
               (file-parsep (filter-tokens lexemes) file)))
  ///
  (fty::deffixequiv-sk file-lex-parse-p
    :args ((ucodes unicode-listp) (file abnf::treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define input-file-parsep ((tokens abnf::tree-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Parsing of Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee file-parsep),
     but for input files instead of (code) files.")
   (xdoc::p
    "Note also that, while @(tsee file-parsep) passes
     the empty list of identifiers to @(tsee token-fringe),
     here we pass the list consisting of the @('private') identifier.
     This is because this identifier is treated
     a bit like a keyword in the grammar of input files:
     it does not appear as @('identifier') in the grammar,
     but ``directly'' as @('%s\"private\"').
     Therefore, when we calculate the token fringe for a CST of an input file
     we need to turn that into a token identifier
     in order to properly relate it to
     the list of tokens filtered from the list of lexemes."))
  (and (abnf-tree-with-root-p (abnf::tree-fix file) "input-file")
       (equal (token-fringe file (list "private"))
              (abnf::tree-list-fix tokens)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk input-file-lex-parse-p ((ucodes unicode-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Lexing and parsing of Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee file-lex-parse-p),
     but for input files instead of (code) files."))
  (exists (lexemes)
          (and (abnf::tree-listp lexemes)
               (lexp ucodes lexemes)
               (input-file-parsep (filter-tokens lexemes) file)))
  ///
  (fty::deffixequiv-sk input-file-lex-parse-p
    :args ((ucodes unicode-listp) (file abnf::treep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define output-file-parsep ((tokens abnf::tree-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Parsing of Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee file-parsep) and @(tsee input-file-parsep),
     but for output files instead of (code) files and input files.")
   (xdoc::p
    "Note also that, while @(tsee file-parsep) passes
     the empty list of identifiers to @(tsee token-fringe),
     here we pass the list consisting of the @('output') identifier.
     This is because this identifier is treated
     a bit like a keyword in the grammar of output files:
     it does not appear as @('identifier') in the grammar,
     but ``directly'' as @('%s\"output\"').
     Therefore, when we calculate the token fringe for a CST of an input file
     we need to turn that into a token identifier
     in order to properly relate it to
     the list of tokens filtered from the list of lexemes."))
  (and (abnf-tree-with-root-p (abnf::tree-fix file) "output-file")
       (equal (token-fringe file (list "output"))
              (abnf::tree-list-fix tokens)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk output-file-lex-parse-p ((ucodes unicode-listp) (file abnf::treep))
  :returns (yes/no booleanp)
  :short "Lexing and parsing of Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee file-lex-parse-p) and @(tsee input-file-lex-parse-p),
     but for output files instead of (code) files and input files."))
  (exists (lexemes)
          (and (abnf::tree-listp lexemes)
               (lexp ucodes lexemes)
               (output-file-parsep (filter-tokens lexemes) file)))
  ///
  (fty::deffixequiv-sk output-file-lex-parse-p
    :args ((ucodes unicode-listp) (file abnf::treep))))
