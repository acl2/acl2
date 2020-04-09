; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "grammar")
(include-book "hexadecimal-digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-escapes
  :parents (syntax)
  :short "First Java lexical translation step: Unicode escapes [JLS:3.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java program is a finite sequence of Unicode characters
     satisfying a number of constraints.
     The first set of constraints is described in [JLS:3.3],
     which also describes how
     a sequence of Unicode characters satisfying these constraints
     is turned into another sequence of Unicode characters,
     which is then subjected to
     further constraint checks and associated transformations.")
   (xdoc::p
    "The grammar rules in [JLS:3.3] express
     part of this first set of constraints,
     but they are ambiguous if taken alone:
     one could always choose the @('raw-input-character') alternative
     for @('unicode-input-character'),
     without recognizing any @('unicode-escape'),
     and therefore leave the original Unicode sequence unchanged.
     The English text in [JLS:3.3] provides additional constraints.")
   (xdoc::p
    "One additional constraint in this first set is that,
     in order for a Unicode escape to be recognized
     (i.e. in order for @('unicode-escape') to be chosen),
     the backslash that starts the escape must be preceded
     by an even number of backslashes.
     Without this constraint, it would be impossible, for example,
     to have the Java literal string
     @('\"The Unicode escape \\\\u0020 is the ASCII space character.\"'),
     where the double backslash is
     a (non-Unicode) escape sequence for a single backslash [JLS:3.10.6]:
     without the constraint, this Java literal string would be equivalent to
     @('\"The Unicode escape \\  is the ASCII space character.\"').
     [JLS:3.3] introduces the notion of `eligible' backslash
     as one preceded by an even number of backslashes (possibly none).
     In the example string above,
     the backslash just before the @('u') is not eligible,
     because it is preceded by an odd number of backslashes.")
   (xdoc::p
    "For each eligible backslash, there are two cases:
     either the eligible backslash is followed by one or more @('u') letters,
     or it is not.
     In the second case, there is no Unicode escape,
     because the grammar requires the presence of one or more @('u') letters;
     the backslash must be presumably
     the start of a (non-Unicode) escape sequence [JLS:3.10.6],
     e.g. the backslash in the Java string literal
     @('\"A line.\\nAnother line.\"')
     is eligible,
     but there is no Unicode escape.")
   (xdoc::p
    "If instead an eligible backslash is followed by one or more @('u') letters,
     there are two sub-cases:
     either the last @('u') is followed by four hexadecimal digits,
     or it is not.
     In the second sub-case,
     the original sequence of Unicode characters is not a valid Java program;
     none of the (non-Unicode) escape sequences [JSL:3.10.6]
     has @('u') following the backslash.
     In the first sub-case,
     we have a possible Unicode escape according to the grammar,
     and it must be recognized as such,
     thus removing the inherent grammatical ambiguity.")
   (xdoc::p
    "We formalize the processing of Unicode escapes via a function
     from lists of Unicode characters to lists of Unicode characters
     that recognizes the Unicode escapes according to the above rules
     and turns them into the corresponding single Unicode characters.
     This function is constructed as the composition of
     (i) a parser from lists of Unicode characters
     to lists of @('unicode-input-character') trees
     and (ii) an abstractor from lists of @('unicode-input-character') trees
     to lists of Unicode characters.")
   (xdoc::p
    "The parser always succeeds,
     even if there is an eligible backslash
     followed by one of more @('u') letters
     but with the last @('u') not followed by four hexadecimal digits
     (in which case, as noted above, the processing of Unicode escapes fails).
     In this case, the parser just leaves the characters as they are,
     without recognizing any Unicode escape (since there is not one).
     This makes the parser slightly more general,
     and perhaps useful in other circumstances.
     Presumably [JLS] prescribes an error in this situation
     (as opposed to simply leaving the characters unchanged)
     because the resulting Unicode character sequence
     could never be a valid Java program anyhow,
     and so parsing can stop immediately instead of stopping later anyhow.
     Nonetheless, when we compose the parser with the abstractor (see above),
     we perform the check for that situation,
     and return an error if the situation occurs,
     as prescribed by [JLS].
     In other words, our formalization of Unicode escape processing
     is faithful to [JLS],
     but its parser component is a bit more general."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk even-backslashes-before-p ((pos natp) (unicodes unicode-listp))
  :guard (< pos (len unicodes))
  :returns (yes/no booleanp)
  :short "Check if, in a list of Unicode characters,
          the character at position @('pos') is preceded by
          an even number of backslashes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to define the notion of eligible backslash.")
   (xdoc::p
    "Note that @('(take n (nthcdr (- pos n) unicodes))')
     consists of the characters from position @('(- pos n)') to @('(- pos 1)'),
     both extremes inclusive (positions in lists are zero-based).")
   (xdoc::p
    "Formally, it is not sufficient just to say that
     there are @('n') backslashes just before @('pos') with @('n') even:
     we must also say that there is no backslash just before @('(- pos n)'),
     either because the list starts there (i.e. @('pos') is @('n'))
     or because the character at @('(- (- pos n) 1)') is not a backslash;
     this is expressed by the last conjunct inside the quantification.")
   (xdoc::p
    "This definition works fine if @('n') is 0."))
  (exists (n)
          (and (natp n)
               (evenp n)
               (>= (- pos n) 0)
               (equal (take n (nthcdr (- pos n) unicodes))
                      (repeat n (char-code #\\)))
               (or (equal (- pos n) 0)
                   (not (equal (nth (1- (- pos n)) unicodes)
                               (char-code #\\))))))
  :skolem-name number-of-even-backslashes-before)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eligible-backslash-p ((pos natp) (unicodes unicode-listp))
  :guard (< pos (len unicodes))
  :returns (yes/no booleanp)
  :short "Check if, in a list of Unicode characters,
          the character at position @('pos') is an eligible backslash."
  :long
  (xdoc::topstring-p
   "This is the case when
    the character at @('pos') is a backslash
    and is preceded by an even number of backslashes.")
  (and (equal (nth pos unicodes)
              (char-code #\\))
       (even-backslashes-before-p pos unicodes))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk nonzero-uletters-after-p ((pos natp) (unicodes unicode-listp))
  :guard (< pos (len unicodes))
  :returns (yes/no booleanp)
  :short "Check if, in a list of Unicode characters,
          the character at position @('pos') is followed by
          a non-zero number of `u' letters."
  :long
  (xdoc::topstring
   (xdoc::p
    "In this definition, we want @('n') to be
    not merely a non-zero number of `u' letters
    at positions @('(+ pos 1)') etc.,
    but the maximum such number,
    i.e. such that @('(+ pos n 1)')
    either is past the end of the list
    or is not a `u' letter;
    this is expressed by the last conjunct inside the quantification.
    The witness function returns this number,
    which is used in subsequent definitions.")
   (xdoc::p
    "Note that @('(take n (nthcdr (1+ pos) unicodes))')
     consists of the characters from position @('(+ pos 1)') to @('(+ pos n)'),
     both extremes inclusive (positions in lists are zero-based)."))
  (exists (n)
          (and (posp n)
               (< (+ pos n) (len unicodes))
               (equal (take n (nthcdr (1+ pos) unicodes))
                      (repeat n (char-code #\u)))
               (or (equal (1+ (+ pos n)) (len unicodes))
                   (not (equal (nth (1+ (+ pos n)) unicodes)
                               (char-code #\u))))))
  :skolem-name number-of-nonzero-uletters-after
  ///

  (defrule posp-of-nonzero-uletters-number
    (implies (nonzero-uletters-after-p pos unicodes)
             (posp (number-of-nonzero-uletters-after pos unicodes)))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescape-candidate-p ((pos natp) (unicodes unicode-listp))
  :guard (< pos (len unicodes))
  :returns (yes/no booleanp)
  :short "Check if, in a list of Unicode characters,
          a Unicode escape may start at position @('pos')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion is not explicitly defined in [JLS:3.3],
     but it is useful for our formalization.
     A candidate position for (the start of) a Unicode escape
     is the position of an eligible backslash
     followed by a non-zero number of `u' letters.")
   (xdoc::p
    "When there is such a candidate position in a list of Unicode characters,
     either the candidate is an actual Unicode escape,
     or the list of Unicode characters is invalid.
     This is defined subsequently."))
  (and (eligible-backslash-p pos unicodes)
       (nonzero-uletters-after-p pos unicodes))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescape-candidate-valid-p ((pos natp) (unicodes unicode-listp))
  :guard (and (< pos (len unicodes))
              (uniescape-candidate-p pos unicodes))
  :returns (yes/no booleanp)
  :short "Check if a candidate Unicode escape is valid."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the candidate is an actual Unicode escape.
     This is the case when there are four hexadecimal digits
     just after the last `u' letter.")
   (xdoc::p
    "Here we use the fact that the witness of @(tsee nonzero-uletters-after-p)
     returns the total number @('n') of `u' letters:
     the hexadecimal digits must be at positions
     @('(+ pos n 1)'),
     @('(+ pos n 2)'),
     @('(+ pos n 3)'), and
     @('(+ pos n 4)')."))
  (b* ((n-uletters (number-of-nonzero-uletters-after pos unicodes))
       (pos-hex (+ pos 1 n-uletters)))
    (and (<= (+ pos-hex 4) (len unicodes))
         (hex-digitp (nth pos-hex unicodes))
         (hex-digitp (nth (+ pos-hex 1) unicodes))
         (hex-digitp (nth (+ pos-hex 2) unicodes))
         (hex-digitp (nth (+ pos-hex 3) unicodes))))
  :guard-hints (("Goal" :in-theory (enable uniescape-candidate-p)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescapep ((pos natp) (unicodes unicode-listp))
  :guard (< pos (len unicodes))
  :returns (yes/no booleanp)
  :short "Check if, in a list of Unicode characters,
          there is a Unicode escape at position @('pos')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is true when
     there is a valid Unicode escape at @('pos'),
     i.e. if there is an eligible backslah at @('pos')
     followed by one or more `u' letters
     that are followed by four hexadecimal digits."))
  (and (uniescape-candidate-p pos unicodes)
       (uniescape-candidate-valid-p pos unicodes))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk some-uniescape-candidate-invalid-p ((unicodes unicode-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of Unicode characters includes
          an invalid Unicode escape candidate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to formalize when the list of Unicode characters
     does not satisfy the constraints related to Unicode escapes,
     i.e. the whole sequence of Unicode characters is not a valid Java program
     right at the first lexical translation step.")
   (xdoc::p
    "This is the case when
     there is at least one candidate Unicode escape that is invalid.
     That is, there is an eligible backslash
     followed by one or more `u' letters
     that are not followed by four hexadecimal digits."))
  (exists (pos)
          (and (integer-range-p 0 (len unicodes) pos)
               (uniescape-candidate-p pos unicodes)
               (not (uniescape-candidate-valid-p pos unicodes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicode-input-character-tree-is-escape-p
  ((tree (abnf-tree-with-root-p tree "unicode-input-character")))
  :returns (yes/no booleanp)
  :short "Check if a @('unicode-input-character') tree
          is a Unicode escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the (only) subtree of the tree
     is a @('unicode-escape') tree."))
  (abnf-tree-with-root-p (caar (abnf::tree-nonleaf->branches tree))
                         "unicode-escape")
  :guard-hints (("Goal"
                 :in-theory (enable abnf-tree-with-root-p
                                    abnf::tree-terminatedp)
                 :expand ((:free (element) (abnf::tree-match-element-p
                                            tree element *grammar*)))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection len-of-string-of-prefix-of-unicode-input-character-trees
  :short "A theorem about the length of the string of
          a (proper) prefix of a list of @('unicode-input-character') trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string at the leaves of a @('unicode-input-character') tree
     is never empty.
     Consequently, the string at the leaves of a non-empty list of such trees
     is never empty.
     Therefore, the string at the leaves of a proper prefix of such a list
     is strictly shorter than the string at the leaves of the tree list.")
   (xdoc::p
    "This inequality is used to verify some guards in subsequent functions.")
   (xdoc::p
    "The @(':use') hint in the final theorem serves to
     decompose @('trees') into @('(append (take i trees) (nthcdr i trees))'),
     which turns, via rewriting, the length of the string of @('trees')
     into the sum of the lengths of the strings of
     the prefix (the @(tsee take)) and suffix (the @(tsee nthcdr)).
     Then the type prescription rule aboout the string of the suffix
     tells us that the second addend is non-zero,
     and therefore the first addend (the length of the prefix)
     must be less than the total length."))

  (defrule nonempty-string-of-unicode-input-character-tree
    (implies (abnf-tree-with-root-p tree "unicode-input-character")
             (consp (abnf::tree->string tree)))
    :rule-classes :type-prescription
    :expand ((:free (element)
              (abnf::tree-match-element-p tree element *grammar*))
             (:free (element)
              (abnf::tree-match-element-p (caar (caddr tree))
                                          element
                                          *grammar*)))
    :enable (abnf-tree-with-root-p
             abnf::tree-match-element-p
             abnf::tree-list-match-repetition-p-of-1-repetition
             abnf::tree-match-num-val-p
             abnf::tree-match-char-val-p
             abnf::nat-match-sensitive-char-p
             abnf::tree->string
             abnf::tree-list->string
             abnf::tree-list-list->string
             abnf::treep
             abnf::tree-listp
             abnf::tree-list-listp
             abnf::tree-terminatedp
             abnf::tree-list-terminatedp
             abnf::tree-list-list-terminatedp
             abnf::tree-kind
             abnf::tree-nonleaf->rulename?
             abnf::tree-nonleaf->branches
             abnf::tree-leafterm->get
             acl2::equal-len-const)
    :prep-books
    ((include-book "kestrel/utilities/lists/len-const-theorems" :dir :system)))

  (defrule nonempty-string-of-unicode-input-character-trees
    (implies (and (abnf-tree-list-with-root-p trees "unicode-input-character")
                  (consp trees))
             (consp (abnf::tree-list->string trees)))
    :rule-classes :type-prescription
    :enable abnf-tree-list-with-root-p)

  (defrule nonempty-string-of-unicode-input-character-tree-nonempty-suffix
    (implies (and (abnf-tree-list-with-root-p trees "unicode-input-character")
                  (integer-range-p 0 (len trees) i))
             (consp (abnf::tree-list->string (nthcdr i trees))))
    :rule-classes :type-prescription)

  (defrule len-of-abnf-tree-list-string-of-take-less-when-index-less
    (implies (and (integer-range-p 0 (len trees) i)
                  (abnf-tree-list-with-root-p trees "unicode-input-character"))
             (< (len (abnf::tree-list->string (take i trees)))
                (len (abnf::tree-list->string trees))))
    :rule-classes :linear
    :use (:instance acl2::append-of-take-and-nthcdr (n i) (x trees))
    :disable acl2::append-of-take-and-nthcdr
    :cases ((consp (abnf::tree-list->string (nthcdr i trees))))
    :prep-books ((include-book "std/lists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk even-backslashes-tree-constraints-p
  ((trees (abnf-tree-list-with-root-p trees "unicode-input-character")))
  :returns (yes/no booleanp)
  :short "Necessary condition for parsed trees to be Unicode escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to constrain the result of
     the declaratively defined parser for Unicode escapes.
     The parser maps a list of Unicode characters to
     a list of @('unicode-input-character') trees
     (when successful),
     such that the string at the leaves of the output trees
     is the input Unicode character list
     (this is the constraint expressed by the grammar alone),
     and such that some additional constrains are satisfied.
     This predicates expresses one such additional constraint, namely that
     if the (only) subtree of any parsed tree is a @('unicode-escape') tree
     (i.e. if a Unicode escape is parsed),
     then the backslash that starts the Unicode escape must be eligible,
     i.e. preceded by an even number of backslashes in the character list.")
   (xdoc::p
    "Since, as mentioned above, the input of the parser
     is the string at the leaves of the trees
     (as stated in subsequent predicates),
     this predicate only takes a list of trees as argument:
     the Unicode character list can be derived from the list of trees.")
   (xdoc::p
    "Note that we do not need to use @(tsee uniescapep) here,
     because the implicit grammar constraint,
     namely that the string at the leaves of the tree is the parser input,
     captures most of @(tsee uniescapep),
     except for the requirement on preceding backslashes."))
  (forall (i)
          (implies
           (and (integer-range-p 0 (len trees) i)
                (unicode-input-character-tree-is-escape-p (nth i trees)))
           (even-backslashes-before-p
            (len (abnf::tree-list->string (take i trees)))
            (abnf::tree-list->string trees)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk uniescape-tree-constraints-p
  ((trees (abnf-tree-list-with-root-p trees "unicode-input-character")))
  :returns (yes/no booleanp)
  :short "Sufficient condition for parsed trees to be Unicode escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the discussion in @(tsee even-backslashes-tree-constraints-p)
     regarding the declarative definition of the Unicode escape parser.
     This predicate captures another constraint,
     besides the grammar constraint:
     namely, that if there is a Unicode escape
     at some position in the Unicode character list
     (the string at the leaves of the tree),
     then the corresponding tree must be of a Unicode escape,
     i.e. its (only) subtree must be a @('unicode-escape') tree.")
   (xdoc::p
    "Note that the position in question is expressed not directly,
     but indirectly via an index in the list of trees.
     There is no ``loss'' in doing that,
     because the string has to be decomposed into trees
     according to the grammar anyhow."))
  (forall (i)
          (implies
           (and (integer-range-p 0 (len trees) i)
                (uniescapep (len (abnf::tree-list->string (take i trees)))
                            (abnf::tree-list->string trees)))
           (unicode-input-character-tree-is-escape-p (nth i trees)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescape-parse-constraints-p
  ((unicodes unicode-listp)
   (trees (abnf-tree-list-with-root-p trees "unicode-input-character")))
  :returns (yes/no booleanp)
  :short "All the input/output constraints for the Unicode escape parser."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode escape parser
     takes as input a list of Unicode characters
     and returns as output a list of parsed @('unicode-input-character') trees.
     This predicate characterizes the parser's input/output relationship:
     it says when, given the input,
     the parser is successful, and what the output is.")
   (xdoc::p
    "As motivated in "
    (xdoc::seetopic "unicode-escapes" "the overview")
    ", the parser omits the check that
     @(tsee some-uniescape-candidate-invalid-p) does not hold,
     which does not involve the output anyhow.
     This check in the top-level function
     that formalizes Unicode escape processing,
     of which he parser is a component.")
   (xdoc::p
    "Here we express the constraints of the output with respect to the input.
     The string at the leaves of the trees must be the input string:
     this is the grammatical constraint.
     The other constraints are the necessary and sufficient conditions
     for parsed Unicode escape trees:")
   (xdoc::ul
    (xdoc::li
     "Necessary condition:
      if a tree is a parsed Unicode escape,
      then there is a Unicode escape in the input
      (where it suffices to say that
      there is an even number of preceding backslashes,
      as explained in @(tsee even-backslashes-tree-constraints-p).")
    (xdoc::li
     "Sufficient condition:
      if there is a Unicode escape in the input,
      there must be a corresponding Unicode escapa tree."))
   (xdoc::p
    "These constraints should uniquely characterize the output
     for every possible input,
     but this remains to be proved formally."))
  (and (equal (abnf::tree-list->string trees) unicodes)
       (even-backslashes-tree-constraints-p trees)
       (uniescape-tree-constraints-p trees))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk uniescape-parse-p ((unicodes unicode-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of Unicode characters
          can be parsed into a list of trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when
     there exists a list of @('unicode-input-character') trees
     that is a valid output of the parser,
     as characterized by @(tsee uniescape-parse-constraints-p).")
   (xdoc::p
    "This should be always the case,
     but it remains to be proved formally.")
   (xdoc::p
    "Note that the witness function returns the parser output."))
  (exists (trees)
          (and (abnf-tree-list-with-root-p trees "unicode-input-character")
               (uniescape-parse-constraints-p unicodes trees)))
  :skolem-name uniescape-parse-witness)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescape-parse ((unicodes unicode-listp))
  :returns (mv (errorp booleanp)
               (trees
                (abnf-tree-list-with-root-p trees "unicode-input-character")
                :hints (("Goal" :in-theory (enable uniescape-parse-p)))))
  :short "Parse the Unicode escapes in a list of Unicode characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This parser is declaratively defined in terms of
     the witness of @(tsee uniescape-parse-p).
     If the list of Unicode characters has a corresponding list of parse trees
     (i.e. such that the input/output constraints are satisified),
     they are returned;
     otherwise the parser fails.
     This parser should never fail, but this remains to be proved formally.")
   (xdoc::p
    "Generally a parser returns a single parse trees,
     but Java's first lexical translation step
     must take place before any further parsing.
     Therefore, it is appropriate for this parser to return
     a list of @('unicode-input-character') trees."))
  (if (uniescape-parse-p unicodes)
      (mv nil (uniescape-parse-witness unicodes))
    (mv t nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-raw-input-character
  ((tree (abnf-tree-with-root-p tree "raw-input-character")))
  :returns (unicode unicodep
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory
                             (enable
                              unicodep
                              abnf-tree-with-root-p
                              abnf::tree-terminatedp
                              abnf::tree-list-match-repetition-p-of-1-repetition
                              abnf::tree-match-element-p
                              abnf::tree-match-num-val-p)
                             :expand ((:free (element)
                                       (abnf::tree-match-element-p
                                        tree element *grammar*))))))
  :short "Abstract a @('raw-input-character') tree to a Unicode character."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('raw-input-character) tree is essentially a single Unicode character,
     which is unchanged by Java's first lexical translation step.
     In other words, we abstract this kind of tree
     to its single Unicode character.")
   (xdoc::p
    "A @('raw-input-character') has a single subtree,
     accessible via @(tsee caar).
     That subtree is a terminal leaf tree
     with a single terminal (natural number)
     in the range of Java Unicode characters.
     That is the result."))
  (b* ((subtree (caar (abnf::tree-nonleaf->branches tree)))
       (string (abnf::tree-leafterm->get subtree)))
    (car string))
  :guard-hints (("Goal"
                 :in-theory (enable
                             abnf-tree-with-root-p
                             abnf::tree-terminatedp
                             abnf::tree-list-match-repetition-p-of-1-repetition
                             abnf::tree-match-element-p
                             abnf::tree-match-num-val-p)
                 :expand ((:free (element) (abnf::tree-match-element-p
                                            tree element *grammar*)))))
  :prepwork ((local (include-book "std/typed-lists/nat-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-hex-digit ((tree (abnf-tree-with-root-p tree "hex-digit")))
  :returns (val natp)
  :short "Abstract a @('hex-digit') tree to a natural number below 16."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('hex-digit') tree is essentially a single
     hexadecimal digit Unicode character,
     which denotes a natural number below 16.
     We abstract this kind of tree to the denoted value.")
   (xdoc::p
    "A @('hex-digit') tree has a single subtree,
     accessible via @(tsee caar).
     That subtree is a terminal leaf tree
     with a single terminal (natural number)
     that is the ASCII/Unicode code of a hexadecimal digit,
     which we map to the value it denotes via @(tsee hex-digit-value)."))
  (b* ((subtree (caar (abnf::tree-nonleaf->branches tree)))
       (string (abnf::tree->string subtree))
       (hexdig (car string)))
    (hex-digit-value hexdig))
  :guard-hints (("Goal"
                 :in-theory (enable
                             abnf-tree-with-root-p
                             abnf::tree-terminatedp
                             abnf::tree-list-match-repetition-p-of-1-repetition
                             abnf::tree-match-element-p
                             abnf::tree-match-char-val-p
                             abnf::nat-match-insensitive-char-p
                             abnf::tree->string
                             hex-digitp)
                 :expand ((:free (element) (abnf::tree-match-element-p
                                            tree element *grammar*)))))
  ///

  (defret abs-hex-digit-upper-bound
    (<= val 15)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unicode-escape
  ((tree (abnf-tree-with-root-p tree "unicode-escape")))
  :returns (unicode unicodep
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory
                             (enable
                              unicodep
                              abnf-tree-with-root-p
                              abnf::tree-terminatedp
                              abnf::tree-list-match-repetition-p-of-1-repetition
                              abnf::tree-match-element-p
                              abnf::tree-match-num-val-p)
                             :expand ((:free (element)
                                       (abnf::tree-match-element-p
                                        tree element *grammar*))))))
  :short "Abstract a @('unicode-escape') tree to a Unicode character."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('unicode-escape') tree consists of a Unicode escape,
     which is essentially a number represented via
     four hexadecimal digit characters.
     We abstract this kind of tree
     to the Unicode character whose code is the number
     represented by the four hexadecimal digits, in big-endian order.")
   (xdoc::p
    "A @('unicode-escape') tree has six subtrees,
     for the backslash, the `u' letter, and the four hexadecimal digits.
     We obtain the @('hex-digit') subtrees (ignoring the other two subtrees),
     abstract them to four natural numbers below 16,
     and combine them in big-endian order."))
  (b* ((subtrees (abnf::tree-nonleaf->branches tree))
       (subtree1 (car (third subtrees)))
       (subtree2 (car (fourth subtrees)))
       (subtree3 (car (fifth subtrees)))
       (subtree4 (car (sixth subtrees)))
       (val1 (abs-hex-digit subtree1))
       (val2 (abs-hex-digit subtree2))
       (val3 (abs-hex-digit subtree3))
       (val4 (abs-hex-digit subtree4)))
    (+ (ash val1 12)
       (ash val2 8)
       (ash val3 4)
       val4))
  :guard-hints (("Goal"
                 :in-theory (enable
                             abnf-tree-with-root-p
                             abnf::tree-terminatedp
                             abnf::tree-list-match-repetition-p-of-1-repetition)
                 :expand ((:free (element) (abnf::tree-match-element-p
                                            tree element *grammar*)))))
  :prepwork ((local (include-book "arithmetic/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unicode-input-character
  ((tree (abnf-tree-with-root-p tree "unicode-input-character")))
  :returns (unicode unicodep
                    :hyp :guard
                    :hints (("Goal"
                             :in-theory
                             (enable
                              abnf-tree-with-root-p
                              abnf::tree-list-match-repetition-p-of-1-repetition
                              abnf::tree-terminatedp)
                             :expand ((:free (element)
                                       (abnf::tree-match-element-p
                                        tree element *grammar*))))))
  :short "Abstract a @('unicode-input-character') tree to a Unicode character."
  :long
  (xdoc::topstring
   (xdoc::p
    "Whether the tree is a raw character or a Unicode escape,
     it always denotes a single Unicode character,
     which we abstract this kind of trees to.")
   (xdoc::p
    "A @('unicode-input-character') tree has a single subtree,
     accessible via @(tsee caar).
     This subtree is either a @('unicode-escape') tree
     or a @('raw-input-character') tree."))
  (b* ((subtree (caar (abnf::tree-nonleaf->branches tree))))
    (if (abnf-tree-with-root-p subtree "unicode-escape")
        (abs-unicode-escape subtree)
      (abs-raw-input-character subtree)))
  :guard-hints (("Goal"
                 :in-theory (enable
                             abnf-tree-with-root-p
                             abnf::tree-terminatedp
                             abnf::tree-list-match-repetition-p-of-1-repetition)
                 :expand ((:free (element) (abnf::tree-match-element-p
                                            tree element *grammar*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unicode-input-character-list
  ((trees (abnf-tree-list-with-root-p trees "unicode-input-character")))
  :returns (unicodes unicode-listp :hyp :guard)
  :short "Abstract a list of @('unicode-input-character') trees
          to a list of Unicode characters."
  :long
  (xdoc::topstring-p
   "This lifts @(tsee abs-unicode-input-character) to lists.")
  (cond ((endp trees) nil)
        (t (cons (abs-unicode-input-character (car trees))
                 (abs-unicode-input-character-list (cdr trees)))))
  ///

  (defret len-of-abs-unicode-input-character-list
    (equal (len unicodes)
           (len trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniescape-process ((unicodes unicode-listp))
  :returns (mv (errorp booleanp)
               (new-unicodes unicode-listp))
  :short "Perform Java's first lexical translation step."
  :long
  (xdoc::topstring
   (xdoc::p
    "We parse the Unicode characters into trees,
     and then we abstract the trees into Unicode characters.
     We also check that there no invalid Unicode escape candidates,
     returning an error if there are any.")
   (xdoc::p
    "We propagate any errors from the parser,
     even though there should never be any.
     See comments in @(tsee uniescape-parse) about this."))
  (b* (((when (some-uniescape-candidate-invalid-p unicodes)) (mv t nil))
       ((mv errorp trees) (uniescape-parse unicodes))
       ((when errorp) (mv t nil)))
    (mv nil (abs-unicode-input-character-list trees))))
