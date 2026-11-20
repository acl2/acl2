; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book has documentation only.
; It is the one place in this library that names programming languages.

(defxdoc+ unicode-coverage
  :parents (unicode)
  :short "What this library models of the Unicode specifications,
          what it does not model,
          and for which programming languages that is enough."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library models Unicode, not any programming language:
     its definitions and theorems do not refer to one.
     This topic is the exception.
     Its third part lists some programming languages
     and says, for each,
     whether the library has everything of Unicode
     that the lexical rules of the language rely on.")
   (xdoc::p
    "The specifications are cited as in the rest of the library:
     [Unicode] is the core specification of the Unicode Standard,
     [UAX #n] is Unicode Standard Annex number n,
     and UTS #n, below, is Unicode Technical Standard number n.")

   (xdoc::h3 "What is modeled")
   (xdoc::p
    "From [Unicode], Chapters 2 and 3:")
   (xdoc::ul
    (xdoc::li
     "Code points, surrogates and scalar values
      [Unicode, D9, D10, D71, D73, D76]:
      see @(see code-points).")
    (xdoc::li
     "Noncharacters [Unicode, D14]: see @(see noncharacters).")
    (xdoc::li
     "Canonical and compatibility decomposition [Unicode, D65, D68],
      the arithmetic for Hangul syllables [Unicode, Section 3.12],
      canonical ordering [Unicode, D108, D109]
      and canonical composition [Unicode, D113 to D117]:
      see @(see normalization).")
    (xdoc::li
     "Canonical equivalence and compatibility equivalence
      [Unicode, D70, D67]:
      see @(tsee canonical-equivalent-p)
      and @(tsee compatibility-equivalent-p).")
    (xdoc::li
     "The connection of the code points of this library
      to a verified decoder and encoder of UTF-8
      [Unicode, Section 3.9], which is in another library:
      see the book @('utf-8')."))
   (xdoc::p
    "From [UAX #15], Unicode Normalization Forms:")
   (xdoc::ul
    (xdoc::li
     "The four normalization forms, NFD, NFC, NFKD and NFKC,
      as functions and as predicates,
      with the theorems that relate them to each other.
      Each passes the conformance test of every supported version.")
    (xdoc::li
     "The four quick check properties [UAX #15, Section 9],
      and the proof that the quick check is exact
      for the two decomposed forms, NFD and NFKD:
      see @(see quick-check) and @(see quick-check-theorems)."))
   (xdoc::p
    "From [UAX #31], Unicode Identifiers and Syntax:")
   (xdoc::ul
    (xdoc::li
     "The @('XID_Start') and @('XID_Continue') properties
      and the default identifiers that they define,
      with the two optional start characters
      [UAX #31, UAX31-D1, UAX31-R1-1, UAX31-R1-2]:
      see @(see xid).")
    (xdoc::li
     "The closure of those identifiers under the four normalization forms
      [UAX #31, Section 5.1.3]: see @(see identifier-closure).")
    (xdoc::li
     "The @('Pattern_White_Space') and @('Pattern_Syntax') properties:
      see @(see pattern-white-space) and @(see pattern-syntax)."))
   (xdoc::p
    "From [UAX #44], the Unicode Character Database,
     the following properties, each for every supported version:")
   (xdoc::ul
    (xdoc::li
     "@('General_Category') [UAX #44, Table 12]:
      see @(see general-category-property).")
    (xdoc::li
     "@('Canonical_Combining_Class'),
      @('Decomposition_Type') and @('Decomposition_Mapping'),
      @('Full_Composition_Exclusion'),
      and the four quick check properties,
      which are part of @(see normalization) and @(see quick-check).")
    (xdoc::li
     "@('Default_Ignorable_Code_Point'), @('Variation_Selector'),
      @('Join_Control'), @('Noncharacter_Code_Point'),
      @('Deprecated') and @('Prepended_Concatenation_Mark'):
      see @(see default-ignorable), @(see variation-selectors),
      @(see join-controls), @(see noncharacters),
      @(see deprecated) and @(see prepended-concatenation-marks).")
    (xdoc::li
     "@('Bidi_Control'), and the part of @('Bidi_Class')
      that tells the explicit directional formatting characters
      from each other [UAX #9, Sections 2.1 to 2.5]:
      see @(see bidi-controls).")
    (xdoc::li
     "@('XID_Start'), @('XID_Continue'),
      @('Pattern_White_Space') and @('Pattern_Syntax'), as said above."))
   (xdoc::p
    "Relations between these properties
     are proved in @(see property-relations).")

   (xdoc::h3 "What is not modeled")
   (xdoc::p
    "Nothing in this list is in the library.
     A model that needs one of these has to get it elsewhere.")
   (xdoc::ul
    (xdoc::li
     "From [Unicode] and [UAX #44]:
      the names of characters and their aliases;
      case mappings, case folding,
      and the properties @('Lowercase') and @('Uppercase');
      @('Script') and @('Script_Extensions'); @('Block');
      numeric values;
      @('ID_Start') and @('ID_Continue'),
      of which the library has only the variants
      that are closed under normalization,
      namely @('XID_Start') and @('XID_Continue');
      the values of @('Bidi_Class') other than the nine
      of the explicit directional formatting characters;
      paired brackets and mirroring;
      @('Joining_Type') and the other properties
      that describe how characters join;
      and every property that is not named
      under `What is modeled' above.")
    (xdoc::li
     "From [Unicode], Chapter 3:
      the encoding forms UTF-16 and UTF-32.")
    (xdoc::li
     "From [UAX #15]:
      a proof of what the quick check says
      for the two composed forms, NFC and NFKC,
      for which the library has the properties and not the theorem;
      and the Stream-Safe Text Format.")
    (xdoc::li
     "From [UAX #31]:
      the identifiers defined by @('ID_Start') and @('ID_Continue'),
      the profile for mathematical notation,
      and the other profiles and requirements of that annex.")
    (xdoc::li
     "[UAX #9], the bidirectional algorithm:
      the library does not say in which order text is displayed.")
    (xdoc::li
     "[UAX #29], text segmentation:
      grapheme clusters, words and sentences.
      Also [UAX #14], line breaking.")
    (xdoc::li
     "UTS #39, Unicode Security Mechanisms:
      the identifier status and type of a character,
      confusable characters and the skeleton of a string,
      and the detection of mixed scripts.")
    (xdoc::li
     "UTS #51, emoji: the emoji properties and the emoji sequences.")
    (xdoc::li
     "UTS #10, collation; UTS #18, regular expressions;
      UTS #46, compatibility processing of domain names."))

   (xdoc::h3 "Programming languages")
   (xdoc::p
    "For each language below we say what its lexical rules
     take from Unicode, according to the specification named,
     and whether this library models all of it.
     `Sufficient' means that the sets of characters
     that those rules mention can be defined
     from the functions of this library, with nothing added.
     It does not mean that the library has a lexer for the language.
     The specifications were read in November 2026.")
   (xdoc::p
    "An implementation of a language
     uses one version of Unicode.
     The library has the versions listed in @(see versions);
     an implementation that uses an earlier version
     is not covered, whatever properties it uses.")
   (xdoc::ul
    (xdoc::li
     (xdoc::b "C: sufficient.")
     " In C23 [ISO/IEC 9899:2024, Section 6.4.3.1],
      the first character of an identifier
      has @('XID_Start') or is the underscore,
      the other characters have @('XID_Continue'),
      and an identifier must be in Normalization Form C;
      whether the dollar sign is allowed
      is left to the implementation.
      See @(tsee xid-start-p), @(tsee xid-continue-p),
      @(tsee optional-start-p) and @(tsee nfc-memberp).")
    (xdoc::li
     (xdoc::b "Java: sufficient.")
     " The Java Language Specification [Section 3.8]
      defines the characters of identifiers
      by two methods of the class @('Character'),
      which are defined by the general category of a character:
      letters, letter numbers, currency symbols
      and connector punctuation can start an identifier,
      and decimal digits, combining marks
      and certain control and format characters, which are ignored,
      can also be in the rest of it.
      Identifiers are not normalized.
      See @(tsee code-point-general-category).")
    (xdoc::li
     (xdoc::b "Python: sufficient.")
     " In Python 3 [The Python Language Reference, `Lexical analysis'],
      a name starts with a character that has @('XID_Start')
      or with the underscore,
      and continues with characters that have @('XID_Continue');
      names are converted to Normalization Form KC
      and compared in that form.
      See @(tsee xid-start-p), @(tsee xid-continue-p) and @(tsee nfkc).")
    (xdoc::li
     (xdoc::b "Rust: sufficient for the lexer.")
     " In Rust [The Rust Reference, `Identifiers' and `Whitespace'],
      an identifier starts with a character that has @('XID_Start')
      or with the underscore,
      and continues with characters that have @('XID_Continue'),
      except that the two join controls are not allowed;
      identifiers are converted to Normalization Form C
      and compared in that form;
      and white space is the characters
      that have @('Pattern_White_Space').
      See @(tsee xid-start-p), @(tsee xid-continue-p),
      @(tsee join-control-p), @(tsee nfc)
      and @(tsee pattern-white-space-p).
      The warnings of the Rust compiler
      about identifiers that can be confused with each other
      and about identifiers that mix scripts
      rely on UTS #39, which is not modeled.")
    (xdoc::li
     (xdoc::b "Scheme: sufficient.")
     " In Scheme as its sixth revised report defines it
      [R6RS, Section 4.2],
      the characters above U+007F that can be in an identifier,
      and the characters that are white space,
      are defined by lists of general categories.
      Identifiers are not normalized.
      See @(tsee code-point-general-category).")
    (xdoc::li
     (xdoc::b "Remora: not sufficient.")
     " The lexical syntax of Remora,
      as specified in the document
      `Unicode in the lexical syntax of Remora',
      takes from Unicode, among other things,
      the general category, the default ignorable code points,
      the variation selectors, the join controls,
      the bidirectional controls and Normalization Form C,
      which are modeled.
      It also takes the identifier status and type
      and the skeleton of UTS #39,
      the emoji properties of UTS #51,
      the scripts of characters, the whole of @('Bidi_Class'),
      and the names of characters,
      which are not.")))
  :order-subtopics t)
