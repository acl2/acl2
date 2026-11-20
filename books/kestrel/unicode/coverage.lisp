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
     and [UTS #n] is Unicode Technical Standard number n.")

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
      the proof that the quick check is exact
      for the two decomposed forms, NFD and NFKD,
      and the proof that the code points that NFC and NFKC change
      are those whose quick check value is `no':
      see @(see quick-check) and @(see quick-check-theorems).")
    (xdoc::li
     "A condition for a code point to be stable
      under all four forms [UAX #15, Section 9.1],
      with the theorems that the forms
      normalize separately what is before and what is after such a code point:
      see @(see normalization-inert-code-points).")
    (xdoc::li
     "The Stream-Safe Text Format and the Stream-Safe Text Process
      [UAX #15, Section 13],
      with the proof that the process gives text in that format
      and leaves text in that format unchanged,
      and that the four forms do not change
      whether text is in that format:
      see @(see stream-safe)."))
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
     "The @('ID_Start') and @('ID_Continue') properties,
      with @('Other_ID_Start') and @('Other_ID_Continue'),
      the proof that they are what [UAX #31, Table 2] derives them from,
      and the list of the code points
      in which they differ from @('XID_Start') and @('XID_Continue'):
      see @(see id-properties) and @(see id-relations).")
    (xdoc::li
     "The two properties of the profile for mathematical notation
      [UAX #31, Section 7.1],
      @('ID_Compat_Math_Start') and @('ID_Compat_Math_Continue'):
      see @(see id-compat-math).")
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
     "@('Bidi_Control') and @('Bidi_Class') [UAX #9, Table 4]:
      see @(see bidi-controls), which has the explicit directional
      formatting characters [UAX #9, Sections 2.1 to 2.5],
      and @(see bidi-class-property), which has the whole property.")
    (xdoc::li
     "@('Script') and @('Script_Extensions') [UAX #24]:
      see @(see scripts).")
    (xdoc::li
     "@('Block'): see @(see blocks).")
    (xdoc::li
     "The decimal digits and their values,
      which is the part of @('Numeric_Type') and @('Numeric_Value')
      for the characters whose numeric type is @('Decimal'):
      see @(see decimal-digits).")
    (xdoc::li
     "@('XID_Start'), @('XID_Continue'),
      @('ID_Start'), @('ID_Continue'),
      @('Other_ID_Start'), @('Other_ID_Continue'),
      @('ID_Compat_Math_Start'), @('ID_Compat_Math_Continue'),
      @('Pattern_White_Space') and @('Pattern_Syntax'), as said above;
      and @('Regional_Indicator'), with the emoji properties below."))
   (xdoc::p
    "From [UTS #39], Unicode Security Mechanisms:")
   (xdoc::ul
    (xdoc::li
     "@('Identifier_Status') and @('Identifier_Type')
      [UTS #39, Section 3.1 and Table 1],
      with the proof that the two agree,
      and that Normalization Form KC changes no allowed character:
      see @(see identifier-status), @(see identifier-type-relations)
      and @(see identifier-status-and-normalization).")
    (xdoc::li
     "The prototypes of confusable characters
      and the internal skeleton of a string [UTS #39, Section 4],
      with the proof of when taking the internal skeleton twice
      is the same as taking it once:
      see @(see confusables), @(tsee internal-skeleton)
      and @(see skeleton-idempotence).")
    (xdoc::li
     "The skeleton of a string and the confusable strings
      [UTS #39, Section 4],
      for the strings that have no right-to-left character,
      no Arabic-Indic digit or other character of class @('AN'),
      and no explicit formatting character that starts right-to-left text,
      and the three classes of confusable strings:
      see @(see confusable-detection) and @(see confusable-kinds).")
    (xdoc::li
     "Mixed-script detection [UTS #39, Section 5.1]:
      augmented script sets, resolved script sets,
      and single-script and mixed-script strings:
      see @(see mixed-script-detection).")
    (xdoc::li
     "Mixed-number detection [UTS #39, Section 5.3]:
      see @(see mixed-number-detection)."))
   (xdoc::p
    "From [UTS #51], Unicode Emoji:")
   (xdoc::ul
    (xdoc::li
     "The six emoji properties of characters [UTS #51, Annex A]:
      @('Emoji'), @('Emoji_Presentation'), @('Emoji_Modifier'),
      @('Emoji_Modifier_Base'), @('Emoji_Component')
      and @('Extended_Pictographic'):
      see @(see emoji)."))
   (xdoc::p
    "Relations between these properties
     are proved in @(see property-relations).")
   (xdoc::p
    "From [Stability], the Unicode Character Encoding Stability Policies,
     the following, as theorems about the supported versions
     (see @(see versions)):")
   (xdoc::ul
    (xdoc::li
     "Encoding Stability, as far as this:
      a code point that is assigned in a version
      is assigned in every later version.
      See @(see assigned-across-versions).")
    (xdoc::li
     "Normalization Stability:
      the four normalization forms of text
      whose characters are assigned in a version
      are the same in every later version,
      and so are the combining class and the decompositions
      of an assigned character,
      and the result of the Stream-Safe Text Process.
      See @(see normalization-across-versions).")
    (xdoc::li
     "Property Value Stability, for the properties that the library has:
      the code points of @('Noncharacter_Code_Point'),
      of @('Pattern_Syntax') and of @('Pattern_White_Space')
      are the same in every version;
      a code point that has @('XID_Start') or @('XID_Continue') keeps it
      (see @(see xid-across-versions)),
      and so does one that has @('ID_Start') or @('ID_Continue')
      (see @(see id-across-versions));
      no code point of @('Pattern_Syntax') or of @('Pattern_White_Space')
      has @('XID_Continue')
      (see @(see pattern-syntax-relations));
      and the code points whose @('General_Category') is
      @('Control'), @('Private_Use') or @('Surrogate')
      are the same in every version
      (see @(see general-category-stability)).")
    (xdoc::li
     "Identifier Stability, for the identifiers of @(see xid):
      an identifier of a version is an identifier of every later version."))
   (xdoc::p
    "The @('General_Category') of other characters is not stable.
     The library computes its changes between two versions:
     see @(see general-category-across-versions).
     Scripts, bidirectional classes, the emoji properties,
     and the identifier status and type are not stable either,
     and the library has no theorems about them across versions.")

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
      numeric values other than those of the decimal digits;
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
      when no code point has the value `no':
      the library has the properties,
      and the theorem only for that value;
      the sets of the code points that are stable under each form,
      of which the library has a subset that is common to the four;
      and a proof that the Stream-Safe Text Process
      keeps text that is in NFC or in NFKC in that form,
      which [UAX #15, Section 13] says
      and which the library proves for NFD and NFKD only.")
    (xdoc::li
     "From [UAX #31]:
      predicates for the identifiers
      that @('ID_Start') and @('ID_Continue') define,
      and for those of the profile for mathematical notation:
      the library has the properties,
      and a predicate only for the identifiers
      of @('XID_Start') and @('XID_Continue');
      and the other profiles and requirements of that annex.")
    (xdoc::li
     "From [Stability]:
      the policies about the names of characters,
      about case folding and case pairs,
      and about the names and aliases of properties,
      none of which the library has;
      and the policies as promises about versions to come,
      which are not something a theorem about the tables can say:
      the theorems are about the supported versions,
      and are checked again for each version that is added.")
    (xdoc::li
     "[UAX #9], the bidirectional algorithm:
      the library has the bidirectional class of each character,
      and does not say in which order text is displayed.")
    (xdoc::li
     "[UAX #29], text segmentation:
      grapheme clusters, words and sentences.
      Also [UAX #14], line breaking.")
    (xdoc::li
     "From [UTS #39]:
      the bidirectional skeleton,
      and so the skeleton and the confusability
      of the strings that are not displayed
      in the order in which they are stored;
      whether a string has a whole-script confusable at all
      [UTS #39, Section 4.1];
      and the restriction levels [UTS #39, Section 5.2].")
    (xdoc::li
     "From [UTS #51]: the emoji sequences,
      and the choice between text and emoji presentation.")
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
      rely on the skeleton and on the script sets of [UTS #39]:
      see @(see confusable-detection)
      and @(see mixed-script-detection).")
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
      the bidirectional controls and classes, Normalization Form C,
      the identifier status and type of [UTS #39],
      the emoji properties of [UTS #51],
      the scripts of characters, a block,
      the values of the decimal digits,
      and, of [UTS #39], the skeleton of a string
      that is displayed in the order in which it is stored,
      mixed-script detection and mixed-number detection,
      which are modeled.
      It also takes the bidirectional skeleton of [UTS #39],
      grapheme clusters, emoji sequences,
      and the names of characters,
      which are not.")))
  :order-subtopics t)
