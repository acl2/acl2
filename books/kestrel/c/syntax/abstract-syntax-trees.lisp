; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; Added 10/6/2024 by Matt K. after 3 successive ACL2(p) certification failures:
(acl2::set-waterfall-parallelism nil)

(include-book "file-paths")

(include-book "kestrel/fty/dec-digit-char-list" :dir :system)
(include-book "kestrel/fty/hex-digit-char-list" :dir :system)
(include-book "kestrel/fty/oct-digit-char-list" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-trees
  :parents (abstract-syntax)
  :short "Abstract syntax trees (ASTs)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for constructs that closely correspond to
     the grammar in [C17], which is summarized in [C17:A].
     For now we cover all the constructs after preprocessing,
     but we are working on adding some preprocessing constructs.")
   (xdoc::p
    "We also include certain GCC extensions,
     as mentioned in @(see syntax-for-tools).")
   (xdoc::p
    "According to the rationale explained in @(see syntax-for-tools),
     here we capture much of the information from the concrete syntax,
     e.g. the distinction between
     the @('0x') and @('0X') hexadecimal prefixes.")
   (xdoc::p
    "We try and pick short yet clear names for these fixtypes,
     so that code that manipulates these fixtypes
     can be a bit more more compact.
     While the grammar in [C17]
     uses the `hexadecimal' and `binary' qualifications
     for certain hexadecimal and binary entities
     but uses no qualifications for certain decimal entities,
     our fixtype names are more symmetric,
     using @('dec') and @('hex') and @('bin') qualifiers
     for certain ``parallel'' entities.")
   (xdoc::p
    "Some library fixtypes already correspond to
     certain nonterminals in the grammar in [C17]
     and are thus not defined here, but just used.
     Examples are fixtypes for digits (in different bases), and lists thereof.")
   (xdoc::p
    "The @('...-list') fixtypes are slightly more general than
     the <i>...-sequence</i> and <i>...-list</i> nonterminals
     in the grammar in [C17],
     because the former include the empty list,
     while the latter only include non-empty sequences/lists.
     Including empty lists in our fixtypes makes things a bit simpler,
     partly because currently @(tsee fty::deflist)
     generates conflicting theorems if used
     both with @(':non-emptyp t') and with (default) @(':non-emptyp nil')
     (although this could be remedied).
     It is fine (and common) for the abstract syntax
     to be more general than the concrete syntax.
     Restrictions on well-formed code can be formulated
     via separate predicates on the abstract syntax.
     The grammar in [C17] does not capture many static constraints anyhow.")
   (xdoc::p
    "The use of natural numbers to represent <i>c-char</i> and <i>s-char</i>
     in character constants and string literals is motivated by
     the fact that we commit to Unicode characters,
     even though [C17] prescribes no specific source character set [C17:5.2.1].
     These days, Unicode should be sufficiently general;
     note that ASCII is a subset of Unicode.
     Thus, the natural numbers represent Unicode code points,
     which include ASCII codes as a subset.
     Although natural numbers are more general that Unicode code points,
     and also more general than <i>c-char</i> and <i>s-char</i>,
     it is fine for abstract syntax to be more general than concrete syntax.")
   (xdoc::p
    "The syntax of C has some known ambiguities,
     which cannot be disambiguated purely syntactically,
     but need some (static) semantic analysis.
     Some of the fixtypes of our abstract syntax
     capture these ambiguous constructions,
     as described when those fixtypes are introduced.
     Here are some resources on the topic:")
   (xdoc::ul
    (xdoc::li
     (xdoc::ahref "https://en.wikipedia.org/wiki/Lexer_hack"
                  "The Wikipedia page on the lexer hack."))
    (xdoc::li
     (xdoc::ahref "https://eli.thegreenplace.net/2007/11/24/the-context-sensitivity-of-cs-grammar/"
                  "This blog post."))
    (xdoc::li
     (xdoc::ahref "https://web.archive.org/web/20131109145649/https://eli.thegreenplace.net/2011/05/02/the-context-sensitivity-of-cs-grammar-revisited/"
                  "This (web-archived) related blog post."))
    (xdoc::li
     (xdoc::ahref "https://stackoverflow.com/questions/17202409/how-typedef-name-identifier-issue-is-resolved-in-c"
                  "This Stack Overflow discussion."))
    (xdoc::li
     (xdoc::ahref "https://www.gnu.org/software/bison/manual/bison.html#Context-Dependency"
                  "The Bison documentation about context dependencies.")))
   (xdoc::p
    "Unlike some approaches suggested in the above resources,
     we prefer to defer the disambiguation of these constructs after parsing,
     so that parsing is purely syntactical,
     without the need for any semantic analysis during parsing.")
   (xdoc::p
    "Our abstract syntax also includes some information
     that is initially absent (after "
    (xdoc::seetopic "parser" "parsing")
    " and "
    (xdoc::seetopic "disambiguator" "disambiguation")
    ") and that is calculated by "
    (xdoc::seetopic "validator" "validation")
    ". This information is stored in the abstract syntax for easy access,
     e.g. access by tools to transform the abstract syntax.")
   (xdoc::p
    "This additional information can be also used, in the future,
     for other purposes than storing results from validation.
     This information in our fixtypes is untyped,
     which, in ACL2, can be regarded as analogous to
     using polymorphic types for the abstract syntax,
     parameterized over the type of the additional information."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident
  :short "Fixtype of identifiers [C17:6.4.2] [C17:A.1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>identifier</i> in the grammar in [C17].
     In this abstract syntax, we allow any ACL2 values as C identifiers.
     We wrap these arbitrary values into a one-component product fixtype
     so that we can more easily distinguish identifiers from other things.")
   (xdoc::p
    "Allowing arbitrary values as identifiers provides flexibility.
     For instance, a transformation on C code could introduce
     multiple versions of certain identifiers, indexed by numbers,
     in which case we could use pairs consisting of
     the original identifiers and the indices.")
   (xdoc::p
    "We plan to define, separately,
     predicates that restrict identifiers to certain forms,
     used for parsing, printing, transformations, etc.
     Restrictions are needed to print this abstract syntax
     into a form where identifiers respect the restrictions in [C17];
     in addition, parsing code compliant to [C17]
     will result in specific forms of identifiers."))
  ((unwrap any))
  :pred identp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ident-list
  :short "Fixtype of lists of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers are defined in @(tsee ident)."))
  :elt-type ident
  :true-listp t
  :elementp-of-nil nil
  :pred ident-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset ident-set
  :short "Fixtype of sets of identifiers."
  :long
  (xdoc::topstring
    (xdoc::p
      "Identifiers are defined in @(tsee ident)."))
  :elt-type ident
  :elementp-of-nil nil
  :pred ident-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption ident-option
  ident
  :short "Fixtype of optional identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers are defined in @(tsee ident)."))
  :pred ident-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset ident-option-set
  :short "Fixtype of sets of optional identifiers."
  :long
  (xdoc::topstring
    (xdoc::p
      "Identifiers are defined in @(tsee ident)."))
  :elt-type ident-option
  :elementp-of-nil t
  :pred ident-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lsuffix
  :short "Fixtype of length suffixes [C17:6.4.4.1] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>long-suffix</i> and <i>long-long-suffix</i>
     in the grammar in [C17].
     We use the term `length suffix' here,
     but the grammar in [C17] does not use that term,
     although it is arguably a good term to denote
     both long and long-long suffixes.
     This captures the four possible suffixes
     @('l'), @('L'), @('ll'), and @('LL')."))
  (:locase-l ())
  (:upcase-l ())
  (:locase-ll ())
  (:upcase-ll ())
  :pred lsuffixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum usuffix
  :short "Fixtype of unsigned suffixes [C17:6.4.41] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>unsigned-suffix</i> in the grammar in [C17].
     This captures the two possible suffixes @('u') and @('U')."))
  (:locase-u ())
  (:upcase-u ())
  :pred usuffixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum isuffix
  :short "Fixtype of integer suffixes [C17:6.4.4.1] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>integer-suffix</i> in the grammar in [C17].
     This captures the four possibilities of
     (i) just an unsigned suffix,
     (ii) just a length suffix,
     (iii) an unsigned suffix followed by a length suffix, and
     (iv) a length suffix followed by an unsigned suffix."))
  (:u ((unsigned usuffix)))
  (:l ((length lsuffix)))
  (:ul ((unsigned usuffix)
        (length lsuffix)))
  (:lu ((length lsuffix)
        (unsigned usuffix)))
  :pred isuffixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption isuffix-option
  isuffix
  :short "Fixtype of optional integer suffixes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer suffixes are defined in @(tsee isuffix)."))
  :pred isuffix-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hprefix
  :short "Fixtype of hexadecimal prefixes [C17:6.4.4.1] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-prefix</i> in the grammar in [C17].
     This captures the two possible prefixes @('0x') and @('0X')."))
  (:locase-0x ())
  (:upcase-0x ())
  :pred hprefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec/oct/hex-const
  :short "Fixtype of decimal, octal, and hexadecimal constants
          [C17:6.4.4.1] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures
     <i>decimal-constant</i>,
     <i>octal-constant</i>, and
     <i>hexadecimal-constant</i>
     in the grammar in [C17].
     The grammar does not have a nonterminal
     that directly corresponds to this fixtype:
     the three alternatives are given in
     the grammar rule for <i>integer-constant</i>,
     along with the optional integer suffixes.
     In these fixtypes, we factor this a little differently
     (see @(tsee iconst)).")
   (xdoc::p
    "A decimal constant is completely characterized by
     its positive integer values.
     Note that @('0') is an octal constant (not a decimal one).
     Decimal constants cannot have leading zeros,
     and thus there is a unique list of digits
     that corresponds to a positive integer.")
   (xdoc::p
    "An octal constant is completely characterized by
     the number of (one or more) leading zeros
     and by its non-negative integer value.
     The non-negative integer value determines
     the non-zero-starting list of digits that follow the leading zeros.
     Note that the octal constant @('0') is represented, in this fixtype,
     as consisting of one leading 0 and the value 0:
     the value 0 determines the empty non-zero-starting list of digits.")
   (xdoc::p
    "A hexadecimal constant consists of a prefix
     and a list of digits (which should be non-empty).
     The fixtype @(tsee hex-digit-char-list)
     corresponds, in the grammar in [C17],
     to <i>hexadecimal-constant</i> without <i>hexadecimal-prefix</i>.
     The non-decimal hexadecimal digits may be uppercase and lowercase,
     so in order to capture all the information from the abstract syntax
     we use lists of digits in this fixtype,
     which can be of course converted to integer values."))
  (:dec ((value pos)))
  (:oct ((leading-zeros pos)
         (value nat)))
  (:hex ((prefix hprefix)
         (digits hex-digit-char-list)))
  :pred dec/oct/hex-constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod iconst
  :short "Fixtype of integer constants [C17:6.4.4.1] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>integer-constant</i> in the grammar in [C17].
     As mentioned in @(tsee dec/oct/hex-const),
     our fixtypes are factored slightly differently.
     An integer constant consists of a decimal, octal, or hexadecimal constant,
     and of an optional integer suffix.")
   (xdoc::p
    "Integer constants may be accompanied by some additional information,
     such as the value calculated during validation."))
  ((core dec/oct/hex-const)
   (suffix? isuffix-option)
   (info any))
  :pred iconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption iconst-option
  iconst
  :short "Fixtype of optional integer constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer constants are defined in @(tsee iconst)."))
  :pred iconst-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fsuffix
  :short "Fixtype of floating suffixes [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>floating-suffix</i> in the grammar in [C17].
     This captures the four possible suffixes
     @('f'), @('F'), @('l'), and @('L')."))
  (:locase-f ())
  (:upcase-f ())
  (:locase-l ())
  (:upcase-l ())
  :pred fsuffixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fsuffix-option
  fsuffix
  :short "Fixtype of optional floating suffixes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Floating suffixes are defined in @(tsee fsuffix)."))
  :pred fsuffix-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum sign
  :short "Fixtype of signs [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>sign</i> in the grammar in [C17].
     This captures the two possible signs @('+') and @('-')
     used in the exponents of floating constants."))
  (:plus ())
  (:minus ())
  :pred signp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption sign-option
  sign
  :short "Fixtype of optional signs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Signs are defined in @(tsee sign)."))
  :pred sign-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec-expo-prefix
  :short "Fixtype of decimal exponent prefixes [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the @('e') or @('E') prefix
     in <i>exponent-part</i> in the grammar in [C17]."))
  (:locase-e ())
  (:upcase-e ())
  :pred dec-expo-prefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bin-expo-prefix
  :short "Fixtype of binary exponent prefixes [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the @('p') or @('P') prefix
     in <i>binary-exponent-part</i> in the grammar in [C17]."))
  (:locase-p ())
  (:upcase-p ())
  :pred bin-expo-prefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod dec-expo
  :short "Fixtype of decimal exponents [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>exponent-part</i> in the grammar in [C17].
     It consists of a prefix,
     an optional sign,
     and a list of (decimal) digits (which should be non-empty)."))
  ((prefix dec-expo-prefix)
   (sign? sign-option)
   (digits dec-digit-char-list))
  :pred dec-expop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption dec-expo-option
  dec-expo
  :short "Fixtype of optional decimal exponents."
  :long
  (xdoc::topstring
   (xdoc::p
    "Decimal exponents are defined in @(tsee dec-expo)."))
  :pred dec-expo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bin-expo
  :short "Fixtype of binary exponents [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>binary-exponent-part</i> in the grammar in [C17].
     It consists of a prefix,
     an optional sign,
     and a list of (decimal) digits (which should be non-empty).
     The digits are decimal, not binary or hexadecimal;
     but the implicit base of the exponent is binary [C17:6.4.4.2/3]."))
  ((prefix bin-expo-prefix)
   (sign? sign-option)
   (digits dec-digit-char-list))
  :pred bin-expop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod dec-frac-const
  :short "Fixtype of decimal fractional constants [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>fractional-constant</i>
     in the grammar in [C17].
     It consists of the digits before and after the point.
     Thus, it covers the three possibilities of
     (i) the point in the middle (with a left and right digit sequence),
     (ii) the point at the start (with just a right digit sequence), and
     (iii) the point at the end (with just a left digit sequence);
     it also covers a fourth possibility, disalowed in the grammar in [C17],
     namely when there are no digits before or after the point.
     This fourth possibilty makes the definition of this fixtype simpler,
     and can be ruled out by predicates over this abstract syntax."))
  ((before dec-digit-char-list)
   (after dec-digit-char-list))
  :pred dec-frac-constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-frac-const
  :short "Fixtype of hexadecimal fractional constants [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-fractional-constant</i>
     in the grammar in [C17].
     It consists of the digits before and after the point.
     Thus, it covers the three possibilities of
     (i) the point in the middle (with a left and right digit sequence),
     (ii) the point at the start (with just a right digit sequence), and
     (iii) the point at the end (with just a left digit sequence);
     it also covers a fourth possibility, disalowed in the grammar in [C17],
     namely when there are no digits before or after the point.
     This fourth possibilty makes the definition of this fixtype simpler,
     and can be ruled out by predicates over this abstract syntax."))
  ((before hex-digit-char-list)
   (after hex-digit-char-list))
  :pred hex-frac-constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec-core-fconst
  :short "Fixtype of decimal core floating constants [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>decimal-floating-constant</i>
     in the grammar in [C17], but without the optional suffix,
     which is what we mean by `core' in the name of this fixtype
     (we factor things slightly differently in our fixtypes;
     see @(tsee fconst)).
     This covers the three possibilities of
     (i) a (decimal) fractional significand without an exponent,
     (ii) a (decimal) fractional significand with a (decimal) exponent, and
     (iii) a (decimal) integer significand with a (decimal) exponent.
     The first two possibilities are modeled as
     a fractional significand with an optional exponent."))
  (:frac ((significand dec-frac-const)
          (expo? dec-expo-option)))
  (:int ((significand dec-digit-char-list)
         (expo dec-expo)))
  :pred dec-core-fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hex-core-fconst
  :short "Fixtype of hexadecimal core floating constants [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-floating-constant</i>
     in the grammar in [C17], but without the prefix and the optional suffix,
     which is what we mean by `core' in the name of this fixtype
     (we factor things slightly differently in our fixtypes;
     see @(tsee fconst)).
     This covers the two possibilities of
     (i) a (hexadecimal) fractional significand with a (binary) exponent and
     (iii) a (hexadecimal integer significand with a (binary) exponent."))
  (:frac ((significand hex-frac-const)
          (expo bin-expo)))
  (:int ((significand hex-digit-char-list)
         (expo bin-expop)))
  :pred hex-core-fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fconst
  :short "Fixtype of floating constants [C17:6.4.4.2] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>floating-constant</i> in the grammar in [C17].
     As mentioned in @(tsee dec-core-fconst) and @(tsee hex-core-fconst),
     we factor things a bit differently in our fixtypes,
     so here we add the prefixes and suffixes as appropriate."))
  (:dec ((core dec-core-fconst)
         (suffix? fsuffix-option)))
  (:hex ((prefix hprefix)
         (core hex-core-fconst)
         (suffix? fsuffix-option)))
  :pred fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum simple-escape
  :short "Fixtype of simple escape sequences [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>simple-escape-sequence</i> in the grammar in [C17].
     A simple escape sequence consists of
     a backslash (implicit in this fixtype definition)
     followed by another character (indicated by the fixtype constructor):
     @('\\\''),
     @('\\\"'),
     @('\\?'),
     @('\\\\'),
     @('\\a'),
     @('\\b'),
     @('\\f'),
     @('\\n'),
     @('\\r'),
     @('\\t'), and
     @('\\v').
     We also include the @('\\%') GCC extension (see our ABNF grammar)."))
  (:squote ())
  (:dquote ())
  (:qmark ())
  (:bslash ())
  (:a ())
  (:b ())
  (:f ())
  (:n ())
  (:r ())
  (:t ())
  (:v ())
  (:percent ())
  :pred simple-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum oct-escape
  :short "Fixtype of octal escape sequences [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>octal-escape-sequence</i> in the grammar in [C17].
     An octal escape sequence consists of
     a backslash (implicit in this fixtype definition)
     followed by one, two, or three octal digits."))
  (:one ((digit oct-digit-char)))
  (:two ((digit1 oct-digit-char)
         (digit2 oct-digit-char)))
  (:three ((digit1 oct-digit-char)
           (digit2 oct-digit-char)
           (digit3 oct-digit-char)))
  :pred oct-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-quad
  :short "Fixtype of quadruples of hexadecimal digits [C17:6.4.3] [C17:A.1.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hex-quad</i> in the grammar in [C17]."))
  ((1st hex-digit-char)
   (2nd hex-digit-char)
   (3rd hex-digit-char)
   (4th hex-digit-char))
  :pred hex-quad-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum univ-char-name
  :short "Fixtype of universal character names [C17:6.4.3] [C17:A.1.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>universal-character-name</i>
     in the grammar in [C17].
     The two cases of this fixtype correspond to
     @('\\uXXXX') and @('\\UXXXXYYYY')."))
  (:locase-u ((quad hex-quad)))
  (:upcase-u ((quad1 hex-quad)
              (quad2 hex-quad)))
  :pred univ-char-name-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum escape
  :short "Fixtype of escape sequences [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>escape-sequence</i> in the grammar in [C17].
     For a hexadecimal escape sequence,
     we use lists of hexadecimal digit characters,
     which correspond to <i>hexadecimal-escape-sequence</i>
     without the implicit @('\\x') prefix."))
  (:simple ((unwrap simple-escape)))
  (:oct ((unwrap oct-escape)))
  (:hex ((unwrap hex-digit-char-list)))
  (:univ ((unwrap univ-char-name)))
  :pred escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum c-char
  :short "Fixtype of characters and escape sequences
          usable in character constants [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>c-char</i> in the grammar in [C17].")
   (xdoc::p
    "As explained in @(see abstract-syntax),
     the natural numbers represent Unicode code points.
     We do not capture the restriction that the characters cannot be
     single quote, backslash, or new-line."))
  (:char ((unwrap nat)))
  (:escape ((unwrap escape)))
  :pred c-char-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist c-char-list
  :short "Fixtype of lists of characters and escape sequences
          usable in character constants [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Characters and escape sequences usable in character constants
     are defined in @(tsee c-char)."))
  :elt-type c-char
  :true-listp t
  :elementp-of-nil nil
  :pred c-char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cprefix
  :short "Fixtype of prefixes of character constants [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @('L'), @('u'), and @('U') prefixes
     in <i>character-constant</i> in the grammar in [C17]."))
  (:upcase-l ())
  (:locase-u ())
  (:upcase-u ())
  :pred cprefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption cprefix-option
  cprefix
  :short "Fixtype of optional prefixes of character constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "Prefixes of character constants are defined in @(tsee cprefix)."))
  :pred cprefix-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cconst
  :short "Fixtype of character constants [C17:6.4.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>character-constant</i> in the grammar in [C17]."))
  ((prefix? cprefix-option)
   (cchars c-char-list))
  :pred cconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum const
  :short "Fixtype of constants [C17:6.4.4] [C17:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>constant</i> in the grammar in [C}."))
  (:int ((unwrap iconst)))
  (:float ((unwrap fconst)))
  (:enum ((unwrap ident)))
  (:char ((unwrap cconst)))
  :pred constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption const-option
  const
  :short "Fixtype of optional constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "Constans are defined in @(tsee const)."))
  :pred const-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum s-char
  :short "Fixtype of characters and escape sequences
          usable in string literals [C17:6.4.5] [C17:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>s-char</i> in the grammar in [C17].")
   (xdoc::p
    "As explained in @(see abstract-syntax),
     the natural numbers represent Unicode code points.
     We do not capture the restriction that the characters cannot be
     double quote, backslash, or new-line."))
  (:char ((unwrap nat)))
  (:escape ((unwrap escape)))
  :pred s-char-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist s-char-list
  :short "Fixtype of lists of characters and escape sequences
          usable in string literals [C17:6.4.5] [C17:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Characters and escape sequences usable in string literals
     are defined in @(tsee s-char)."))
  :elt-type s-char
  :true-listp t
  :elementp-of-nil nil
  :pred s-char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum eprefix
  :short "Fixtype of encoding prefixes [C17:6.4.5] [C17:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>encoding-prexif</i> in the grammar in [C17]."))
  (:locase-u8 ())
  (:locase-u ())
  (:upcase-u ())
  (:upcase-l ())
  :pred eprefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption eprefix-option
  eprefix
  :short "Fixtype of optional encoding prefixes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Encoding prefixes are defined in @(tsee eprefix)."))
  :pred eprefix-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist eprefix-option-list
  :short "Fixtype of lists of optional encoding prefixes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Optional encoding prefixes are defined in @(tsee eprefix-option)."))
  :elt-type eprefix-option
  :true-listp t
  :elementp-of-nil t
  :pred eprefix-option-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stringlit
  :short "Fixtype of string literals [C17:6.4.5] [C17:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>string-literal</i> in the grammar in [C17]."))
  ((prefix? eprefix-option)
   (schars s-char-list))
  :pred stringlitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist stringlit-list
  :short "Fixtype of lists of string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "String literals are defined in @(tsee stringlit)."))
  :elt-type stringlit
  :true-listp t
  :elementp-of-nil nil
  :pred stringlit-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod h-char
  :short "Fixtype of characters usable in
          header names between angle brackets [C17:6.4.7] [C17:A.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>h-char</i> in the grammar in [C17].")
   (xdoc::p
    "As explained in @(see abstract-syntax),
     the natural numbers represent Unicode code points.
     We wrap the natural number in this fixtype for more abstraction,
     and to facilitate the addition of restrictions on the number,
     namely that the character cannot be @('>') or a new-line,
     but for now we do not capture this restriction."))
  ((char nat))
  :pred h-char-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist h-char-list
  :short "Fixtype of lists of characters usable in
          header names between angle brackets [C17:6.4.7] [C17:A.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Characters usable in header names between angle brackets
     are defined in @(tsee h-char)."))
  :elt-type h-char
  :true-listp t
  :elementp-of-nil nil
  :pred h-char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod q-char
  :short "Fixtype of characters usable in
          header names between double quotes [C17:6.4.7] [C17:A.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>q-char</i> in the grammar in [C17].")
   (xdoc::p
    "As explained in @(see abstract-syntax),
     the natural numbers represent Unicode code points.
     We wrap the natural number in this fixtype for more abstraction,
     and to facilitate the addition of restrictions on the number,
     namely that the character cannot be @('>') or a new-line,
     but for now we do not capture this restriction."))
  ((char nat))
  :pred q-char-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist q-char-list
  :short "Fixtype of lists of characters usable in
          header names between double quotes [C17:6.4.7] [C17:A.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Characters usable in header names between double quotes
     are defined in @(tsee q-char)."))
  :elt-type q-char
  :true-listp t
  :elementp-of-nil nil
  :pred q-char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum header-name
  :short "Fixtype of header names [C17:6.4.7] [C17:A.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>header-name</i> in the grammar in [C17]."))
  (:angles ((chars h-char-list)))
  (:quotes ((chars q-char-list)))
  :pred header-namep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unop
  :short "Fixtype of unary operators
          [C17:6.5.3] [C17:6.5.2] [C17:A.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>unary-operator</i> in the grammar in [C17],
     but it also includes one-argument operators
     used in <i>unary-expression</i> and <i>postfix-expression</i>,
     which can therefore be reasonably regarded as unary operators,
     although the grammar in [C17] reserves the term to only some of them.
     From the standpoint of our abstract syntax,
     including the additional operators under this definition of unary operators
     makes things more factored and orthogonal.
     The operators are
     @('&') (unary),
     @('*') (unary),
     @('+') (unary),
     @('-') (unary),
     @('~'),
     @('!'),
     @('++') (prefix),
     @('--') (prefix),
     @('++') (postfix),
     @('--') (postfix), and
     @('sizeof').
     The latter is the variant on expressions;
     see @(tsee expr)."))
  (:address ())
  (:indir ())
  (:plus ())
  (:minus ())
  (:bitnot ())
  (:lognot ())
  (:preinc ())
  (:predec ())
  (:postinc ())
  (:postdec ())
  (:sizeof ())
  :pred unopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum binop
  :short "Fixtype of binary operators
          [C17:6.5.5-14] [C17:6.5.16] [C17:A.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in [C17] does not have a nonterminal for binary operators.
     Instead, it has nonterminals for various kinds of binary expressions,
     used to capture certain precedence rules in the grammar itself.
     In our abstract syntax, for better factoring and orthogonality,
     it makes sense to introduce a fixtype for binary operators,
     and use it to define binary expressions as we do in @(tsee expr).
     The binary operators are
     @('*') (binary),
     @('/'),
     @('%'),
     @('+') (binary),
     @('-') (binary),
     @('<<'),
     @('>>'),
     @('<'),
     @('>'),
     @('<='),
     @('>='),
     @('=='),
     @('!='),
     @('&') (binary),
     @('^'),
     @('|'),
     @('&&'),
     @('||'),
     @('='),
     @('*='),
     @('/='),
     @('%='),
     @('+='),
     @('-='),
     @('<<='),
     @('>>='),
     @('&='),
     @('^='), and
     @('|=')."))
  (:mul ())
  (:div ())
  (:rem ())
  (:add ())
  (:sub ())
  (:shl ())
  (:shr ())
  (:lt ())
  (:gt ())
  (:le ())
  (:ge ())
  (:eq ())
  (:ne ())
  (:bitand ())
  (:bitxor ())
  (:bitior ())
  (:logand ())
  (:logor ())
  (:asg ())
  (:asg-mul ())
  (:asg-div ())
  (:asg-rem ())
  (:asg-add ())
  (:asg-sub ())
  (:asg-shl ())
  (:asg-shr ())
  (:asg-and ())
  (:asg-xor ())
  (:asg-ior ())
  :pred binopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum inc/dec-op
  :short "Fixtype of increment and decrement operators
          [C17:6.5.3] [C17:6.5.2] [C17:A.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @('++') and @('--') operators,
     for pre- and post- increment and decrement.
     They are already part of @(tsee unop),
     but we also need a fixtype for just the two of them,
     so we can form lists in @(tsee inc/dec-op-list),
     which are used to capture parts of certain ambiguous constructs
     (see @(tsee expr))."))
  (:inc ())
  (:dec ())
  :pred inc/dec-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist inc/dec-op-list
  :short "Fixtype of lists of increment and decrement operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Increment and decrement operators are defined in @(tsee inc/dec-op)."))
  :elt-type inc/dec-op
  :true-listp t
  :elementp-of-nil nil
  :pred inc/dec-op-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum keyword-uscores
  :short "Fixtype of keyword underscores."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some keywords for GCC extensions have variants
     without underscores,
     with underscores at the beginning,
     and with underscores at both the beginning and end:
     see the ABNF grammar for examples.")
   (xdoc::p
    "In order to preserve that information in our abstract syntax,
     we introduce a fixtype that captures those three possibilities."))
  (:none ())
  (:start ())
  (:both ())
  :pred keyword-uscores-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum stor-spec
  :short "Fixtype of storage class specifiers [C17:6.7.1] [C17:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>storage-class-specifier</i> in the grammar in [C17].
     The storage class specifiers are
     @('typedef'),
     @('extern'),
     @('static'),
     @('_Thread_local'),
     @('auto'), and
     @('register').")
   (xdoc::p
    "We also include the @('__thread') storage class specifier
     as a GCC extension and variant of @('_Thread_local'). See "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Thread-Local.html"
                 "``Thread-Local Storage")
    " in the GCC documentation."))
  (:typedef ())
  (:extern ())
  (:static ())
  (:thread ((local bool)))
  (:auto ())
  (:register ())
  :pred stor-specp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist stor-spec-list
  :short "Fixtype of lists of storage class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Storage class specifiers are defined in @(tsee stor-spec)."))
  :elt-type stor-spec
  :true-listp t
  :elementp-of-nil nil
  :pred stor-spec-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-qual
  :short "Fixtype of type qualifiers [C17:6.7.3] [C17:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>type-qualifier</i> in the grammar in [C17].
     The type qualifiers are
     @('const'),
     @('restrict'),
     @('volatile'), and
     @('_Atomic').")
   (xdoc::p
    "We also include the GCC extension variants
     @('__restrict') and @('__restrict__') of @('restrict'),
     only used if GCC extensions are supported.
     These are captured by adding underscore information
     to the @(':restrict') case.")
   (xdoc::p
    "We also include the GCC extension variants
     @('__volatile') and @('__volatile__') of @('volatile'),
     only used if GCC extensions are supported.
     These are captured by adding underscore information
     to the @(':volatile') case."))
  (:const ())
  (:restrict ((uscores keyword-uscores)))
  (:volatile ((uscores keyword-uscores)))
  (:atomic ())
  :pred type-qualp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fun-spec
  :short "Fixtype of function specifiers [C17:6.7.4] [C17:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>function-specifier</i> in the grammar in [C17].
     The function specifiers are @('inline') and @('_Noreturn').")
   (xdoc::p
    "We also include the GCC extension variants
     @('__inline') and @('__inline__') of @('inline'),
     only used if GCC extensions are supported.
     These are captured by adding underscore information
     to the @(':inline') case."))
  (:inline ((uscores keyword-uscores)))
  (:noreturn ())
  :pred fun-specp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod asm-name-spec
  :short "Fixtype of GCC assembler name specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Asm-Labels.html"
                 "construct to specify assembler names")
    ". It consists of the keyword @('asm') or @('__asm') or @('__asm__')
     and a parenthesized string literal.
     Since adjacent string literals may be concatenated [C17:5.1.1.2/6],
     we allow a list of string literals here;
     this way, we preserve the fact that there were adjacent string literals.
     Indeed, we have observed multiple (two, to be precise)
     string literals in this construct in practical code.
     We also capture which keyword variant (with or without underscores)
     was used.")
   (xdoc::p
    "The GCC documentation does not provide a clear term
     to denote this construct,
     although the URL suggests that it is an `assembler label';
     but the text does not mention that term.
     Note that this is not the only kind of assembler construct
     in GCC extensions; there are others.
     So we use the term `assembler name specifier' for this construct,
     since it specifies the assembler name (of an identifier).")
   (xdoc::p
    "We use a list of string literals,
     which should be non-empty, although we do not capture this constraint.
     This way, we preserve the information about adjacent string literals."))
  ((strings stringlit-list)
   (uscores keyword-uscores))
  :pred asm-name-specp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption asm-name-spec-option
  asm-name-spec
  :short "Fixtype of optional assembler name specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Assembler name specifiers are defined in @(tsee asm-name-spec)."))
  :pred asm-name-spec-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum asm-qual
  :short "Fixtype of assembler qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are a GCC extension; see ABNF grammar."))
  (:volatile ((uscores keyword-uscores)))
  (:inline ((uscores keyword-uscores)))
  (:goto ())
  :pred asm-qualp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist asm-qual-list
  :short "Fixtype of lists of assembler qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Assembler qualifiers are defined in @(tsee asm-qual)."))
  :elt-type asm-qual
  :true-listp t
  :elementp-of-nil nil
  :pred asm-qual-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod asm-clobber
  :short "Fixtype of assembler clobbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are a GCC extension; see ABNF grammar."))
  ((unwrap stringlit-list))
  :pred asm-clobberp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist asm-clobber-list
  :short "Fixtype of lists of assembler clobbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Assembler clobbers are defined in @(tsee asm-clobber)."))
  :elt-type asm-clobber
  :true-listp t
  :elementp-of-nil nil
  :pred asm-clobber-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum attrib-name
  :short "Fixtype of attribute names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Attributes are a GCC extension.
     An attribute name is an identifier or a keyword: see the ABNF grammar.
     We use an ACL2 string to represent a keyword."))
  (:ident ((unwrap ident)))
  (:keyword ((unwrap string)))
  :pred attrib-namep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes exprs/decls/stmts
  :short "Fixtypes of expressions, declarations, statements,
          and related entities
          [C17:6.5] [C17:6.6] [C17:6.7] [C17:6.8]
          [C17:A.2.1] [C17:A.2.2] [C17:A.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in [C17] defines expressions and declarations
     via a large and complex collection of mutually recursive rules;
     statements are not mutualy recursive with expressions and declarations.
     However, GCC extensions include statement expressions,
     i.e. the ability to use a parenthesized (compound) statement
     as an expression:
     this extends the mutual recursion to statements.
     Here we want to capture GCC extensions,
     so we define a collection of mutually recursive fixtypes
     for expressions, declarations, statements, and related entities;
     this takes a few seconds to process on fast machines.")
   (xdoc::p
    "A few fixtypes related to declarations
     are actually outside this mutual recursion,
     because they are not mutually recursive with others.
     For instance, the fixtype @(tsee type-qual) for type qualifiers
     is defined before these mutually recursive fixtypes.
     Also, external declarations are defined outside the recursion,
     after these mutualy recursive fixtypes.")
   (xdoc::p
    "As is sometimes the case with mutually recursive fixtypes,
     we need to add @(':base-case-override') to some sum fixtypes,
     as well as @(':measure') with @(tsee two-nats-measure) to all the fixtypes.
     For instance, @(tsee genassoc) does not have a clear base case,
     and thus we specify to use the @(':default') case of this sum fixtype.
     But then the accessor @('genassoc-default->expr') must always return
     an expression that is smaller than its input,
     even when its input is not a @(tsee genassoc) value,
     but any ACL2 value, including atoms.
     In order to achieve that,
     we add a second lexicographic component to the measure,
     making a @(tsee genassoc) always larger than an @(tsee expr)
     when the two have the same @(tsee acl2-count)
     (which is the case when they are certain atoms).
     There are some additional patterns
     in the use of this second lexicographic components:
     a @(tsee fty::defoption)
     has one more than the base fixtype;
     a @(tsee fty::defprod)
     has one more than the component fixtypes.
     There is one instance in which it does not seem possible
     to find appropriate second lexicographic components:
     in a @(tsee dirabsdeclor), all the cases except @(':paren')
     contain an @(tsee dirabsdeclor-option),
     which as discussed above must have a larger second lexicographic component;
     thus the only possible base case is @(':paren'),
     which contains an @(tsee absdeclor),
     and so it must have a larger second lexicographic component,
     but @(tsee absdeclor) is a @(tsee fty::defprod)
     containing an @(tsee dirabsdeclor),
     which in turn must have a larger second lexicographic component.
     Thus, we add a dummy base case @(':dummy-base') to @(tsee dirabsdeclor),
     whch is unfortunate but perhaps unavoidable.
     We will prohibit the occurrence of @(':dummy-base') via separate checks."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of expressions [C17:6.5] [C17:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>expression</i> in the grammar in [C17].")
     (xdoc::p
      "Given that the abstract syntax is tree-structured,
       we do not explicitly introduce the various kinds of binary expressions
       defined in the grammar in [C17],
       and instead use a single kind of binary expression
       consisting of two sub-expressions and a binary operator.
       Furthermore, we always use the general fixtype for expressions
       as components of other constructs where the grammar in [C17]
       uses more specific kinds of expressions,
       like <i>assignment-expression</i> in <i>generic-selection</i>.
       This means that our fixtypes are a bit more general,
       but we can use separate predicates to enforce restrictions.")
     (xdoc::p
      "Some kinds of expressions may include some additional information
       (e.g. identifiers),
       such as types calculated during validation.
       This is an instance of the additional information
       discussed in @(tsee abstract-syntax).")
     (xdoc::p
      "In order to capture
       possibly redundant parenthesization from the concrete syntax,
       we include, in this fixtype, a case @(':paren')
       for an explicitly parenthesized expression.")
     (xdoc::p
      "There is a syntactic overlap between
       identifier expressions (variables) and (enumeration) constants.
       This ambiguity cannot be resolved purely syntactically.
       During parsing, we classify those as identifier expressions,
       and defer a possible re-classification to enumeration constant
       during a post-parsing static semantic analysis.")
     (xdoc::p
      "Instead of a single string literal, we allow a list of them,
       which should be non-empty, although we do not capture this constraint.
       This mirrors the ABNF grammar;
       we preserve the information about adjacent string literals,
       as opposed to concatenating them into one.")
     (xdoc::p
      "The @(':sizeof') case of this fixtype
       captures @('sizeof') applied to a type name.
       The @('sizeof') applied to an expression is instead captured
       in the @(':unary') case,
       since @(tsee unop) includes @('sizeof') for expressions.
       As explained in @(tsee amb-expr/tyname),
       there is a complex syntactic overlap between expressions and type names;
       thus, an expression of the form @('sizeof(X)'),
       where @('X') is in that syntactic overlap,
       is inherently ambiguous.
       (The simplest case is when @('X') is an identifier,
       but as explained in @(tsee amb-expr/tyname)
       there are infinitely many cases.)
       This is captured by the @(':sizeof-ambig') case,
       which contains an @(tsee amb-expr/tyname).")
     (xdoc::p
      "The @(':alignof') case of this fixtype
       includes an indication of the underscore variant.
       Note that the variant without underscores
       represents the standard @('_Alignof'),
       not the non-existing @('alignof'),
       while the other two represent @('__alignof') and @('__alignof__');
       see the ABNF grammar.
       Presumably, @('_Alignof') was added to the grammar
       after @('__alignof') and @('__alignof__') were GCC extensions.")
     (xdoc::p
      "We use different cases, @(':member') and @(':memberp')
       for the @('.') and @('->') operators.")
     (xdoc::p
      "For compound literals, we also capture
       the presence or absence of the final comma
       just after the <i>initializer-list</i>.
       We formalize <i>initializer-list</i> [C17:6.7.9] [C17:A.2.2]
       as a list (which should be non-empty, unless GCC extensions are enabled)
       of pairs each consisting of
       some designators and an initializer (see @(tsee desiniter).")
     (xdoc::p
      "The comma sequentialization operator is modeled
       as its own case in this fixtype.
       An alternative is to include that into @(tsee binop).
       Another alternative is to model it as taking
       a list of expressions (it associates to the left).
       But for now the current model is adequate.")
     (xdoc::p
      "The last five kinds of expressions capture
       syntactically ambiguous expressions of the forms")
     (xdoc::codeblock
      "( X ) IncDec ( E ) Pr"
      "( X ) IncDec * E"
      "( X ) IncDec + E"
      "( X ) IncDec - E"
      "( X ) IncDec & E")
     (xdoc::p
      "where @('X') is an ambiguous expression or type name,
       @('IncDec') is a sequence of zero or more
       increment and decrement operators @('++') and @('--'),
       @('E') is an expression,
       and @('Pr') is a possibly empty rest of a postfix expression.
       All of this is now explained in detail.")
     (xdoc::p
      "If @('X') is an ambiguous expression or type name
       (i.e. something captured by @(tsee amb-expr/tyname)),
       then @('(X)') could either start a proper cast expression
       (if @('X') is a type name)
       or be or start an expression that is or starts with
       a parenthesized primary expression
       (if @('X') is an expression).
       Note that @('(X)') could also start a compound literal,
       but in that case we would be able to disambiguate @('X')
       to be a type name and not an expression,
       because an expression @('(X)') cannot be followed by an open curly brace.
       So if @('(X)') is not followed by an open curly brace,
       there are a number of other tokens that may follow:
       some would let us disambiguate @('X')
       to be either a type name or an expression;
       but in other cases it is not possible to disambiguate @('X'),
       and so, similarly to @(':sizeof-ambig'),
       we capture the ambiguous constructs explicitly in our abstract syntax.
       But for these ambiguous casts, the situation is more complex.")
     (xdoc::p
      "In the five patterns shown above,
       it is easier to ignore the @('IncDec') part at first,
       pretending it is not there.
       In the first pattern, the @('Pr') is either empty
       or one or more of the constructs that
       may be cascaded in postfix expressions.
       For instance, @('Pr') could have the form @('[3].mem(ab)++'),
       which consists of
       an array access @('[3]'),
       a member access @('.mem'),
       a function call @('(ab)') where @('ab') is the argument,
       and a postincrement operator @('++').
       In this situation, if @('X') is an expression
       then @('(X)(E)') is a function call that precedes the array access;
       but if @('X') is a type name,
       then @('(E)') is the start of a postfix expression.
       Note that in general an expression @('E')
       could be a comma-separated sequence of (assignment) expressions,
       but that still looks like a function call,
       with multiple arguments:
       see the isomorphism between the grammar rules for
       <i>argument-expression-list</i> and <i>expression</i> in [C17].
       The two situations cannot be disambiguated purely syntactically.
       So the @(':cast/call-ambig') case of this fixtype
       captures this ambiguous situation:
       it is either a cast to @('X') or a call of @('X'),
       where the @('X') component (an @(tsee amb-expr/tyname))
       is either a type (name) or a function,
       and where the @('(E)Pr') component (an expression)
       is either the argument of the cast
       or the rest of the postfix expression.
       Currently this fixtype does not capture the requirement that
       the expression has in fact the form @('(E)Pr'),
       but this should be an invariant after parsing,
       and it can be enforced externally to this fixtype.")
     (xdoc::p
      "The addition of @('IncDec') maintains the ambiguity.
       If @('X') is a type name,
       the sequence of operators are pre-increment/decrement ones
       that are part of the argument of the cast,
       and whose final argument is @('(E)Pr').
       If instead @('X') is an expression,
       we have a postfix expression starting with @('X'),
       continuing with those as post-increment/decrement operators,
       and ending with @('(E)Pr').
       So the @(':cast/call-ambig') case of this fixtype
       includes, between the components for @('X') and @('(E)Pr'),
       a list of zero or more increment and decrement operators.")
     (xdoc::p
      "The other four of the five patterns shown earlier
       are more uniform with each other.
       Again, ignore @('IncDec') initially.
       The issue here is that the operators @('*'), @('+'), @('-'), @('&')
       are both unary and binary.
       Thus, if @('X') is a type name,
       the @('* E') or @('+ E') or @('- E') or @('& E')
       is a unary expression that is the argument of the cast;
       the operator is unary.
       If instead @('X') is an expression,
       the operator is binary with operands @('(X)') and @('E').
       The cases
       @(':cast/mul-ambig'),
       @(':cast/add-ambig'),
       @(':cast/sub-ambig'), and
       @(':cast/and-ambig') of this fixtype
       capture these ambiguous situations.
       They are either casts or
       multiplications/additions/subtractions/conjunctions.
       Their first component is @('X'),
       and their last component is @('E').
       Their middle component is a list of zero or more
       increment and decrement operators that may be in between,
       i.e. @('IncDec') in the patterns shown earlier.
       Their presence maintain the ambiguity:
       if @('X') is a type name,
       they are pre-increment and pre-decrement operators
       applied to @('* E') or @('+ E') or @('- E') or @('& E');
       if @('X') is an expression,
       they are post-increment and post-decrement operators applied to @('X'),
       forming the left operand of the binary operators.")
     (xdoc::p
      "These should capture all the possible ambiguous cases.
       One needs to look, in the grammar, at what can follow the @('(X)'),
       where @('X') is an ambiguous type name or expression.
       The cases explained above lead to unresolvable syntactic ambiguities
       (which can be resolved semantically, of course).
       Other cases lead to disambiguation.
       For instance, if @('(X)') is followed by @('!'),
       then @('X') must be a type name,
       and the @('!') must start a unary expression
       that is the argument of the cast expression:
       the @('!') cannot follow an expression,
       if @('X') were an expression instead.
       But it should be apparent that this is all very tricky;
       we plan to work on a formal proof showing that
       indeed the last five cases of this fixtype
       captures all and only the ambiguous expressions
       that start with @('(X)')
       where @('X') is an ambiguous type name or expression.
       Also see how @(see parser) handles
       possibly ambiguous cast expressions.")
     (xdoc::p
      "As a GCC extension, we allow the omission of
       the `then' sub-expression of a conditional expression.
       See the ABNF grammar.")
     (xdoc::p
      "As a GCC extension, we include statement expressions,
       i.e. expressions consisting of compound statements.
       The @(':stmt') case of this fixtype includes
       the block items that comprise the compound statement.")
     (xdoc::p
      "As a GCC extension, we include calls of
       the built-in function @('__builtin_types_compatible_p').
       This is not a regular function,
       because its arguments are types names, not expressions.")
     (xdoc::p
      "As a GCC extension, we include calls of
       the built-in function @('__builtin_offsetof').
       This is not a regular function,
       because its first argument is a type name, not an expression.
       The second argument is a member designator,
       which is a restricted form of expression.")
     (xdoc::p
      "As a GCC extension, we include calls of
       the built-in function @('__builtin_va_arg').
       This is not a regular function,
       because its second argument is a type name, not an expression.
       The first argument is an expression.")
     (xdoc::p
      "As a GCC extesntion, we include
       expressions preceded by @('__extension__').
       See our ABNF grammar."))
    (:ident ((ident ident)
             (info any)))
    (:const ((const const)))
    (:string ((strings stringlit-list)))
    (:paren ((inner expr)))
    (:gensel ((control expr)
              (assocs genassoc-list)))
    (:arrsub ((arg1 expr)
              (arg2 expr)))
    (:funcall ((fun expr)
               (args expr-list)))
    (:member ((arg expr)
              (name ident)))
    (:memberp ((arg expr)
               (name ident)))
    (:complit ((type tyname)
               (elems desiniter-list)
               (final-comma bool)))
    (:unary ((op unop)
             (arg expr)
             (info any)))
    (:sizeof ((type tyname)))
    (:sizeof-ambig ((expr/tyname amb-expr/tyname)))
    (:alignof ((type tyname)
               (uscores keyword-uscores)))
    (:cast ((type tyname)
            (arg expr)))
    (:binary ((op binop)
              (arg1 expr)
              (arg2 expr)
              (info any)))
    (:cond ((test expr)
            (then expr-option)
            (else expr)))
    (:comma ((first expr)
             (next expr)))
    (:cast/call-ambig ((type/fun amb-expr/tyname)
                       (inc/dec inc/dec-op-list)
                       (arg/rest expr)))
    (:cast/mul-ambig ((type/arg1 amb-expr/tyname)
                      (inc/dec inc/dec-op-list)
                      (arg/arg2 expr)))
    (:cast/add-ambig ((type/arg1 amb-expr/tyname)
                      (inc/dec inc/dec-op-list)
                      (arg/arg2 expr)))
    (:cast/sub-ambig ((type/arg1 amb-expr/tyname)
                      (inc/dec inc/dec-op-list)
                      (arg/arg2 expr)))
    (:cast/and-ambig ((type/arg1 amb-expr/tyname)
                      (inc/dec inc/dec-op-list)
                      (arg/arg2 expr)))
    (:stmt ((items block-item-list)))
    (:tycompat ((type1 tyname)
                (type2 tyname)))
    (:offsetof ((type tyname)
                (member member-designor)))
    (:va-arg ((list expr)
              (type tyname)))
    (:extension ((expr expr)))
    :pred exprp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Expressions are defined in @(tsee expr)."))
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption expr-option
    expr
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Expressions are defined in @(tsee expr)."))
    :pred expr-optionp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod const-expr
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of constant expressions [C17:6.6] [C17:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>constant-expression</i> in the grammar in [C17].
       As in that grammar,
       it does not actually constrain the expression to be constant,
       but it may be useful to mark expressions to be constant,
       with separate predicates that enforce that."))
    ((expr expr))
    :pred const-exprp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption const-expr-option
    const-expr
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional constant expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Constant expressions are defined in @(tsee const-expr)."))
    :pred const-expr-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum genassoc
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of generic associations [C17:6.5.1.1] [C17:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>generic-association</i> in the grammar in [C17]."))
    (:type ((type tyname)
            (expr expr)))
    (:default ((expr expr)))
    :pred genassocp
    :base-case-override :default
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist genassoc-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Generic associations are defined in @(tsee genassoc).")
     (xdoc::p
      "This fixtype corresponds to <i>generic-assoc-list</i>
     in the grammar in [C17]."))
    :elt-type genassoc
    :true-listp t
    :elementp-of-nil nil
    :pred genassoc-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum member-designor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of member designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are part of calls of @('__builtin_offsetof'),
       which is a GCC extension;
       see @(tsee expr)."))
    (:ident ((ident ident)))
    (:dot ((member member-designor)
           (name ident)))
    (:sub ((member member-designor)
           (index expr)))
    :pred member-designorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type-spec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of type specifiers [C17:6.7.3] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This captures <i>type-specifier</i> in the grammar in [C17].")
     (xdoc::p
      "We model <i>atomic-type-specifier</i>
       by inlining the type name into the @(':atomic') case of this fixtype.")
     (xdoc::p
      "We make two separate cases for structures and unions,
       avoiding explicit modeling of the <i>struct-or-union</i> nonterminal.")
     (xdoc::p
      "We model <i>typedef-name</i>
       by inlining the type name into the @(':typedef') case of this fixtype.")
     (xdoc::p
      "We include the GCC extension variant keywords
       @('__signed') and @('__signed__') of @('signed').
       An indicator of which variant is included
       in the @(':signed') case of this fixtype.")
     (xdoc::p
      "We also include the GCC extension @('__int128'),
       which is a (non-standard) integer type: see "
      (xdoc::ahref
       "https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html"
       "@('https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html')")
      ". We also support the @('__int128_t') variant syntax.
       This form does not appear to be documented,
       but has been observed in real code and is accepted by GCC.")
     (xdoc::p
      "We also include the GCC extensions
       @('_Float32'),
       @('_Float32x'),
       @('_Float64'),
       @('_Float64x'),
       @('_Float128'), and
       @('_Float128x'),
       which are floating types: see "
      (xdoc::ahref
       "https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html"
       "@('https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html')")
      ".")
     (xdoc::p
      "We also include the GCC extension @('__builtin_va_list'),
       whch is a type.
       Although we did not see it in the GCC documentation,
       we encountered it in practical code,
       and we indeed verified that it is accepted as a type
       in at least an implementation of GCC in macOS.")
     (xdoc::p
      "As a GCC extension, we allow a structure type specifier with no members,
       and with an optional name; see the ABNF grammar.")
     (xdoc::p
      "As a GCC extension, we include @('typeof'),
       along with its variants @('__typeof') and @('__typeof__').
       The argument may be an expression or a type name,
       and therefore we also need to include the ambiguous possibility.")
     (xdoc::p
      "As a GCC extension, we include @('__auto_type');
       see the ABNF grammar."))
    (:void ())
    (:char ())
    (:short ())
    (:int ())
    (:long ())
    (:float ())
    (:double ())
    (:signed ((uscores keyword-uscores-p)))
    (:unsigned ())
    (:bool ())
    (:complex ())
    (:atomic ((type tyname)))
    (:struct ((spec struni-spec)))
    (:union ((spec struni-spec)))
    (:enum ((spec enumspec)))
    (:typedef ((name ident)))
    ;; GCC extensions:
    (:int128 ((uscoret bool)))
    (:float32 ())
    (:float32x ())
    (:float64 ())
    (:float64x ())
    (:float128 ())
    (:float128x ())
    (:builtin-va-list ())
    (:struct-empty ((name? ident-option)))
    (:typeof-expr ((expr expr)
                   (uscores keyword-uscores-p)))
    (:typeof-type ((type tyname)
                   (uscores keyword-uscores-p)))
    (:typeof-ambig ((expr/type amb-expr/tyname)
                    (uscores keyword-uscores-p)))
    (:auto-type ())
    :pred type-specp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum spec/qual
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of specifiers and qualifiers
            [C17:6.7.2.1] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not correspond directly
       to any nonterminal in the grammar in [C17],
       but it is useful to define <i>specifier-qualifier-list</i>:
       see @(tsee spec/qual-list).")
     (xdoc::p
      "As a GCC extension, we include attribute specifiers.
       See our ABNF grammar."))
    (:typespec ((spec type-spec)))
    (:typequal ((qual type-qual)))
    (:align ((spec align-spec)))
    (:attrib ((spec attrib-spec))) ; GCC extension
    :pred spec/qual-p
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist spec/qual-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of specifiers and qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "The fixtype of type specifiers and type qualifiers
       is defined in @(tsee spec/qual).")
     (xdoc::p
      "This fixtype corresponds to <i>specifier-qualifier-list</i>."))
    :elt-type spec/qual
    :true-listp t
    :elementp-of-nil nil
    :pred spec/qual-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum align-spec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of alignment specifiers [C17:6.7.5] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>alignment-specifier</i> in the grammar in [C17].
       The first two cases of this fixtype correspond to
       the two forms of @('_Alignas'),
       one for type names and one for constant expressions.
       The third case is for ambiguous forms")
     (xdoc::codeblock
      "_Alignas ( X )")
     (xdoc::p
      "where @('X') is, syntactically, both an expression or a type name.
       As discussed in @(tsee amb-expr/tyname),
       there is a non-trivial overlap between expressions and type names."))
    (:alignas-type ((type tyname)))
    (:alignas-expr ((expr const-expr)))
    (:alignas-ambig ((expr/type amb-expr/tyname)))
    :pred align-specp
    :base-case-override :alignas-expr
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum decl-spec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of declaration specifiers [C17:6.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not directly correspond to
       any nonterminal in the grammar in [C17],
       but it is useful to define <i>declaration-specifiers</i>
       (see @(tsee decl-spec-list)).")
     (xdoc::p
      "As GCC extensions, we include
       attribute specifiers,
       the keyword @('__stdcall'),
       and the @('__declspec') attribute syntax.
       See our ABNF grammar for details."))
    (:stoclass ((spec stor-spec)))
    (:typespec ((spec type-spec)))
    (:typequal ((qual type-qual)))
    (:function ((spec fun-spec)))
    (:align ((spec align-spec)))
    (:attrib ((spec attrib-spec))) ; GCC extension
    (:stdcall ()) ; GCC extension
    (:declspec ((arg identp))) ; GCC extension
    :pred decl-specp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist decl-spec-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "The fixtype of declaration specifiers is defined in @(tsee decl-spec).")
     (xdoc::p
      "This fixtype corresponds to <i>declaration-specifiers</i>
       in the grammar in [C17]."))
    :elt-type decl-spec
    :true-listp t
    :elementp-of-nil nil
    :pred decl-spec-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum typequal/attribspec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of type qualifiers and attribute specifiers."
    (:type ((unwrap type-qual)))
    (:attrib ((unwrap attrib-spec)))
    :pred typequal/attribspec-p
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist typequal/attribspec-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of type qualifiers and attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "Type qualifiers and attribute specifiers are defined in
       @(tsee typequal/attribspec)."))
    :elt-type typequal/attribspec
    :true-listp t
    :elementp-of-nil nil
    :pred typequal/attribspec-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist typequal/attribspec-list-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of lists of
            type qualifiers and attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "Lists of type qualifiers and attribute specifiers are defined in
       @(tsee typequal/attribspec-list)."))
    :elt-type typequal/attribspec-list
    :true-listp t
    :elementp-of-nil t
    :pred typequal/attribspec-list-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum initer
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of initializers [C17:6.7.9] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>initializer</i> in the grammar in [C17].
       The <i>initializer-list</i> is captured as
       a list (which should be non-empty) of initializers with designations
       (see @(tsee desiniter))."))
    (:single ((expr expr)))
    (:list ((elems desiniter-list)
            (final-comma bool)))
    :pred initerp
    :base-case-override :single
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption initer-option
    initer
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializers are defined in @(tsee initer)."))
    :pred initer-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod desiniter
    :short "Fixtype of initializers with optional designations
            [C17:6.7.9] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This has no direct corresponding nonterminal in the grammar in [C17],
       but it is useful to define <i>initializer-list</i>,
       which is a non-empty sequence of initializers with designations.
       An optional <i>designation</i> [C17:6.7.9] [C17:A.2.2] is captured here
       as a list of designators (see @(tsee designor)),
       where the empty list means that the designation is absent,
       while a non-empty list captures the designation,
       which has a non-empty list of designators."))
    ((designors designor-list)
     (initer initer))
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :pred desiniterp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist desiniter-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of initializers with optional designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializers with designations are defined in @(tsee desiniter).")
     (xdoc::p
      "This fixtype corresponds to <i>initializer-list</i>
       in the grammar in [C17]."))
    :elt-type desiniter
    :true-listp t
    :elementp-of-nil nil
    :pred desiniter-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum designor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of designators [C17:6.7.9] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>designator</i> in the grammar in [C17]."))
    (:sub ((index const-expr)))
    (:dot ((name ident)))
    :pred designorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist designor-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Designators are defined in @(tsee designor)."))
    :elt-type designor
    :true-listp t
    :elementp-of-nil nil
    :pred designor-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod declor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of declarators [C17:6.7.6] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>declarator</i> in the grammar in [C17].
       The optional <i>pointer</i> that precedes the <i>direct-declarator</i>
       is a sequence of stars each optionally followed by
       an optional sequence of type qualifiers and attribute specifiers.
       We model this as
       a list of lists of type qualifiers and attribute specifiers:
       the outer list corresponds to each star,
       and each inner list corresponds to
       the type qualifiers and attribute specifiers
       that immediately follow the star."))
    ((pointers typequal/attribspec-list-list)
     (direct dirdeclor))
    :pred declorp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption declor-option
    declor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Declarators are defined in @(tsee declor)."))
    :pred declor-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum dirdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of direct declarators [C17:6.7.6] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>direct-declarator</i> in the grammar in [C17].")
     (xdoc::p
      "The base case is the identifier.")
     (xdoc::p
      "We explicitly capture parenthesized declarators,
       analogously to how we also capture parenthesized expressions,
       in order to not lose concrete syntax information
       about redundant parenthesizations that may improve readability.
       This is recursive, since a declarator includes a direct declarator
       (see @(tsee declor)).")
     (xdoc::p
      "Each of the other cases starts with a direct declarator,
       followed by additional syntactic entities.
       The @(':array') case captures the first kind of array declarator,
       without @('static') and without @('*');
       the @(':array-static1') and @(':array-static2') cases
       capture the @('...[static...]') and @('...[...static...]') forms;
       and the @(':array-star') case captures the @('...[...*]') form.")
     (xdoc::p
      "In the @(':function-params') case,
       we inline <i>parameter-type-list</i>.")
     (xdoc::p
      "Grammatically, an <i>identifier-list</i>
       is also a <i>parameter-type-list</i>,
       because an identifier could be a type specifier (a @('typedef') name).
       This cannot be disambiguated purely syntactically.
       So, during parsing, we always generate the @(':function-params') case,
       which may be re-classified into the @(':function-names') case
       during post-parsing semantic analysis."))
    (:ident ((ident ident)))
    (:paren ((inner declor)))
    (:array ((declor dirdeclor)
             (qualspecs typequal/attribspec-list)
             (size? expr-option)))
    (:array-static1 ((declor dirdeclor)
                     (qualspecs typequal/attribspec-list)
                     (size expr)))
    (:array-static2 ((declor dirdeclor)
                     (qualspecs typequal/attribspec-list)
                     (size expr)))
    (:array-star ((declor dirdeclor)
                  (qualspecs typequal/attribspec-list)))
    (:function-params ((declor dirdeclor)
                       (params param-declon-list)
                       (ellipsis bool)))
    (:function-names ((declor dirdeclor)
                      (names ident-list)))
    :pred dirdeclorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod absdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of abstract declarators [C17:6.7.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>abstract-declarator</i> in the grammar in [C17].
       This fixtype is similar to @(tsee declor)
       (see that fixtype's documentation in particular
       for an explanation of the modeling of the <i>pointer</i> part),
       but the abstract direct declarator is optional.")
     (xdoc::p
      "To match the grammar, we cannot have
       both an empty list of pointers
       and an absent direct abstract declarator.
       This constraint is currently not enforced in this fixtype."))
    ((pointers typequal/attribspec-list-list)
     (direct? dirabsdeclor-option))
    :pred absdeclorp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption absdeclor-option
    absdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional abstract declarators [C17:6.7.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "Abstract declarators are defined in @(tsee absdeclor)."))
    :pred absdeclor-optionp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum dirabsdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of direct abstract declarators [C17:6.7.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>direct-abstract-declarator</i>
       in the grammar in [C17].
       This fixtype is similar to @(tsee dirdeclor),
       with the differences that
       the nested direct abstract declarators are optional,
       the @('...[*]') form has no type qualifiers just before the @('*'),
       and there is just the parameter form for functions.
       Furthermore, as explained in @(see exprs/decls/stmts),
       there is a dummy base case."))
    (:dummy-base ())
    (:paren ((inner absdeclor)))
    (:array ((declor? dirabsdeclor-option)
             (qualspecs typequal/attribspec-list)
             (size? expr-option)))
    (:array-static1 ((declor? dirabsdeclor-option)
                     (qualspecs typequal/attribspec-list)
                     (size expr)))
    (:array-static2 ((declor? dirabsdeclor-option)
                     (qualspecs typequal/attribspec-list)
                     (size expr)))
    (:array-star ((declor? dirabsdeclor-option)))
    (:function ((declor? dirabsdeclor-option)
                (params param-declon-list)
                (ellipsis bool)))
    :pred dirabsdeclorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption dirabsdeclor-option
    dirabsdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of optional direct abstract declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Direct abstract declarators are defined in @(tsee dirabsdeclor)."))
    :pred dirabsdeclor-optionp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod param-declon
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of parameter declarations [C17:6.7.6] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>parameter-declaration</i> in the grammar in [C17].
       In our abstract syntax, this is defined as consisting of
       declaration specifiers followed by a parameter declarator;
       see @(tsee param-declor) for a description and motivation
       for this notion of parameter declarator."))
    ((specs decl-spec-list)
     (declor param-declor))
    :pred param-declonp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist param-declon-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Parameter declarations are defined in @(tsee param-declon).
       This fixtype corresponds to <i>parameter-list</i>
       in the grammar in [C17]."))
    :elt-type param-declon
    :true-listp t
    :elementp-of-nil nil
    :pred param-declon-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum param-declor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of parameter declarators [C17:6.7.6] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "There is actually no notion of `parameter declarator' in [C17],
       but it is convenient to introduce in our abstract syntax,
       to factor it better.
       Our notion of parameter declarator is analogous to
       the notions of various kinds of declarators in [C17],
       which, when preceded by declaration specifiers,
       form declarations.")
     (xdoc::p
      "We define a parameter declarator as
       either a declarator or an abstract declarator or nothing.
       These are the three possibilities for what can follow
       the declaration specifiers in a parameter declaration."))
    (:nonabstract ((declor declor)))
    (:abstract ((declor absdeclor)))
    (:none ())
    (:ambig ((declor amb-declor/absdeclor)))
    :pred param-declorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod tyname
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of type names [C17:6.7.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>type-name</i> in the grammar in [C17].")
     (xdoc::p
      "Type names may be accompanied by some additional information,
       such as the type calculated during validation."))
    ((specquals spec/qual-list)
     (declor? absdeclor-option)
     (info any))
    :pred tynamep
    :measure (two-nats-measure (acl2-count x) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod struni-spec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of structure or union specifiers [C17:6.7.2.1] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-or-union-specifier</i>
       in the grammar in [C17], but without the initial <i>struct-or-union</i>.
       The only use of this fixtype is in @(tsee type-spec),
       where we have two separate cases for structures and unions.")
     (xdoc::p
      "This fixtype is a little broader than the grammar,
       because it allows an absent name and no members.
       But this definition is simpler,
       and the disallowed case can be ruled out
       via predicates over the abstract syntax.")
     (xdoc::p
      "This fixtype does not cover structure types with no members,
       which is a GCC extension;
       this is covered as a separate case in @(tsee type-spec)."))
    ((name? ident-option)
     (members structdecl-list))
    :pred struni-specp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum structdecl
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of structure declarations [C17:6.7.2.1] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-declaration</i> in the grammar of [C17].
       Despite its name in the grammar and in this fixtype,
       this applies to both structures and unions;
       in fact, it is not a declaration of a structure,
       but instead it is a declaration of a member of a structure or union.
       So something like <i>member-declaration</i>
       would be a better name for this grammar nonterminal,
       but our fixtype name reflects the current grammar.")
     (xdoc::p
      "As a GCC extension, we include the possibility that
       a member declaration starts with
       the @('__extension__') GCC keyword.
       We model that as a boolean that says whether
       that keyword is present or absent.")
     (xdoc::p
      "As a GCC extension, we include
       a possibly empty list of attribute specifiers,
       which come after the declarator (cf. the grammar).")
     (xdoc::p
      "As explained in our ABNF grammar,
       we also include an empty external declaration,
       which syntactically consists of a semicolon."))
    (:member ((extension bool) ; GCC extension
              (specqual spec/qual-list)
              (declor structdeclor-list)
              (attrib attrib-spec-list))) ; GCC extension
    (:statassert ((unwrap statassert)))
    (:empty ()) ; GCC extension
    :pred structdeclp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist structdecl-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of structure declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Structure declarations are defined in @(tsee structdecl).
       This fixtype corresponds to <i>struct-declaration-list</i>
       in the grammar in [C17]."))
    :elt-type structdecl
    :true-listp t
    :elementp-of-nil nil
    :pred structdecl-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod structdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of structure declarators [C17:6.7.2.1] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-declarator</i> in the grammar in [C17].
       This is part of structure declarations,
       so as discussed in @(tsee structdecl)
       arguably a better name would be `member declarators'.")
     (xdoc::p
      "To make this definition simpler,
       we allow an absent declarator and an absent expression,
       even though this is disallowed in the concrete syntax."))
    ((declor? declor-option)
     (expr? const-expr-option))
    :pred structdeclorp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist structdeclor-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Structure declarators are defined in @(tsee structdeclor).
       This fixtype corresponds to <i>struct-declarator-list</i>
       in the grammar in [C17]."))
    :elt-type structdeclor
    :true-listp t
    :elementp-of-nil nil
    :pred structdeclor-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod enumspec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of enumeration specifiers [C17:6.7.2.2] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>enum-specifier</i> in the grammar in [C17].")
     (xdoc::p
      "To make this definition simpler,
       we allow an absent name and no enumerators,
       even though this is disallowed in the concrete syntax."))
    ((name ident-option)
     (list enumer-list)
     (final-comma bool))
    :pred enumspecp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod enumer
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of enumerators [C17:6.7.2.2] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>enumerator</i> in the grammar in [C17]."))
    ((name ident)
     (value const-expr-option))
    :pred enumerp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist enumer-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Enumerators are defined in @(tsee enumer).
       This fixtype corresponds to <i>enumerator-list</i>
       in the grammar in [C17]."))
    :elt-type enumer
    :true-listp t
    :elementp-of-nil nil
    :pred enumer-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod statassert
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of static assertion declarations [C17:6.7.10] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>static_assert-declaration</i>
       in the grammar in [C17].")
     (xdoc::p
      "We use a list of string literals,
       which should be non-empty, but we do not capture this constraint.
       This mirrors the ABNF grammar:
       this way, we preserve the information about adjacent string literals."))
    ((test const-expr)
     (message stringlit-list))
    :pred statassertp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum attrib
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of GCC attributes."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is part of the "
      (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Attribute-Syntax.html"
                   "GCC extension for attributes")
      ". For now we only model the older @('__attribute__') syntax.")
     (xdoc::p
      "The documentation lists three kinds of attributes:
       empty, names, and names with parameters.
       For now we only model the latter two kinds.
       The documentation lists three kinds of parameters
       (which presumably refer to the whole collection of parameters
       of a single attribute with parameters,
       not to a single parameter,
       because otherwise it would be unclear what it means,
       for a single parameter, to be a comma-separated list of things,
       given that parameters are themselves comma-separated.
       However, the three kinds of (lists of) parameters overlap syntactically:
       an instance of the first kind,
       i.e. an identifier,
       could be also an expression,
       and thus could be also an instance of the third kind;
       an instance of the second kind,
       i.e. an identifier followed by one or more expressions,
       could be also just a list of two or more expressions,
       and thus an instance of the third kind.
       Thus, we simply define an attribute with parameter as
       containing a list of zero or more expressions,
       which covers all three kinds of parameters.")
     (xdoc::p
      "Note the distinction between an attribute that is just a name,
       and an attributed that consists of a name and zero parameters:
       in concrete syntax, the latter would include open and closed parentheses,
       without anything in between (except white space or comments)."))
    (:name-only ((name attrib-name)))
    (:name-param ((name attrib-name)
                  (param expr-list)))
    :pred attribp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist attrib-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of GCC attributes."
    :long
    (xdoc::topstring
     (xdoc::p
      "GCC attributes are defined in @(tsee attrib)."))
    :elt-type attrib
    :true-listp t
    :elementp-of-nil nil
    :pred attrib-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod attrib-spec
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of GCC attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is part of the "
      (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Attribute-Syntax.html"
                   "GCC extension for attributes")
      ". For now we only model the older @('__attribute__') syntax.")
     (xdoc::p
      "We wrap a possibly empty list of attributes,
       and we include a flag to distinguish
       between @('__attribute') and @('__attribute__').
       The flag is @('t') for the second variant (i.e. more underscores),
       @('nil') for the first variant (i.e. fewer underscores)."))
    ((uscores bool)
     (attribs attrib-list))
    :pred attrib-specp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist attrib-spec-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of GCC attribute specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "GCC attribute specifiers are defined in @(tsee attrib-spec)."))
    :elt-type attrib-spec
    :true-listp t
    :elementp-of-nil nil
    :pred attrib-spec-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod initdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of initializer declarators [C17:6.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "As GCC extensions, we allow
       an optional assembler name specifier
       and a possibly empty of attribute specifiers.
       See the ABNF grammar."))
    ((declor declor)
     (asm? asm-name-spec-option)
     (attribs attrib-spec-list)
     (init? initer-option))
    :pred initdeclorp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist initdeclor-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializer declarators are defined in @(tsee initdeclor).
       This fixtype corresponds to <i>init-declarator-list</i>
       in the grammar in [C17]."))
    :elt-type initdeclor
    :true-listp t
    :elementp-of-nil nil
    :pred initdeclor-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum decl
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of declarations [C17:6.7] [C17:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "As a GCC extension,
       we include the possibility that
       the declaration starts with the @('__extension__') GCC keyword.
       We model this as a boolean saying whether
       the keyword is present or absent."))
    (:decl ((extension bool)
            (specs decl-spec-list)
            (init initdeclor-list)))
    (:statassert ((unwrap statassert)))
    :pred declp
    :base-case-override :statassert
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist decl-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Declarations are defined in @(tsee decl).
       This fixtype corresponds to <i>declaration-list</i>
       in the grammar in [C17],
       which is under external definitions [C17:6.9.1] [C17:A.2.4]."))
    :elt-type decl
    :true-listp t
    :elementp-of-nil nil
    :pred decl-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum label
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of labels [C17:6.8.1] [C17:A.2.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not directly correspond to
       any nonterminal in the grammar in [C17],
       but it captures the three initial portions of
       the grammar rule for <i>labeled-statement</i>.
       There are three possible kinds of labels:
       names (identifiers),
       constant expressions in @('case'),
       and the @('default') label.
       As a GCC extension,
       we allow an optional additional constant expression in @('case'),
       to capture ranges (see ABNF grammar)."))
    (:name ((unwrap ident)))
    (:casexpr ((expr const-expr)
               (range? const-expr-option)))
    (:default ())
    :pred labelp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod asm-output
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of assembler output operands."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are a GCC extension; see ABNF grammar."))
    ((name ident-option)
     (constraint stringlit-list)
     (lvalue expr))
    :pred asm-outputp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist asm-output-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of assembler output operands."
    :long
    (xdoc::topstring
     (xdoc::p
      "Assembler output operands are defined in @(tsee asm-output)."))
    :elt-type asm-output
    :true-listp t
    :elementp-of-nil nil
    :pred asm-output-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod asm-input
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of assembler input operands."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are a GCC extension; see ABNF grammar."))
    ((name ident-option)
     (constraint stringlit-list)
     (rvalue expr))
    :pred asm-inputp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist asm-input-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of assembler input operands."
    :long
    (xdoc::topstring
     (xdoc::p
      "Assembler input operands are defined in @(tsee asm-input)."))
    :elt-type asm-input
    :true-listp t
    :elementp-of-nil nil
    :pred asm-input-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod asm-stmt
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of assembler statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is a GCC extension.
       Our abstract syntax of assembler statements
       is based on their definition in the ABNF grammar,
       which is in turn derived from the GCC documentation.
       As in the grammar,
       we unify the representation of basic and extended assembler statements.
       The grammar contains four nested optional parts (output operands etc.);
       the nesting is such that any prefix of the sequence of four parts,
       ranging from no parts to all four parts, may be present.
       In the abstract syntax, we include a component
       that counts the number of parts, or equivalently the number of colons,
       since each part starts with a colon.
       Then each part consists of a list of things, four lists, one per part.
       If @('num-colons') is less than 4,
       the fourth list must be empty;
       if @('num-colons') is less than 3,
       the fourth and third lists must be empty;
       and so on, but we do not explicitly capture
       these constraints in the fixtype."))
    ((uscores keyword-uscores)
     (quals asm-qual-list)
     (template stringlit-list)
     (num-colons nat)
     (outputs asm-output-list)
     (inputs asm-input-list)
     (clobbers asm-clobber-list)
     (labels ident-list))
    :pred asm-stmtp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum stmt
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of statements [C17:6.8] [C17:A.2.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>statement</i> in the grammar in [C17].")
     (xdoc::p
      "We inline
       <i>labeled-stament</i>,
       <i>expression-statement</i>,
       <i>selection-statement</i>,
       <i>iteration-statement</i>, and
       <i>jump-statement</i>.")
     (xdoc::p
      "For labeled statements,
       we use @(tsee label) to factor the three kinds of labels.")
     (xdoc::p
      "There are two forms of @('for') loops:
       one where the initialization part is an (optional) expression,
       and one where the initialization part is a declaration.
       There is also a third ambiguous form,
       which applies when the initialization part could be
       either an expression or a declaration, syntactically:
       this is captured exactly by @(tsee amb-decl/stmt),
       because the statement in an ambiguous declaration or statement
       is a statement expression,
       which is exactly what
       the initialization part of a @('for') looks like,
       when it is an expression.")
     (xdoc::p
      "As a GCC extension, we include assembler statements."))
    (:labeled ((label label)
               (stmt stmt)))
    (:compound ((items block-item-list)))
    (:expr ((expr? expr-option)
            (info any)))
    (:if ((test expr)
          (then stmt)))
    (:ifelse ((test expr)
              (then stmt)
              (else stmt)))
    (:switch ((target expr)
              (body stmt)))
    (:while ((test expr)
             (body stmt)))
    (:dowhile ((body stmt)
               (test expr)))
    (:for-expr ((init expr-option)
                (test expr-option)
                (next expr-option)
                (body stmt)))
    (:for-decl ((init decl)
                (test expr-option)
                (next expr-option)
                (body stmt)))
    (:for-ambig ((init amb-decl/stmt)
                 (test expr-option)
                 (next expr-option)
                 (body stmt)))
    (:goto ((label ident)))
    (:continue ())
    (:break ())
    (:return ((expr? expr-option)
              (info any)))
    (:asm ((unwrap asm-stmt)))
    :pred stmtp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum block-item
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of block items [C17:6.8.2] [C17:A.2.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>block-item</i> in the grammar in [C17].")
     (xdoc::p
      "We also include a case for an ambiguous declaration or statement;
       see @(tsee amb-decl/stmt)."))
    (:decl ((unwrap decl)))
    (:stmt ((stmt stmt)
            (info any)))
    (:ambig ((unwrap amb-decl/stmt)))
    :pred block-itemp
    :base-case-override :stmt
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist block-item-list
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of lists of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "Block items are defined in @(tsee block-item).
       This fixtype corresponds to <i>block-item-list</i>
       in the grammar in [C17]."))
    :elt-type block-item
    :true-listp t
    :elementp-of-nil nil
    :pred block-item-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod amb-expr/tyname
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of ambiguous expressions or type names."
    :long
    (xdoc::topstring
     (xdoc::p
      "Certain parts of the syntax may be either expressions or type names.
       An example is the argument of @('sizeof'), which is followed by
       either a parenthesized type name or a parenthesized expression
       (it can be also followed by a non-parenthesized expression,
       but in that case there is no ambiguity).")
     (xdoc::p
      "The syntactic overlap between expressions and type names is complex.
       The simplest case is a single identifier @('I'),
       which can be either a variable (which is an expression)
       or a @('typedef') name
       (which is a type specifier,
       and thus a type name without abstract declarator).
       But also @('I(I1)') is ambiguous, if @('I1') is also an identifier:
       it could be either a function call (which is an expression),
       or a @('typedef') name followed by a function abstract declarator,
       in which case @('I1') is a parameter declaration
       consisting of a @('typedef') name @('I1').
       Things can be nested: @('I(I1(I2(...(In)...)))').
       It is also possible to have multiple arguments or parameters,
       e.g. @('I(I1,I2)'), or things can be nested more deeply.
       There are also cases involving square brackets, such as
       @('I[E]'), where @('I') is an identifier and @('E') is an expression:
       this can be an array subscripting expression,
       or a @('typedef') name @('I') followed by an array abstract declarator.")
     (xdoc::p
      "It may take a bit of work to accurately characterize
       the syntactic ``intersection'' of expressions and type names.
       Therefore, at least for now, we introduce a fixtype to capture
       the notiion of an ambiguous expression or type name.
       A value of this fixtype consists of both an expression and a type name:
       the idea is that they are the same in concrete syntax,
       although there is no explicit requirement in this fixtype.
       Assuming that this requirement is met,
       a value of this fixtype provides the two possible interpretations,
       the expression and the type name (both in abstract syntax, of course)."))
    ((expr expr)
     (tyname tyname))
    :pred amb-expr/tyname-p
    :measure (two-nats-measure (acl2-count x) 5))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod amb-declor/absdeclor
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of ambiguous declarators or abstract declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "A parameter declaration may include, after the declaration specifiers,
       either a declarator or an abstract declarator (or also nothing).
       Syntactically,
       there is a complex overlap between declarators and abstract declarators.
       For instance, if @('I') is an identifier, @('(I)') could be
       either a direct declarator for the parenthesized identifier
       or a function abstract declarator
       where @('I') is a type specifier for the (one) parameter.
       But this is just a simple example:
       there are infinite overlapping constructs,
       e.g. obtained by adding array and function declarator parts to @('(I)'),
       but not only those.")
     (xdoc::p
      "So here, analogously to @(tsee amb-expr/tyname),
       we introduce a fixtype to capture constructs that, syntactically,
       are both declarators and abstract declarators.
       The two components of this fixtype should be the same in concrete syntax,
       but we do not enforce that in the fixtype."))
    ((declor declor)
     (absdeclor absdeclor))
    :pred amb-declor/absdeclor-p
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod amb-decl/stmt
    :parents (abstract-syntax-trees exprs/decls/stmts)
    :short "Fixtype of ambiguous declarations or statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "A block item may be a declaration or a statement,
       but there is a complex syntactic overlap
       between declarations and statements, specifically expression statements.
       For instance, if @('I1'), ..., @('In') are identifiers,
       @('I1(I2(...(In)...));') could be either a declaration or a statement.
       It is a declaration if @('I1') is a type specifier (a @('typedef') name)
       and @('(I2(...(In)...))') is a declarator of @('I2'),
       which is a function with a parameter @('I3'),
       which is a function with a parameter @('I4'),
       and so on;
       here @('I3'), @('I4'), etc. are type specifiers (@('typedef') names).
       It is instead an expression statement if
       @('I1') is a function, called with argument @('I2(...(In)...)'),
       which is itself a function call, and so on.
       There are also other, more complex patterns,
       for example similar to the ones above
       but with multiple function arguments.")
     (xdoc::p
      "So, similarly to
       @(tsee amb-expr/tyname) and @(tsee amb-declor/absdeclor),
       here we define a fixtype of ambiguous declarations or statements,
       which contain both the declaration and the expression
       (since the only ambiguity is with expression statements).
     These two components should look the same in concrete syntax,
       but we do not enforce that in this fixtype definition."))
    ((decl decl)
     (stmt expr))
    :pred amb-decl/stmt-p
    :measure (two-nats-measure (acl2-count x) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  (in-theory (disable (:e label-default)
                      (:e stmt-continue)
                      (:e stmt-break))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-spec-option
  type-spec
  :short "Fixtype of optional type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type specifiers are defined in @(tsee type-spec)."))
  :pred type-spec-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-spec-list
  :short "Fixtype of lists of type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type specifiers are defined in @(tsee type-spec)."))
  :elt-type type-spec
  :true-listp t
  :elementp-of-nil nil
  :pred type-spec-listp

  ///

  (defruled type-spec-listp-of-remove1-equal
    (implies (type-spec-listp tyspecs)
             (type-spec-listp (remove1-equal tyspec tyspecs)))
    :induct t
    :enable remove1-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expr/tyname
  :short "Fixtype of expressions or type names."
  (:expr ((unwrap expr)))
  (:tyname ((unwrap tyname)))
  :pred expr/tyname-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum declor/absdeclor
  :short "Fixtype of declarators or abstract declarators."
  (:declor ((unwrap declor)))
  (:absdeclor ((unwrap absdeclor)))
  :pred declor/absdeclor-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum decl/stmt
  :short "Fixtype of declarations or (expression) statements."
  (:decl ((unwrap decl)))
  (:stmt ((unwrap expr)))
  :pred decl/stmt-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum amb?-expr/tyname
  :short "Fixtype of possibly ambiguous expressions or type names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the difference between this fixtype,
     with a question mark in @('amb?'),
     and the fixtype @(tsee amb-expr/tyname).
     The latter captures definitely ambiguous constructs
     that may be expressions or type names.
     In contrast, this fixtype includes constructs that are
     either just expressions, or just type names, or ambiguous ones."))
  (:expr ((unwrap expr)))
  (:tyname ((unwrap tyname)))
  (:ambig ((unwrap amb-expr/tyname)))
  :pred amb?-expr/tyname-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum amb?-declor/absdeclor
  :short "Fixtype of possibly ambiguous declarators or abstract declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the difference between this fixtype,
     with a question mark in @('amb?'),
     and the fixtype @(tsee amb-declor/absdeclor).
     The latter captures definitely ambiguous constructs
     that may be declarators or abstract declarators.
     In contrast, this fixtype includes constructs that are
     either just declarators,
     or just abstract declarators,
     or ambiguous ones."))
  (:declor ((unwrap declor)))
  (:absdeclor ((unwrap absdeclor)))
  (:ambig ((unwrap amb-declor/absdeclor)))
  :pred amb?-declor/absdeclor-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum amb?-decl/stmt
  :short "Fixtype of possibly ambiguous declarations or statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to
     @(tsee amb?-expr/tyname) and @(tsee amb?-declor/absdeclor).
     It captures the possibilities of
     a declaration,
     an (expression) statement,
     or an ambiguous declaration or statements."))
  (:decl ((unwrap decl)))
  (:stmt ((unwrap expr)))
  (:ambig ((unwrap amb-decl/stmt)))
  :pred amb?-decl/stmt-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef
  :short "Fixtype of function definitions [C17:6.9.1] [C17:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>function-definition</i> in the grammar in [C17].
     The grammar constrains the function body to be a compound statement;
     in this fixtype we capture that restriction by using a list of block items,
     which the compound statement consists of.")
   (xdoc::p
    "As a GCC extension,
     we include the possibility that
     the function definition starts with the @('__extension__') GCC keyword.
     We model this as a boolean saying whether
     the keyword is present or absent.")
   (xdoc::p
    "We also allow an optional assembler name specifier
     and zero or more attribute specifiers,
     as GCC extensions;
     see the ABNF grammar."))
  ((extension bool) ; GCC extension
   (spec decl-spec-list)
   (declor declor)
   (asm? asm-name-spec-option) ; GCC extension
   (attribs attrib-spec-list) ; GCC extension
   (decls decl-list)
   (body block-item-list))
  :pred fundefp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fundef-option
  fundef
  :short "Fixtype of optional function definitions."
  :long
  (xdoc::topstring
    (xdoc::p
      "Function definitions are defined in @(tsee fundef)."))
  :pred fundef-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum extdecl
  :short "Fixtype of external declarations [C17:6.9] [C17:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>external-declaration</i> in the grammar in [C17].")
   (xdoc::p
    "As explained in our ABNF grammar,
     we also include an empty external declaration,
     which syntactically consists of a semicolon.")
   (xdoc::p
    "As a GCC extension, we also allow an assembler statement.
     See the ABNF grammar."))
  (:fundef ((unwrap fundef)))
  (:decl ((unwrap decl)))
  (:empty ()) ; GCC extension
  (:asm ((unwrap asm-stmt))) ; GCC extension
  :pred extdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist extdecl-list
  :short "Fixtype of lists of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "External declarations are defined in @(tsee extdecl).
     This fixtype corresponds to <i>external-declaration-list</i>
     in the grammar in [C17]."))
  :elt-type extdecl
  :true-listp t
  :elementp-of-nil nil
  :pred extdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit
  :short "Fixtype of translation units [C17:6.9] [C17:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>translation-unit</i> in the grammar in [C17].")
   (xdoc::p
    "A translation unit consists of a list of external declarations.
     We also add a slot with additional information, e.g. from validation."))
  ((decls extdecl-list)
   (info any))
  :pred transunitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap filepath-transunit-map
  :short "Fixtype of omaps from file paths to translation units."
  :key-type filepath
  :val-type transunit
  :pred filepath-transunit-mapp
  ///

  (defrule filepath-setp-of-keys-when-filepath-transunit-mapp
    (implies (filepath-transunit-mapp map)
             (filepath-setp (omap::keys map)))
    :induct t
    :enable omap::keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit-ensemble
  :short "Fixtype of ensembles of translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion has no explicit counterpart in [C17],
     but it is useful to represent, in the abstract syntax,
     a collection of translation units that form
     a C program or library or other component.
     Since translation units are contained in files,
     it is natural to view a translation unit ensemble
     as a collection of (parsed) files.
     Since @(tsee fileset) models a collection of files
     as a map from file paths to file data (bytes),
     we use a finite map from file paths to translation units
     to model ensembles in the abstract syntax.")
   (xdoc::p
    "Currently we do not model preprocessing constructs in our abstract syntax,
     and so a translation unit as formalized in @(tsee transunit)
     corresponds exactly to the notion of translation unit in [C17].
     As we add support for preprocessing constructs,
     our translation units will be more like something in between
     proper traslation units and preprocessing translation units.
     The notion of file set as formalized here will still apply to that case,
     with some elements of the ensembles
     that may be headers instead of source files."))
  ((unwrap filepath-transunit-map))
  :pred transunit-ensemblep)
