; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")

(include-book "kestrel/fty/dec-digit-char-list" :dir :system)
(include-book "kestrel/fty/hex-digit-char-list" :dir :system)
(include-book "kestrel/fty/oct-digit-char-list" :dir :system)
(include-book "kestrel/std/util/defirrelevant" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (syntax-for-tools)
  :short "An abstract syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see syntax-for-tools) for background.")
   (xdoc::p
    "We define fixtypes for constructs that closely correspond to
     the grammar in [C], which is summarized in [C:A].
     For now we cover all the constructs after preprocessing,
     but we plan to add some preprocessing constructs.")
   (xdoc::p
    "According to the rationale explained in @(see syntax-for-tools),
     here we capture much of the information from the concrete syntax,
     e.g. the distinction between
     the @('0x') and @('0X') hexadecimal prefixes.")
   (xdoc::p
    "We try and pick short yet clear names for these fixtypes,
     so that tools' code manipulating them can be a bit more more compact.
     While the grammar in [C]
     uses the `hexadecimal' and `binary' qualifications
     for certain hexadecimal and binary entities
     but uses no qualifications for certain decimal entities,
     our fixtype names are more symmetric,
     using @('dec') and @('hex') and @('bin') qualifiers
     for certain ``parallel'' entities.")
   (xdoc::p
    "Some library fixtypes already correspond to
     certain nonterminals in the grammar in [C]
     and are thus not defined here, but just used:")
   (xdoc::ul
    (xdoc::li
     "The fixtype @(tsee dec-digit-char-list) corresponds to
      <i>digit-sequence</i> in [C:6.4.4.2] [C:A.1.5].")
    (xdoc::li
     "The fixtype @(tsee hex-digit-char-list) corresponds to
      <i>hexadecimal-digit-sequence</i> in [C:6.4.4.2] [C:A.1.5].")
    (xdoc::li
     "The fixtypes "
     (xdoc::seetopic "fty::basetypes" "@('nat')")
     " and @(tsee nat-list)
      correspond to
      <i>c-char</i> and <i>c-char-sequence</i> in [C:6.4.4.4] [C:A.1.5],
      as well as to
      <i>s-char</i> and <i>s-char-sequence</i> in [C:6.4.5] [C:A.1.6]."))
   (xdoc::p
    "The @('...-list') fixtypes are slightly more general than
     <i>...-sequence</i> nonterminals in the grammar in [C],
     because the former include the empty list,
     while the latter only include non-empty sequences.
     The same applies to other fixtypes defined here:
     while the grammar in [C] forces
     certain sequences of entities to be non-empty,
     our corresponding fixtypes include the empty list.
     This makes things a bit simpler,
     partly because currently @(tsee fty::deflist)
     generates conflicting theorems if used
     both with @(':non-emptyp t') and with @(':non-emptyp nil')
     (although this could be remedied).
     It is fine (and common) for the abstract syntax
     to be more general than the concrete syntax.
     Restrictions on well-formed code can be formulated
     via separate predicates on the abstract syntax.
     The grammar in [C] does not capture many static constraints anyhow.")
   (xdoc::p
    "The use of natural numbers to represent <i>c-char</i> and <i>s-char</i>
     in character constants and string literals is motivated by
     the fact that we commit to Unicode characters,
     even though [C] prescribes no specific source character set [C:5.2.1].
     These days, Unicode should be sufficiently general;
     note that ASCII is a subset of Unicode.
     Thus, the natural numbers represent Unicode code points,
     which include ASCII codes as a subset.
     Although natural numbers are more general that Unicode code points,
     and also more general than <i>c-char</i> and <i>s-char</i>,
     it is fine for abstract syntax to be more general than concrete syntax."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident
  :short "Fixtype of identifiers [C:6.4.2] [C:A.1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>identifier</i> in the grammar in [C].
     In this abstract syntax, we allow any ACL2 values as C identifiers.
     We wrap these arbitrary values into a one-component product fixtype
     so that we can more easily distinguish identifiers from other things.")
   (xdoc::p
    "Allowing arbitrary values as identifiers provides flexibility.
     For instance, a transformation on C code could introduce
     multiple versions of certain identifiers, indexed by numbers,
     in which case we could use pair consisting of
     the original identifiers and the indices.")
   (xdoc::p
    "We plan to define, separately,
     predicates that restrict identifiers to certain forms,
     used for parsing, pretty-printing, transformations, etc.
     Restrictions are needed to pretty-print this abstract syntax
     into a form where identifiers respect the restrictions in [C];
     in addition, parsing code compliant to [C]
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lsuffix
  :short "Fixtype of length suffixes [C:6.4.4.1] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>long-suffix</i> and <i>long-long-suffix</i>
     in the grammar in [C].
     We use the term `length suffix' here,
     but the grammar in [C] does not use that term,
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
  :short "Fixtype of unsigned suffixes [C:6.4.41] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>unsigned-suffix</i> in the grammar in [C].
     This captures the two possible suffixes @('u') and @('U')."))
  (:locase-u ())
  (:upcase-u ())
  :pred usuffixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum isuffix
  :short "Fixtype of integer suffixes [C:6.4.4.1] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>integer-suffix</i> in the grammar in [C].
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
  :short "Fixtype of hexadecimal prefixes [C:6.4.4.1] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-prefix</i> in the grammar in [C].
     This captures the two possible prefixes @('0x') and @('0X')."))
  (:locase-0x ())
  (:upcase-0x ())
  :pred hprefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec/oct/hex-const
  :short "Fixtype of decimal, octal, and hexadecimal constants
          [C:6.4.4.1] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures
     <i>decimal-constant</i>,
     <i>octal-constant</i>, and
     <i>hexadecimal-constant</i>
     in the grammar in [C].
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
     and thus there is a unique sequence of digits
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
     corresponds, in the grammar in [C],
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
  :short "Fixtype of integer constants [C:6.4.4.1] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>integer-constant</i> in the grammar in [C].
     As mentioned in @(tsee dec/oct/hex-const),
     our fixtypes are factored slightly differently.
     An integer constant consists of a decimal, octal, or hexadecimal constant,
     and of an optional integer suffix."))
  ((dec/oct/hex dec/oct/hex-const)
   (suffix isuffix-option))
  :pred iconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fsuffix
  :short "Fixtype of floating suffixes [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>floating-suffix</i> in the grammar in [C].
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
  :short "Fixtype of signs [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>sign</i> in the grammar in [C].
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
  :short "Fixtype of decimal exponent prefixes [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the @('e') or @('E') prefix
     in <i>exponent-part</i> in the grammar in [C]."))
  (:locase-e ())
  (:upcase-e ())
  :pred dec-expo-prefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bin-expo-prefix
  :short "Fixtype of binary exponent prefixes [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the @('p') or @('P') prefix
     in <i>binary-exponent-part</i> in the grammar in [C]."))
  (:locase-p ())
  (:upcase-p ())
  :pred bin-expo-prefixp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod dec-expo
  :short "Fixtype of decimal exponents [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>exponent-part</i> in the grammar in [C].
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
  :short "Fixtype of binary exponents [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>binary-exponent-part</i> in the grammar in [C].
     It consists of a prefix,
     an optional sign,
     and a list of (decimal) digits (which should be non-empty).
     The digits are decimal, not binary or hexadecimal;
     but the implicit base of the exponent is binary [C:6.4.4.2/3]."))
  ((prefix bin-expo-prefix)
   (sign? sign-option)
   (digits dec-digit-char-list))
  :pred bin-expop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec-frac-const
  :short "Fixtype of decimal fractional constants [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>fractional-constant</i>
     in the grammar in [C].
     It covers the three possibilities of
     (i) the point in the middle (with a left and right digit sequence),
     (ii) the point at the start (with just a right digit sequence), and
     (iii) the point at the end (with just a left digit sequence).
     This is structured slightly differently and more symmetrically
     than in the grammar in [C]."))
  (:middle ((left dec-digit-char-list)
            (right dec-digit-char-list)))
  (:start ((right dec-digit-char-list)))
  (:end ((left dec-digit-char-list)))
  :pred dec-frac-constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hex-frac-const
  :short "Fixtype of hexadecimal fractional constants [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-fractional-constant</i>
     in the grammar in [C].
     It covers the three possibilities of
     (i) the point in the middle (with a left and right digit sequence),
     (ii) the point at the start (with just a right digit sequence), and
     (iii) the point at the end (with just a left digit sequence).
     This is structured slightly differently and more symmetrically
     than in the grammar in [C]."))
  (:middle ((left hex-digit-char-list)
            (right hex-digit-char-list)))
  (:start ((right hex-digit-char-list)))
  (:end ((left hex-digit-char-list)))
  :pred hex-frac-constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum dec-core-fconst
  :short "Fixtype of decimal core floating constants [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>decimal-floating-constant</i>
     in the grammar in [C], but without the optional suffix,
     which is what we mean by `core' in the name of this fixtype
     (we factor things slightly differently in our fixtypes;
     see @(tsee fconst)).
     This covers the three possibilities of
     (i) a (decimal) fractional significand without an exponent,
     (ii) a (decimal) fractional significand with a (decimal) exponent, and
     (iii) a (decimal) integer significand with a (decimal) exponent."))
  (:frac ((significand dec-frac-const)))
  (:frac-expo ((significand dec-frac-const)
               (expo dec-expo)))
  (:int-expo ((significand dec-digit-char-list)
              (expo dec-expo)))
  :pred dec-core-fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum hex-core-fconst
  :short "Fixtype of hexadecimal core floating constants [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hexadecimal-floating-constant</i>
     in the grammar in [C], but without the prefix and the optional suffix,
     which is what we mean by `core' in the name of this fixtype
     (we factor things slightly differently in our fixtypes;
     see @(tsee fconst)).
     This covers the two possibilities of
     (i) a (hexadecimal) fractional significand with a (binary) exponent and
     (iii) a (hexadecimal integer significand with a (binary) exponent."))
  (:frac-expo ((significand hex-frac-const)
               (expo bin-expo)))
  (:int-expo ((significand hex-digit-char-list)
              (expo bin-expop)))
  :pred hex-core-fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fconst
  :short "Fixtype of floating constants [C:6.4.4.2] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>floating-constant</i> in the grammar in [C].
     As mentioned in @(tsee dec-core-fconst) and @(tsee hex-core-fconst),
     we factor things a bit differently in our fixtypes,
     so here we add the prefixes and suffixes as appropriate."))
  (:dec ((core dec-core-fconst)
         (suffix fsuffix-option)))
  (:hex ((prefix hprefix)
         (core hex-core-fconst)
         (suffix fsuffix-option)))
  :pred fconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum simple-escape
  :short "Fixtype of simple escape sequences [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>simple-escape-sequence</i> in the grammar in [C].
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
     @('\\v')."))
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
  :pred simple-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum oct-escape
  :short "Fixtype of octal escape sequences [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>octal-escape-sequence</i> in the grammar in [C].
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
  :short "Fixtype of quadruples of hexadecimal digits [C:6.4.3] [C:A.1.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>hex-quad</i> in the grammar in [C]."))
  ((1st hex-digit-char)
   (2nd hex-digit-char)
   (3rd hex-digit-char)
   (4th hex-digit-char))
  :pred hex-quad-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum univ-char-name
  :short "Fixtype of universal character names [C:6.4.3] [C:A.1.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>universal-character-name</i>
     in the grammar in [C].
     The two cases of this fixtype correspond to
     @('\\uXXXX') and @('\\UXXXXYYYY')."))
  (:locase-u ((quad hex-quad)))
  (:upcase-u ((quad1 hex-quad)
              (quad2 hex-quad)))
  :pred univ-char-name-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum escape
  :short "Fixtype of escape sequences [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>escape-sequence</i> in the grammar in [C].
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
          usable in character constants [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>c-char</i> in the grammar in [C].")
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
          usable in character constants [C:6.4.4.4] [C:A.1.5]."
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
  :short "Fixtype of prefixes of character constants [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @('L'), @('u'), and @('U') prefixes
     in <i>character-constant</i> in the grammar in [C]."))
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
  :short "Fixtype of character constants [C:6.4.4.4] [C:A.1.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>character-constant</i> in the grammar in [C]."))
  ((prefix cprefix-option)
   (cchars c-char-list))
  :pred cconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum const
  :short "Fixtype of constants [C:6.4.4] [C:A.1.5]."
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
          usable in string literals [C:6.4.5] [C:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>s-char</i> in the grammar in [C].")
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
          usable in string literals [C:6.4.5] [C:A.1.6]."
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
  :short "Fixtype of encoding prefixes [C:6.4.5] [C:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>encoding-prexif</i> in the grammar in [C]."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stringlit
  :short "Fixtype of string literals [C:6.4.5] [C:A.1.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>string-literal</i> in the grammar in [C].")
   (xdoc::p
    "The list of natural numbers corresponds to <i>s-char-sequence</i>.
     As explained in @(see abstract-syntax),
     these natural numbers represent Unicode code points.
     We do not capture here the requirement that these characters
     are not new-line, backslash, and double quote."))
  ((prefix eprefix-option)
   (schars s-char-list))
  :pred stringlitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unop
  :short "Fixtype of unary operators
          [C:6.5.3] [C:6.5.2] [C:A.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>unary-operator</i> in the grammar in [C],
     but it also includes one-argument operators
     used in <i>unary-expression</i> and <i>postfix-expression</i>,
     which can therefore be reasonably regarded as unary operators,
     although the grammar in [C] reserves the term to only some of them.
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
          [C:6.5.5-14] [C:6.5.16] [C:A.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in [C] does not have a nonterminal for binary operators.
     Instead, it has nonterminals for various kinds of binary expressions,
     used to capture certain precedence rules in the grammar itself.
     In our abstract syntax, for better factoring and orthogonality,
     it makes sense to introduce a fixtype for binary operators,
     and use it to define binary expressions as in @(tsee expr).
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
     @('|'),
     @('^'),
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
     @('^='),
     @('|='), and
     @('*=')."))
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

(fty::deftagsum stoclaspec
  :short "Fixtype of storage class specifiers [C:6.7.1] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>storage-class-specifier</i> in the grammar in [C].
     The storage class specifiers are
     @('typedef'),
     @('extern'),
     @('static'),
     @('_Thread_local'),
     @('auto'), and
     @('register')."))
  (:tydef ())
  (:extern ())
  (:static ())
  (:threadloc ())
  (:auto ())
  (:register ())
  :pred stoclaspecp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tyqual
  :short "Fixtype of type qualifiers [C:6.7.3] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>type-qualifier</i> in the grammar in [C].
     The type qualifiers are
     @('const'),
     @('restrict'),
     @('volatile'), and
     @('_Atomic')."))
  (:const ())
  (:restrict ())
  (:volatile ())
  (:atomic ())
  :pred tyqualp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tyqual-list
  :short "Fixtype of lists of type qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type qualifiers are defined in @(tsee tyqual)."))
  :elt-type tyqual
  :true-listp t
  :elementp-of-nil nil
  :pred tyqual-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tyqual-list
  :short "Fixtype of lists of type qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type qualifiers are defined in @(tsee tyqual)."))
  :elt-type tyqual
  :true-listp t
  :elementp-of-nil nil
  :pred tyqual-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tyqual-list-list
  :short "Fixtype of lists of lists of type qualifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type qualifiers are defined in @(tsee tyqual)."))
  :elt-type tyqual-list
  :true-listp t
  :elementp-of-nil t
  :pred tyqual-list-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum funspec
  :short "Fixtype of function specifiers [C:6.7.4] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>function-specifier</i> in the grammar in [C].
     The function specifiers are @('inline') and @('_Noreturn')."))
  (:inline ())
  (:noreturn ())
  :pred funspecp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes exprs/decls
  :short "Fixtypes of expressions, declarations, and related entities
          [C:6.5] [C:6.6] [C:6.7] [C:A.2.1] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in [C] defines expressions and declarations
     via a large and complex collection of mutually recursive rules.
     We use a corresponding collection of mutually recursive fixtypes,
     which take a few seconds to process on fast machines.
     If we run into scalability issues, we could split the recursion
     by using more generic fixtypes in certain places
     and by enforcing the more restricted fixtypes in predicates.
     For instance, to avoid the dependency of expressions on type names
     (which in turn depend on expressions, hence the mutual recursion),
     we could use the fixtype for @(tsee acl2::any-p)
     in the definition of expressions instead of the fixtype for type names,
     and then we could define predicates requiring
     those values to be in fact type names,
     whose fixtype would be defined after, and non-recursively with,
     the fixtype of expressions.")
   (xdoc::p
    "A few fixtypes related to declarations
     are actually outside this mutual recursion,
     because they are not mutually recursive with others.
     For instance, the fixtype @(tsee tyqual) for type qualifiers
     is defined before these mutually recursive fixtypes,
     and the fixtype @(tsee decl) for (top-level) declarations
     is defined after these mutually recursive fixtypes.")
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
     in an @(tsee dirabsdeclor), all the cases except @(':paren')
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
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of expressions [C:6.5] [C:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>expression</i> in the grammar in [C].")
     (xdoc::p
      "Given that abstract syntax is tree-structured,
       we do not explicitly introduce the various kinds of binary expressions
       defined in the grammar in [C],
       and instead use a single kind of binary expression
       consisting of two sub-expressions and a binary operator.
       Furthermore, we always use the general fixtype for expressions
       as components of other constructs where the grammar in [C]
       uses more specific kinds of expressions,
       like <i>assignment-expression</i> in <i>generic-selection</i>.
       This means that our fixtypes are a bit more general,
       but we can use separate predicates to enforce restrictions.")
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
      "The @(':sizeof') case of this fixtype
       captures @('sizeof') applied to a type name.
       The @('sizeof') applied to an expression is instead captured
       in the @(':unary') case,
       since @(tsee unop) includes @('sizeof') for expressions.
       During parsing, an expression of the form @('sizeof ( I )'),
       where @('I') is an identifier,
       cannot be disambiguated on a purely syntactic basis,
       because @('I') may be either an expression or a type name:
       we defer the resolution of this ambiguity
       to static semantic analysis after parsing;
       during parsing, we classify that as a type name.")
     (xdoc::p
      "We use different cases, @(':member') and @(':memberp')
       for the @('.') and @('->') operators.")
     (xdoc::p
      "For compound literals, we also capture
       the presence of absence of the final comma
       just after the <i>initializer-list</i>.
       We formalize <i>initializer-list</i> [C:6.7.9] [C:A.2.2]
       as a list (which should be non-empty) of pairs each consisting of
       some designators and an initializer (see @(tsee desiniter).")
     (xdoc::p
      "The comma sequentialization operator is modeled
       as its own case in this fixtype.
       An alternative is to include that into @(tsee binop).
       Another alternative is to model it as taking
       a list of expressions (it associates to the left).
       But for now the current model is adequate.")
     (xdoc::p
      "The remaining four kinds of expressions capture expressions of the form")
     (xdoc::codeblock
      "(I) * E"
      "(I) + E"
      "(I) - E"
      "(I) & E")
     (xdoc::p
      "where @('I') is an identifier
       and @('E') is an expression of a certain form
       (depending on the preceding operator).
       These expressions are syntactically ambiguous because they may be
       either cast expressions (if @('I') is a type name)
       or binary expressions (if @('I') is an expression).
       More precisely, @('E') could be a binary expression,
       and thus things would associate differently, e.g.")
     (xdoc::codeblock
      "(I) + E1 * E2")
     (xdoc::p
      "could be either the product of a cast expression and another expression
       or the sum of an identifier and a product of two expressions.")
     (xdoc::p
      "The problem is that the four operators above
       are both unary and binary,
       and that type names and expressions overlap in identifiers.
       There is no way to resolve this ambiguity purely syntactically:
       some (static) semantic analysis is needed,
       in particular to determine
       whether @('I') is a type name or an expression,
       based on what is in scope at that point.
       Here are some resources that describe the issue
       and approaches to handle it:")
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
      "(And more resources should be easy to find.)
       We handle the issue by extending our definition of expressions
       with cases that represent syntactically ambiguous expressions:
       there are four cases, one for each unary/binary operator,
       and each case has two components, namely
       the identifier that is either a type name or an expression,
       and a subsequent expression.
       We prefer this approach to
       performing any kind of semantic analysis during parsing."))
    (:ident ((unwrap ident)))
    (:const ((unwrap const)))
    (:string ((unwrap stringlit)))
    (:paren ((unwrap expr)))
    (:gensel ((control expr)
              (assoc genassoc-list)))
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
             (arg expr)))
    (:sizeof ((type tyname)))
    (:alignof ((type tyname)))
    (:cast ((type tyname)
            (arg expr)))
    (:binary ((op binop)
              (arg1 expr)
              (arg2 expr)))
    (:cond ((test expr)
            (then expr)
            (else expr)))
    (:comma ((first expr)
             (next expr)))
    (:cast/mul ((type/arg1 ident)
                (arg/arg2 expr)))
    (:cast/add ((type/arg1 ident)
                (arg/arg2 expr)))
    (:cast/sub ((type/arg1 ident)
                (arg/arg2 expr)))
    (:cast/and ((type/arg1 ident)
                (arg/arg2 expr)))
    :pred exprp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-list
    :parents (abstract-syntax expr/decls)
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
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of optional expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Expressions are defined in @(tsee expr)."))
    :pred expr-optionp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod const-expr
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of constant expressions [C:6.6] [C:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>constant-expression</i> in the grammar in [C].
       As in that grammar,
       it does not actually constrain the expression to be constant,
       but it may be useful to mark expressions to be constant,
       with separate predicates that enforce that."))
    ((unwrap expr))
    :pred const-exprp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption const-expr-option
    const-expr
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of optional constant expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Constant expressions are defined in @(tsee const-expr)."))
    :pred const-expr-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum genassoc
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of generic associations [C:6.5.1.1] [C:A.2.1]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>generic-association</i> in the grammar in [C]."))
    (:type ((type tyname)
            (expr expr)))
    (:default ((expr expr)))
    :pred genassocp
    :base-case-override :default
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist genassoc-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Generic associations are defined in @(tsee genassoc).")
     (xdoc::p
      "This fixtype corresponds to <i>generic-assoc-list</i>
     in the grammar in [C]."))
    :elt-type genassoc
    :true-listp t
    :elementp-of-nil nil
    :pred genassoc-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum tyspec
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of type specifiers [C:6.7.3] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This captures <i>type-specifier</i> in the grammar in [C].")
     (xdoc::p
      "We model <i>atomic-type-specifier</i>
       by inlining the type name into the @(':atomic') case of this fixtype.")
     (xdoc::p
      "We make two separate cases for structures and unions,
       avoiding explicit modeling of the <i>struct-or-union</i> nonterminal.")
     (xdoc::p
      "We model <i>typedef-name</i>
       by inlining the type name into the @(':tydef') case of this fixtype."))
    (:void ())
    (:char ())
    (:short ())
    (:int ())
    (:long ())
    (:float ())
    (:double ())
    (:signed ())
    (:unsigned ())
    (:bool ())
    (:complex ())
    (:atomic ((type tyname)))
    (:struct ((unwrap strunispec)))
    (:union ((unwrap strunispec)))
    (:enum ((unwrap enumspec)))
    (:tydef ((name ident)))
    :pred tyspecp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum specqual
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of type specifiers and type qualifiers
            [C:6.7.2.1] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not correspond directly
       to any nonterminal in the grammar in [C],
       but it is useful to define <i>specifier-qualifier-list</i>:
       see @(tsee specqual-list)."))
    (:tyspec ((unwrap tyspec)))
    (:tyqual ((unwrap tyqual)))
    (:alignspec ((unwrap alignspec)))
    :pred specqualp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist specqual-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of type specifiers and type qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "The fixtype of type specifiers and type qualifiers
       is defined in @(tsee specqual).")
     (xdoc::p
      "This fixtype corresponds to <i>specifier-qualifier-list</i>."))
    :elt-type specqual
    :true-listp t
    :elementp-of-nil nil
    :pred specqual-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum alignspec
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of alignment specifiers [C:6.7.5] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>alignment-specifier</i> in the grammar in [C].
       The two cases of this fixtype correspond to
       the two forms of @('_Alignas'),
       one for type names and one for constant expressions."))
    (:alignas-type ((type tyname)))
    (:alignas-expr ((arg const-expr)))
    :pred alignspecp
    :base-case-override :alignas-expr
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum declspec
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of declaration specifiers [C:6.7] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This does not directly correspond to
       any nonterminal in the grammar in [C],
       but it is useful to define <i>declaration-specifiers</i>
       (see @(tsee declspec-list))."))
    (:stocla ((unwrap stoclaspec)))
    (:tyspec ((unwrap tyspec)))
    (:tyqual ((unwrap tyqual)))
    (:funspec ((unwrap funspec)))
    (:alignspec ((unwrap alignspec)))
    :pred declspecp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist declspec-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "The fixtype of declaration specifiers is defined in @(tsee declspec).")
     (xdoc::p
      "This fixtype corresponds to <i>declaration-specifiers</i>
       in the grammar in [C]."))
    :elt-type declspec
    :true-listp t
    :elementp-of-nil nil
    :pred declspec-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum initer
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of initializers [C:6.7.9] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>initializer</i> in the grammar in [C].
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
    :parents (abstract-syntax expr/decls)
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
            [C:6.7.9] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This has no direct corresponding nonterminal in the grammar in [C],
       but it is useful to define <i>initializer-list</i>,
       which is a non-empty sequence of initializers with designations.
       An optional <i>designation</i> [C:6.7.9] [C:A.2.2] is captured here
       as a list of designators (see @(tsee designor)),
       where the empty list means that the designation is absent,
       while a non-empty list captures the designation,
       which has a non-empty list of designators."))
    ((design designor-list)
     (init initer))
    :parents (abstract-syntax expr/decls)
    :pred desiniterp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist desiniter-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of initializers with designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializers with designations are defined in @(tsee desiniter).")
     (xdoc::p
      "This fixtype corresponds to <i>initializer-list</i>
       in the grammar in [C]."))
    :elt-type desiniter
    :true-listp t
    :elementp-of-nil nil
    :pred desiniter-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum designor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of designators [C:6.7.9] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>designator</i> in the grammar in [C]."))
    (:sub ((index const-expr)))
    (:dot ((name ident)))
    :pred designorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist designor-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Designators are defines in @(tsee designor)."))
    :elt-type designor
    :true-listp t
    :elementp-of-nil nil
    :pred designor-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod declor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of declarators [C:6.7.6] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>declarator</i> in the grammar in [C].
       The optional <i>pointer</i> that precedes the <i>direct-declarator</i>
       is a sequence of stars each optionally followed by
       an optional sequence of type qualifiers.
       We model this as a list of lists of type qualifiers:
       the outer list corresponds to each star,
       and each inner list corresponds to the type qualifiers
       that immediately follow the star."))
    ((pointers tyqual-list-list)
     (decl dirdeclor))
    :pred declorp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum dirdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of direct declarators [C:6.7.6] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>direct-declarator</i> in the grammar in [C].")
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
       we inline <i>parameter-type-list</i>."))
    (:ident ((unwrap ident)))
    (:paren ((unwrap declor)))
    (:array ((decl dirdeclor)
             (tyquals tyqual-list)
             (expr? expr-option)))
    (:array-static1 ((decl dirdeclor)
                     (tyquals tyqual-list)
                     (expr expr)))
    (:array-static2 ((decl dirdeclor)
                     (tyquals tyqual-list)
                     (expr expr)))
    (:array-star ((decl dirdeclor)
                  (tyquals tyqual-list)))
    (:function-params ((decl dirdeclor)
                       (params paramdecl-list)
                       (ellipses bool)))
    (:function-names ((decl dirdeclor)
                      (names ident-list)))
    :pred dirdeclorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod absdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of abstract declarators [C:6.7.7] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>abstract-declarator</i> in the grammar in [C].
       This fixtype is similar to @(tsee declor)
       (see that fixtype's documentation in particular
       for an explanation of the modeling of the <i>pointer</i> part),
       but the abstract direct declarator is optional."))
    ((pointers tyqual-list-list)
     (decl? dirabsdeclor-option))
    :pred absdeclorp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption absdeclor-option
    absdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of optional abstract declarators [C:6.7.7] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "Abstract declarators are defined in @(tsee absdeclor)."))
    :pred absdeclor-optionp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum dirabsdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of direct abstract declarators [C:6.7.7] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>direct-abstract-declarator</i>
       in the grammar in [C].
       This fixtype is similar to @(tsee dirdeclor),
       with the differences that
       the nested direct abstract declarators are optional,
       the @('...[*]') form has no type qualifiers just before the @('*'),
       and there is just the parameter form for functions.
       Furthermore, as explained in @(see exprs/decls),
       there is a dummy base case."))
    (:dummy-base ())
    (:paren ((unwrap absdeclor)))
    (:array ((decl? dirabsdeclor-option)
             (tyquals tyqual-list)
             (expr? expr-option)))
    (:array-static1 ((decl? dirabsdeclor-option)
                     (tyquals tyqual-list)
                     (expr expr)))
    (:array-static2 ((decl? dirabsdeclor-option)
                     (tyquals tyqual-list)
                     (expr expr)))
    (:array-star ((decl? dirabsdeclor-option)))
    (:function ((decl? dirabsdeclor-option)
                (params paramdecl-list)
                (ellipses bool)))
    :pred dirabsdeclorp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::defoption dirabsdeclor-option
    dirabsdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of optional direct abstract declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Direct abstract declarators are defined in @(tsee dirabsdeclor)."))
    :pred dirabsdeclor-optionp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum paramdecl
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of parameter declarations [C:6.7.6] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>parameter-declaration</i> in the grammar in [C].
       There are declaration specifiers followed by
       either a (non-abstract) declarator
       or an optional abstract declarator."))
    (:nonabstract ((spec declspec-list)
                   (decl declor)))
    (:abstract ((spec declspec-list)
                (decl absdeclor-option)))
    :pred paramdeclp
    :base-case-override :nonabstract
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist paramdecl-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Parameter declarations are defined in @(tsee paramdecl).
       This fixtype corresponds to <i>parameter-list</i>
       in the grammar in [C]."))
    :elt-type paramdecl
    :true-listp t
    :elementp-of-nil nil
    :pred paramdecl-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod tyname
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of type names [C:6.7.7] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>type-name</i> in the grammar in [C]."))
    ((specqual specqual-list)
     (decl? absdeclor-option))
    :pred tynamep
    :measure (two-nats-measure (acl2-count x) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum strunispec
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of structure and union specifiers [C:6.7.2.1] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-or-union-specifier</i>
       in the grammar in [C], but without the initial <i>struct-or-union</i>.
       The only use of this fixtype is in @(tsee tyspec),
       where we have two separate cases for structures and unions."))
    (:name ((name ident)))
    (:members ((members structdecl-list)))
    (:name-members ((name ident)
                    (members structdecl-list)))
    :pred strunispecp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum structdecl
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of structure declarations [C:6.7.2.1] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-declaration</i> in the grammar of [C].
     Despite its name in the grammar and in this fixtype,
     this applies to both structures and unions;
     in fact, it is not a declaration of a structure,
     but instead it is a declarations of a member of a structure or union.
     So something like <i>member-declaration</i>
     would be a better name for this grammar nonterminal,
     but our fixtype name reflects the current grammar."))
    (:member ((specqual specqual-list)
              (declor structdeclor-list)))
    (:statassert ((unwrap statassert)))
    :pred structdeclp
    :base-case-override :statassert
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist structdecl-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of structure declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "Structure declarations are defined in @(tsee structdecl).
       This fixtype corresponds to <i>struct-declaration-list</i>
       in the grammar in [C]."))
    :elt-type structdecl
    :true-listp t
    :elementp-of-nil nil
    :pred structdecl-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum structdeclor
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of structure declarators [C:6.7.2.1] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>struct-declarator</i> in the grammar in [C].
       This is part of structure declarations,
       so as discussed in @(tsee structdecl)
       arguably a better name would be `member declarators'."))
    (:declor ((unwrap declor)))
    (:expr ((unwrap const-expr)))
    (:declor-expr ((declor declor)
                   (expr const-expr)))
    :pred structdeclorp
    :base-case-override :expr
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist structdeclor-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Structure declarators are defined in @(tsee structdeclor).
       This fixtype corresponds to <i>struct-declarator-list</i>
       in the grammar in [C]."))
    :elt-type structdeclor
    :true-listp t
    :elementp-of-nil nil
    :pred structdeclor-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum enumspec
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of enumeration specifiers [C:6.7.2.2] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>enum-specifier</i> in the grammar in [C]."))
    (:name ((unwrap ident)))
    (:list ((unwrap enumer-list)
            (final-comma bool)))
    (:name-list ((name ident)
                 (list enumer-list)
                 (final-comma bool)))
    :pred enumspec
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod enumer
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of enumerators [C:6.7.2.2] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>enumerator</i> in the grammar in [C]."))
    ((name ident)
     (value const-expr-option))
    :pred enumerp
    :measure (two-nats-measure (acl2-count x) 3))

  ;;;;;;;;;;;;;;;;;;;;

  (fty::deflist enumer-list
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of lists of enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "Enumerators are defined in @(tsee enumer).
       This fixtype corresponds to <i>enumerator-list</i>
       in the grammar in [C]."))
    :elt-type enumer
    :true-listp t
    :elementp-of-nil nil
    :pred enumer-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod statassert
    :parents (abstract-syntax expr/decls)
    :short "Fixtype of static assertion declarations [C:6.7.10] [C:A.2.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>static_assert-declaration</i>
       in the grammar in [C]."))
    ((test const-expr)
     (message stringlit))
    :pred statassertp
    :measure (two-nats-measure (acl2-count x) 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod initdeclor
  :short "Fixtype of initializer declarators [C:6.7] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>init-declarator</i> in the grammar in [C].
     This is part of declarations,
     but it is outside the mutual recursion in @(see exprs/decls)."))
  ((declor declor)
   (init? initer-option))
  :pred initdeclorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist initdeclor-list
  :short "Fixtype of lists of initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initializer declarators are defined in @(tsee initdeclor).
     This fixtype corresponds to <i>init-declarator-list</i>
     in the grammar in [C]."))
  :elt-type initdeclor
  :true-listp t
  :elementp-of-nil nil
  :pred initdeclor-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum decl
  :short "Fixtype of declarations [C:6.7] [C:A.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>declaration</i> in the grammar in [C].
     It is the top-level construct for declarations,
     and it is outside the mutual recursion @(see exprs/decls)."))
  (:decl ((specs declspec-list)
          (init initdeclor-list)))
  (:statassert ((unwrap statassert)))
  :pred declp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist decl-list
  :short "Fixtype of lists of declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Declarations are defined in @(tsee decl).
     This fixtype corresponds to <i>declaration-list</i>
     in the grammar in [C],
     which is under external definitions [C:6.9.1] [C:A.2.4]."))
  :elt-type decl
  :true-listp t
  :elementp-of-nil nil
  :pred decl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum label
  :short "Fixtype of labels [C:6.8.1] [C:A.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not directly correspond to any nonterminal in the grammar in [C],
     but it captures the three initial portions of
     the grammar rule for <i>labeled-statement</i>.
     There are three possible kinds of labels:
     names (identifiers),
     constant expressions in @('case'),
     and the @('default') label."))
  (:name ((unwrap ident)))
  (:const ((unwrap const-expr)))
  (:default ())
  :pred labelp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes stmts/blocks
  :short "Fixtypes of statements, blocks, and related entities
          [C:6.8] [C:A.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are mutually recursive,
     but the mutual recursion is much smaller and simpler
     than the one in @(see exprs/decls)."))

  (fty::deftagsum stmt
    :parents (abstract-syntax stmts/blocks)
    :short "Fixtype of statements [C:6.8] [C:A.2.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>statement</i> in the grammar in [C].")
     (xdoc::p
      "We inline
       <i>labeled-stament</i>,
       <i>expression-statement</i>,
       <i>selection-statement</i>,
       <i>iteration-statement</i>, and
       <i>jump-statement</i>.")
     (xdoc::p
      "For labeled statements,
       we use @(tsee label) to factor the three kinds of labels."))
    (:labeled ((label label)
               (stmt stmt)))
    (:compound ((items block-item-list)))
    (:expr ((expr? expr-option)))
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
    (:for ((init expr-option)
           (test expr-option)
           (next expr-option)
           (body stmt)))
    (:fordecl ((init decl)
               (test expr-option)
               (next expr-option)
               (body stmt)))
    (:goto ((label ident)))
    (:continue ())
    (:break ())
    (:return ((expr? expr-option)))
    :pred stmtp)

  (fty::deftagsum block-item
    :parents (abstract-syntax stmts/blocks)
    :short "Fixtype of block items [C:6.8.2] [C:A.2.3]."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to <i>block-item</i> in the grammar in [C]."))
    (:decl ((unwrap decl)))
    (:stmt ((unwrap stmt)))
    :pred block-itemp)

  (fty::deflist block-item-list
    :parents (abstract-syntax stmts/blocks)
    :short "Fixtype of lists of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "Block items are defined in @(tsee block-item).
       This fixtype corresponds to <i>block-item-list</i>
       in the grammar in [C]."))
    :elt-type block-item
    :true-listp t
    :elementp-of-nil nil
    :pred block-item-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef
  :short "Fixtype of function definitions [C:6.9.1] [C:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>function-definition</i> in the grammar in [C].
     Unlike that grammar, we do not constrain the function body
     to be a compound statement in this fixtype."))
  ((spec declspec-list)
   (declor declor)
   (decls decl-list)
   (body stmt))
  :pred fundefp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum extdecl
  :short "Fixtype of external declarations [C:6.9] [C:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>external-declaration</i> in the grammar in [C]."))
  (:fundef ((unwrap fundef)))
  (:decl ((unwrap decl)))
  :pred extdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist extdecl-list
  :short "Fixtype of lists of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "External declarations are defined in @(tsee extdecl).
     This fixtype corresponds to <i>external-declaration-list</i>
     in the grammar in [C]."))
  :elt-type extdecl
  :true-listp t
  :elementp-of-nil nil
  :pred extdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit
  :short "Fixtype of translation units [C:6.9] [C:A.2.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to <i>translation-unit</i> in the grammar in [C].")
   (xdoc::p
    "We wrap the list of external declarations in this fixtype
     to maintain a conceptual separation with translation units."))
  ((decls extdecl-list))
  :pred transunitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap filepath-transunit-map
  :short "Fixtype of omaps from file paths to translation units."
  :key-type filepath
  :val-type transunit
  :pred filepath-transunit-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit-ensemble
  :short "Fixtype of ensembles of translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion has no explicit counterpart in [C],
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
     corresponds exactly to the notion of translation unit in [C].
     As we add support for preprocessing constructs,
     our translation units will be more like something in between
     proper traslation units and preprocessing translation units.
     The notion of file set as formalized here will still apply to that case,
     with some elements of the ensembles
     that may be headers instead of source files."))
  ((unwrap filepath-transunit-map))
  :pred transunit-ensemblep)
