; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "name-tables")
(include-book "hangul")
(include-book "versions")
(include-book "general-category")
(include-book "data/v16.0.0/jamo")
(include-book "data/v17.0.0/jamo")
(include-book "data/v18.0.0/jamo")
(include-book "data/v16.0.0/derived-name")
(include-book "data/v17.0.0/derived-name")
(include-book "data/v18.0.0/derived-name")

(include-book "std/util/defconsts" :dir :system)

(local (include-book "range-operations"))

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ names
  :parents (unicode)
  :short "The names of the characters: the property @('Name')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each character has a name,
     such as @('LATIN SMALL LETTER A') for U+0061
     [Unicode, Section 4.8].
     Formally the name is the value of the property @('Name'),
     which is a string for every code point:
     the empty string for the code points that have no name,
     which are the control codes, the private use code points,
     the surrogate code points, the noncharacters
     and the code points that are not assigned
     [Unicode, Section 4.8, rule NR4].
     Names are made of capital letters, digits, spaces and hyphens,
     and no two code points have the same name.
     The name of a character does not change
     from a version of Unicode to a later one.")
   (xdoc::p
    "The names are defined in three ways [Unicode, Section 4.8].")
   (xdoc::ul
    (xdoc::li
     "The name of a Hangul syllable is @('HANGUL SYLLABLE')
      followed by the short names of its jamo,
      which are the letters of the Korean alphabet
      of which the syllable is made.
      The short names are the values of the property @('Jamo_Short_Name')
      [Unicode, Section 4.8, rule NR1, and Section 3.12].
      For example, U+D4DB decomposes into three jamo
      whose short names are @('P'), @('WI') and @('LH'),
      and its name is @('HANGUL SYLLABLE PWILH').")
    (xdoc::li
     "For some ranges of code points,
      mostly of ideographs,
      the name is a prefix followed by the code point in hexadecimal
      [Unicode, Section 4.8, rule NR2].
      The name of U+4E00 is @('CJK UNIFIED IDEOGRAPH-4E00').")
    (xdoc::li
     "The other names are listed one by one
      [Unicode, Section 4.8, rule NR3]."))
   (xdoc::p
    "We take the names from the file @('DerivedName.txt')
     of the Unicode Character Database, for each supported version:
     it has the listed names, and a pattern for each range of the second kind
     (see @(see name-tables)).
     It also lists the names of the Hangul syllables;
     we compute those by the rule,
     from the short names in the file @('Jamo.txt'),
     and the tests check that the rule gives the names of the file.
     There are 34,137 listed names in Unicode 16.0.0,
     34,594 in 17.0.0 and 35,351 in 18.0.0;
     with the 11,172 Hangul syllables and the ranges with a pattern,
     154,998, 159,801 and 172,808 code points have a name.
     The table of a version is the table of the version before it
     with the names that the version adds.")
   (xdoc::p
    "@(tsee code-point-name) is the name of a code point
     and @(tsee name-code-point) is the code point with a name;
     the theorems say that each undoes the other.
     To go from a name to its code point without a table
     as large as the first one with the names as keys,
     we use the loose matching of names
     [UAX #44, Section 5.9.2, rule UAX44-LM2]:
     two strings match
     when they differ only in the case of their letters,
     in spaces and underscores, and in hyphens between two letters or digits.
     @(tsee name-loose-key) reduces a string to a key
     that is the same for the strings that match,
     the table from keys to code points has the listed names,
     and the names of the other two kinds are read from the key.
     @(tsee loose-name-code-point) is the code point
     whose name matches a string loosely.
     No two names match loosely;
     the Unicode Standard promises this of the names, the name aliases,
     the named sequences and the code point labels taken together,
     and this library does not have the last three.")
   (xdoc::p
    "The theorems are proved by evaluation, on every code point,
     for each supported version;
     so adding a version checks them for that version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jamo-short-names ((ver versionp))
  :returns (map name-mapp)
  :short "The map from the conjoining jamo of the Hangul syllables
          to their short names, in a version of Unicode."
  (version-case ver
                :v16.0.0 *jamo-short-names-v16.0.0*
                :v17.0.0 *jamo-short-names-v17.0.0*
                :v18.0.0 *jamo-short-names-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define jamo-short-name ((cp code-point-p) (ver versionp))
  :returns (name stringp)
  :short "The @('Jamo_Short_Name') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The property has a value for the 67 conjoining jamo
     of which the Hangul syllables are composed:
     19 leading consonants, 21 vowels and 27 trailing consonants
     [Unicode, Section 3.12].
     The values are one to three capital letters,
     and for U+110B HANGUL CHOSEONG IEUNG the empty string.
     The result is the empty string for every other code point too."))
  (name-map-lookup cp (jamo-short-names ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define jamos-short-name ((jamos code-point-listp) (ver versionp))
  :returns (name stringp)
  :short "The short names of a list of jamo, one after the other."
  (if (endp jamos)
      ""
    (string-append (jamo-short-name (car jamos) ver)
                   (jamos-short-name (cdr jamos) ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-name ((s hangul-syllable-p) (ver versionp))
  :returns (name stringp)
  :short "The name of a Hangul syllable, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is @('HANGUL SYLLABLE'), a space,
     and the short names of the two or three jamo
     of the full decomposition of the syllable
     [Unicode, Section 4.8, rule NR1,
     and Section 3.12, Hangul Syllable Name Generation]."))
  (string-append "HANGUL SYLLABLE "
                 (jamos-short-name (hangul-syllable-decomposition s) ver))
  :guard-hints (("Goal" :in-theory (enable
                                    code-point-listp-when-scalar-value-listp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hex-digit-char (digit)
  :returns (char characterp)
  :short "The hexadecimal digit for a number below 16,
          with a capital letter from 10 on."
  (acl2::char-fix (nth (nfix digit)
                       '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7
                         #\8 #\9 #\A #\B #\C #\D #\E #\F))))

;;;;;;;;;;;;;;;;;;;;

(define code-point-hex-chars ((cp code-point-p))
  :returns (chars character-listp)
  :short "The hexadecimal digits of a code point, as a list of characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee code-point-hex)."))
  (b* ((cp (code-point-fix cp))
       (d0 (hex-digit-char (mod cp 16)))
       (d1 (hex-digit-char (mod (floor cp #x10) 16)))
       (d2 (hex-digit-char (mod (floor cp #x100) 16)))
       (d3 (hex-digit-char (mod (floor cp #x1000) 16)))
       (d4 (hex-digit-char (mod (floor cp #x10000) 16)))
       (d5 (hex-digit-char (mod (floor cp #x100000) 16))))
    (cond ((< cp #x10000) (list d3 d2 d1 d0))
          ((< cp #x100000) (list d4 d3 d2 d1 d0))
          (t (list d5 d4 d3 d2 d1 d0))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-hex ((cp code-point-p))
  :returns (hex stringp)
  :short "A code point in hexadecimal, as it is written after @('U+')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The digits above 9 are capital letters,
     and there are four to six digits:
     zeros are written at the front
     only when there would be fewer than four digits without them
     [Unicode, Appendix A].
     So U+0041 gives @('0041') and U+1F600 gives @('1F600')."))
  (coerce (code-point-hex-chars cp) 'string)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-patterns ((ver versionp))
  :returns (patterns name-pattern-listp)
  :short "The patterns of names of a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the ranges of code points
     whose names are a prefix followed by the code point
     [Unicode, Section 4.8, Table 4-8],
     as the file @('DerivedName.txt') has them.
     A range of the file ends at the last assigned code point,
     so some ranges are longer in a later version.
     The prefixes are
     @('CJK UNIFIED IDEOGRAPH-'), @('CJK COMPATIBILITY IDEOGRAPH-'),
     @('EGYPTIAN HIEROGLYPH-'), @('TANGUT IDEOGRAPH-'),
     @('KHITAN SMALL SCRIPT CHARACTER-') and @('NUSHU CHARACTER-'),
     and from Unicode 18.0.0 on
     @('JURCHEN CHARACTER-') and @('SMALL SEAL CHARACTER-')."))
  (version-case ver
                :v16.0.0 *name-patterns-v16.0.0*
                :v17.0.0 *name-patterns-v17.0.0*
                :v18.0.0 *name-patterns-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define listed-names ((ver versionp))
  :returns (map name-mapp)
  :short "The map from the code points whose names are listed one by one
          to their names, in a version of Unicode."
  (version-case ver
                :v16.0.0 *names-v16.0.0*
                :v17.0.0 *names-v17.0.0*
                :v18.0.0 *names-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-name ((cp code-point-p) (ver versionp))
  :returns (name stringp)
  :short "The name of a code point: its @('Name') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the empty string for a code point that has no name
     [Unicode, Section 4.8, rule NR4].
     See @(see names) for the three ways in which a name is defined."))
  (b* ((cp (code-point-fix cp))
       ((when (hangul-syllable-p cp)) (hangul-syllable-name cp ver))
       (prefix (name-patterns-prefix cp (name-patterns ver)))
       ((unless (equal prefix ""))
        (string-append prefix (code-point-hex cp))))
    (name-map-lookup cp (listed-names ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-char-p ((char characterp))
  :returns (yes/no booleanp)
  :short "Recognize the characters of which names are made:
          the capital letters @('A') to @('Z'), the digits,
          the space and the hyphen."
  (b* ((code (char-code (acl2::char-fix char))))
    (or (and (<= 65 code) (<= code 90))
        (and (<= 48 code) (<= code 57))
        (equal code 32)
        (equal code 45)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-char-listp ((chars character-listp))
  :returns (yes/no booleanp)
  :short "Recognize lists of characters of which names are made."
  (or (endp chars)
      (and (name-char-p (car chars))
           (name-char-listp (cdr chars))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-ignored-char-p ((char characterp))
  :returns (yes/no booleanp)
  :short "Recognize the characters that the loose matching of names ignores:
          white space and the underscore."
  :long
  (xdoc::topstring
   (xdoc::p
    "An ACL2 string has characters with codes below 256.
     We take a character to be white space
     when the code point with its code has the property @('White_Space'),
     which is the same in the supported versions:
     the codes are 9 to 13, 32, 133 and 160.
     The names themselves have only the space, with code 32.
     The underscore has code 95."))
  (b* ((code (char-code (acl2::char-fix char))))
    (or (and (<= 9 code) (<= code 13))
        (equal code 32)
        (equal code 133)
        (equal code 160)
        (equal code 95)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-alphanumeric-char-p ((char characterp))
  :returns (yes/no booleanp)
  :short "Recognize the letters @('A') to @('Z'), of either case,
          and the digits."
  (b* ((code (char-code (acl2::char-fix char))))
    (or (and (<= 48 code) (<= code 57))
        (and (<= 65 code) (<= code 90))
        (and (<= 97 code) (<= code 122))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-char-downcase ((char characterp))
  :returns (lower characterp)
  :short "Turn a capital letter @('A') to @('Z') into the small letter;
          leave any other character as it is."
  (b* ((char (acl2::char-fix char))
       (code (char-code char)))
    (if (and (<= 65 code) (<= code 90))
        (code-char (+ 32 code))
      char))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-char-upcase ((char characterp))
  :returns (upper characterp)
  :short "Turn a small letter @('a') to @('z') into the capital letter;
          leave any other character as it is."
  (b* ((char (acl2::char-fix char))
       (code (char-code char)))
    (if (and (<= 97 code) (<= code 122))
        (code-char (- code 32))
      char))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-chars-upcase ((chars character-listp))
  :returns (upper character-listp)
  :short "Turn the small letters of a list of characters
          into capital letters."
  (if (endp chars)
      nil
    (cons (name-char-upcase (car chars))
          (name-chars-upcase (cdr chars))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define name-loose-key-chars ((after-alphanumeric booleanp)
                              (chars character-listp)
                              (keep-hyphens booleanp))
  :returns (key-chars character-listp)
  :short "The characters of the key of a string for loose matching,
          from the characters of the string."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee name-loose-key).
     The first argument says whether the character before the list,
     in the string, is a letter or a digit;
     the third argument is true to keep every hyphen."))
  (b* (((when (endp chars)) nil)
       (char (acl2::char-fix (car chars)))
       (rest (name-loose-key-chars (name-alphanumeric-char-p (car chars))
                                   (cdr chars)
                                   keep-hyphens))
       ((when (name-ignored-char-p char)) rest)
       ((when (and (not keep-hyphens)
                   (equal char #\-)
                   after-alphanumeric
                   (consp (cdr chars))
                   (name-alphanumeric-char-p
                    (acl2::char-fix (cadr chars)))))
        rest))
    (cons (name-char-downcase char) rest))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define name-loose-key ((name stringp))
  :returns (key stringp)
  :short "The key of a string for the loose matching of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two strings match loosely as names
     when they are the same after these three steps
     [UAX #44, Section 5.9.2, rule UAX44-LM2]:
     remove every medial hyphen,
     which is a hyphen between two letters or digits of the string;
     remove white space and underscores;
     turn capital letters into small letters.
     The key is the string after the three steps.
     So @('ZERO WIDTH SPACE'), @('zero-width space')
     and @('zerowidthspace') have the same key, @('zerowidthspace').
     The hyphen of @('TIBETAN LETTER -A') is not medial,
     and the key is @('tibetanletter-a'),
     which is not the key of @('TIBETAN LETTER A').")
   (xdoc::p
    "The rule has one exception:
     the medial hyphen of the name of U+1180, @('HANGUL JUNGSEONG O-E'),
     is kept, because U+116C is @('HANGUL JUNGSEONG OE').
     We keep the hyphens of a string
     when the string with all its hyphens kept,
     after the other two steps, is @('hanguljungseongo-e')."))
  (b* ((chars (coerce (acl2::str-fix name) 'list))
       (kept (coerce (name-loose-key-chars nil chars t) 'string))
       ((when (equal kept "hanguljungseongo-e")) kept))
    (coerce (name-loose-key-chars nil chars nil) 'string))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-keys-add ((cps code-point-listp)
                       (names name-mapp)
                       (keys name-key-mapp))
  :returns (new-keys name-key-mapp)
  :short "Add to a map from keys to code points
          the keys of the names that a map gives to a list of code points."
  (b* (((when (endp cps)) (name-key-map-fix keys))
       (cp (code-point-fix (car cps)))
       (name (name-map-lookup cp names))
       (keys (if (equal name "")
                 (name-key-map-fix keys)
               (treemap::update (name-loose-key name)
                                cp
                                (name-key-map-fix keys)))))
    (name-keys-add (cdr cps) names keys))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

; The maps from the keys of the listed names to the code points.
; They are built when this book is certified
; and stored in its certificate.

(defconsts *name-keys-v16.0.0*
  (name-keys-add (all-code-points) *names-v16.0.0* (treemap::empty)))

(defconsts *name-keys-v17.0.0*
  (name-keys-add (all-code-points) *names-v17.0.0* (treemap::empty)))

(defconsts *name-keys-v18.0.0*
  (name-keys-add (all-code-points) *names-v18.0.0* (treemap::empty)))

; No two listed names have the same key.

(assert-event (equal (treemap::size *name-keys-v16.0.0*)
                     (treemap::size *names-v16.0.0*)))
(assert-event (equal (treemap::size *name-keys-v17.0.0*)
                     (treemap::size *names-v17.0.0*)))
(assert-event (equal (treemap::size *name-keys-v18.0.0*)
                     (treemap::size *names-v18.0.0*)))

;;;;;;;;;;;;;;;;;;;;

(define listed-name-keys ((ver versionp))
  :returns (keys name-key-mapp)
  :short "The map from the keys of the names that are listed one by one
          to their code points, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys are those of @(tsee name-loose-key).
     The map has as many entries as @(tsee listed-names):
     no two listed names have the same key."))
  (version-case ver
                :v16.0.0 *name-keys-v16.0.0*
                :v17.0.0 *name-keys-v17.0.0*
                :v18.0.0 *name-keys-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jamo-with-short-name ((name stringp)
                              (first code-point-p)
                              (count natp)
                              (ver versionp))
  :returns (jamo? code-point-option-p)
  :short "The first code point with a given @('Jamo_Short_Name'),
          among a number of code points in a row."
  (b* (((when (zp count)) nil)
       (first (code-point-fix first))
       ((when (equal (jamo-short-name first ver)
                     (acl2::str-fix name)))
        first)
       ((unless (code-point-p (+ 1 first))) nil))
    (jamo-with-short-name name (+ 1 first) (- count 1) ver))
  :measure (nfix count)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix zp natp)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-with-jamo-names ((l-name stringp)
                                         (v-name stringp)
                                         (t-name stringp)
                                         (ver versionp))
  :returns (s? code-point-option-p)
  :short "The Hangul syllable whose leading consonant, vowel
          and trailing consonant have given short names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The third name is the empty string
     for a syllable without a trailing consonant.
     The result is @('nil') if one of the names
     is not the short name of a jamo of its kind."))
  (b* ((l? (jamo-with-short-name l-name
                                 *hangul-l-base*
                                 *hangul-l-count*
                                 ver))
       (v? (jamo-with-short-name v-name
                                 *hangul-v-base*
                                 *hangul-v-count*
                                 ver))
       (t? (if (equal (acl2::str-fix t-name) "")
               *hangul-t-base*
             (jamo-with-short-name t-name
                                   (+ 1 *hangul-t-base*)
                                   (- *hangul-t-count* 1)
                                   ver)))
       ((unless (and l? v? t?)) nil)
       (s (+ *hangul-s-base*
             (* (+ (* (- l? *hangul-l-base*) *hangul-v-count*)
                   (- v? *hangul-v-base*))
                *hangul-t-count*)
             (- t? *hangul-t-base*))))
    (and (hangul-syllable-p s)
         s))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-with-jamo-chars ((chars character-listp)
                                         (l-length natp)
                                         (v-length natp)
                                         (ver versionp))
  :returns (s? code-point-option-p)
  :short "The Hangul syllable whose jamo have the short names
          into which a list of characters is cut at two positions."
  (b* ((l-length (nfix l-length))
       (v-length (nfix v-length))
       ((unless (<= (+ l-length v-length) (len chars))) nil))
    (hangul-syllable-with-jamo-names
     (coerce (take l-length chars) 'string)
     (coerce (take v-length (nthcdr l-length chars)) 'string)
     (coerce (nthcdr (+ l-length v-length) chars) 'string)
     ver))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-key-code-point ((key-chars character-listp)
                                        (ver versionp))
  :returns (s? code-point-option-p)
  :short "The Hangul syllable for the key of its name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key of the name of a Hangul syllable is @('hangulsyllable')
     followed by the short names of its jamo in small letters.
     The short name of a leading consonant has at most two letters,
     and that of a vowel one to three,
     so we try the six ways of cutting the rest of the key
     and take the first that gives short names of the three kinds.
     The result is @('nil') if there is none."))
  (b* ((prefix (coerce "hangulsyllable" 'list))
       ((unless (and (<= (len prefix) (len key-chars))
                     (equal (take (len prefix) key-chars) prefix)))
        nil)
       (chars (name-chars-upcase (nthcdr (len prefix) key-chars))))
    (or (hangul-syllable-with-jamo-chars chars 0 1 ver)
        (hangul-syllable-with-jamo-chars chars 0 2 ver)
        (hangul-syllable-with-jamo-chars chars 0 3 ver)
        (hangul-syllable-with-jamo-chars chars 1 1 ver)
        (hangul-syllable-with-jamo-chars chars 1 2 ver)
        (hangul-syllable-with-jamo-chars chars 1 3 ver)
        (hangul-syllable-with-jamo-chars chars 2 1 ver)
        (hangul-syllable-with-jamo-chars chars 2 2 ver)
        (hangul-syllable-with-jamo-chars chars 2 3 ver)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hex-chars-value ((chars character-listp) (value natp))
  :returns (new-value? acl2::maybe-natp
                       :hints (("Goal" :in-theory (enable nfix natp))))
  :short "The number that a list of hexadecimal digits stands for,
          after the digits of a number that is given."
  :long
  (xdoc::topstring
   (xdoc::p
    "The digits above 9 are small letters, as in a key.
     The result is @('nil') if a character is not such a digit."))
  (b* (((when (endp chars)) (nfix value))
       (code (char-code (acl2::char-fix (car chars))))
       (digit? (cond ((and (<= 48 code) (<= code 57)) (- code 48))
                     ((and (<= 97 code) (<= code 102)) (- code 87))
                     (t nil)))
       ((unless digit?) nil))
    (hex-chars-value (cdr chars) (+ (* 16 (nfix value)) digit?)))
  :guard-hints (("Goal" :in-theory (enable nfix natp)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define name-pattern-key-code-point ((key-chars character-listp)
                                     (patterns name-pattern-listp))
  :returns (cp? code-point-option-p)
  :short "The code point of the range of a pattern
          whose name can have a given key."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key of a name with a pattern
     is the key of the prefix, without the hyphen at its end,
     followed by the code point in hexadecimal, with small letters.
     We take the first pattern of the list
     such that the key starts in that way
     and the digits stand for a code point of the range of the pattern.
     The result is @('nil') if there is none.
     The digits are not checked to be written
     as @(tsee code-point-hex) writes them:
     @(tsee name-key-code-point) compares the key of the name."))
  (b* (((when (endp patterns)) nil)
       ((name-pattern pattern) (car patterns))
       (prefix (butlast (coerce (name-loose-key pattern.prefix) 'list) 1))
       (value? (and (< (len prefix) (len key-chars))
                    (equal (take (len prefix) key-chars) prefix)
                    (hex-chars-value (nthcdr (len prefix) key-chars) 0)))
       ((when (and value?
                   (code-point-p value?)
                   (code-point-in-range-p value? pattern.range)))
        value?))
    (name-pattern-key-code-point key-chars (cdr patterns)))
  :measure (len patterns)
  :hints (("Goal" :in-theory (enable len o-p o-finp o<)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-key-code-point ((key stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point whose name has a given key,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key is one that @(tsee name-loose-key) gives.
     We look it up in the map of the keys of the listed names;
     if it is not there, we read it as the key of the name
     of a Hangul syllable, and then as the key of a name with a pattern.
     If one of these gives a code point,
     the result is that code point when the key of its name is the given key,
     and @('nil') otherwise.
     So the result is a code point whose name has the key,
     whatever the three searches do;
     that they find the code point of every name is a theorem
     (see @(see names-theorems))."))
  (b* ((key (acl2::str-fix key))
       (ver (version-fix ver))
       (key-chars (coerce key 'list))
       (cp? (or (name-key-map-lookup key (listed-name-keys ver))
                (hangul-syllable-key-code-point key-chars ver)
                (name-pattern-key-code-point key-chars (name-patterns ver)))))
    (and cp?
         (equal (name-loose-key (code-point-name cp? ver)) key)
         cp?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define loose-name-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point whose name matches a string loosely,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the code point whose name has the key of the string
     (see @(tsee name-loose-key)), or @('nil') if there is none.
     So @('latin small letter a'), @('Latin_Small_Letter_A')
     and @('LATINSMALLLETTERA') all give U+0061.
     Only the names are searched:
     this library does not have the name aliases,
     nor the labels of the code points without a name,
     which the same rule matches."))
  (name-key-code-point (name-loose-key name) ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-code-point ((name stringp) (ver versionp))
  :returns (cp? code-point-option-p)
  :short "The code point with a given name, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if no code point has the name.
     The string has to be the name exactly:
     we find the code point whose name matches it loosely,
     and compare the two."))
  (b* ((name (acl2::str-fix name))
       (cp? (loose-name-code-point name ver)))
    (and cp?
         (equal (code-point-name cp? ver) name)
         cp?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection names-theorems
  :short "The two functions between code points and names undo each other,
          no two names match loosely,
          names are made of capital letters, digits, spaces and hyphens,
          the code points without a name are those of four general categories,
          and a name is the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem is the one from which the others about
     @(tsee name-code-point) and @(tsee loose-name-code-point) follow:
     from the key of the name of a code point,
     @(tsee name-key-code-point) finds the code point.
     It is checked on every code point, for each version.
     So the name of a code point gives the code point back,
     exactly or loosely;
     the other direction holds by the definitions.
     Two code points whose names have the same key are the same code point:
     that is the Unicode Standard's promise
     that no two names match loosely
     [UAX #44, Section 5.9.2], for the names of a version.
     In particular no two code points have the same name.")
   (xdoc::p
    "The code points without a name are the control codes,
     the surrogate code points, the private use code points
     and the code points to which no character is assigned,
     which are the noncharacters and the reserved code points
     [Unicode, Section 4.8, rule NR4].
     In terms of the property @('General_Category'),
     the name of a code point is the empty string
     exactly when its general category is
     @('Cc'), @('Cs'), @('Co') or @('Cn')
     (see @(tsee general-category)).
     One direction is checked on every code point,
     and the other on the code points
     outside the ranges of the four categories.
     That theorem is disabled by default.")
   (xdoc::p
    "The last theorem is the stability of names
     [Unicode, Section 4.8]:
     a code point that has a name in a version
     has the same name in every later version.
     It is checked on every code point,
     for each version and the version after it.
     It is disabled by default."))

  ;; The ranges of the code points of the four general categories
  ;; that have no names.

  (defrulel range-listp-of-append
    (implies (and (range-listp x)
                  (range-listp y))
             (range-listp (append x y)))
    :induct t
    :enable append)

  (local
   (define nameless-ranges ((ver versionp))
     :returns (ranges range-listp)
     (append (general-category-ranges (general-category-control) ver)
             (general-category-ranges (general-category-surrogate) ver)
             (general-category-ranges (general-category-private-use) ver)
             (general-category-ranges (general-category-unassigned) ver))
     :hooks nil))

  ;; What is checked on every code point:
  ;; the name is made of the characters of names;
  ;; and if there is a name, the code point is not in those ranges,
  ;; and the key of the name gives the code point.

  (local
   (define name-ok ((cp code-point-p) (nameless range-listp) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((name (code-point-name cp ver)))
       (and (name-char-listp (coerce name 'list))
            (or (equal name "")
                (and (not (code-point-in-ranges-p cp nameless))
                     (equal (name-key-code-point (name-loose-key name) ver)
                            (code-point-fix cp))))))
     :hooks nil))

  (local
   (std::deflist name-ok-listp (x nameless ver)
     :guard (and (code-point-listp x)
                 (range-listp nameless)
                 (versionp ver))
     (name-ok x nameless ver)))

  (defrulel name-ok-listp-of-all-code-points
    (name-ok-listp (all-code-points)
                   (nameless-ranges (version-fix ver))
                   (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable name-ok-listp-of-cons)

  (defrulel name-ok-holds
    (name-ok cp (nameless-ranges (version-fix ver)) ver)
    :rule-classes nil
    :use (:instance name-ok-when-member-equal-of-name-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (nameless (nameless-ranges (version-fix ver)))
                    (ver (version-fix ver)))
    :enable name-ok)

  ;; What is checked on the code points that are not in those ranges:
  ;; there is a name.

  (local
   (define named-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (not (equal (code-point-name cp ver) ""))
     :hooks nil))

  (local
   (std::deflist named-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (named-ok x ver)))

  (defrulel named-ok-listp-of-the-other-code-points
    (named-ok-listp
     (range-list-code-points
      (ranges-complement (nameless-ranges (version-fix ver))))
     (version-fix ver))
    :rule-classes nil
    :enable version-fix-in-terms-of-version-case
    :disable named-ok-listp-of-cons)

  (defrule name-key-code-point-of-name-loose-key-of-code-point-name
    (implies (not (equal (code-point-name cp ver) ""))
             (equal (name-key-code-point
                     (name-loose-key (code-point-name cp ver))
                     ver)
                    (code-point-fix cp)))
    :enable name-ok
    :use name-ok-holds)

  (defrule loose-name-code-point-of-code-point-name
    (implies (not (equal (code-point-name cp ver) ""))
             (equal (loose-name-code-point (code-point-name cp ver) ver)
                    (code-point-fix cp)))
    :enable loose-name-code-point)

  (defrule name-code-point-of-code-point-name
    (implies (not (equal (code-point-name cp ver) ""))
             (equal (name-code-point (code-point-name cp ver) ver)
                    (code-point-fix cp)))
    :enable name-code-point)

  (defrule code-point-name-of-name-code-point
    (implies (name-code-point name ver)
             (equal (code-point-name (name-code-point name ver) ver)
                    (acl2::str-fix name)))
    :enable name-code-point)

  (defrule name-loose-key-of-code-point-name-of-loose-name-code-point
    (implies (loose-name-code-point name ver)
             (equal (name-loose-key
                     (code-point-name (loose-name-code-point name ver) ver))
                    (name-loose-key name)))
    :enable (loose-name-code-point
             name-key-code-point))

  (defrule code-points-equal-when-names-match-loosely
    (implies (and (equal (name-loose-key (code-point-name cp1 ver))
                         (name-loose-key (code-point-name cp2 ver)))
                  (not (equal (code-point-name cp1 ver) ""))
                  (not (equal (code-point-name cp2 ver) "")))
             (equal (code-point-fix cp1)
                    (code-point-fix cp2)))
    :rule-classes nil
    :disable name-key-code-point-of-name-loose-key-of-code-point-name
    :use ((:instance name-key-code-point-of-name-loose-key-of-code-point-name
                     (cp cp1))
          (:instance name-key-code-point-of-name-loose-key-of-code-point-name
                     (cp cp2))))

  (defrule code-points-equal-when-names-equal
    (implies (and (equal (code-point-name cp1 ver)
                         (code-point-name cp2 ver))
                  (not (equal (code-point-name cp1 ver) "")))
             (equal (code-point-fix cp1)
                    (code-point-fix cp2)))
    :rule-classes nil
    :use code-points-equal-when-names-match-loosely)

  (defrule name-char-listp-of-code-point-name
    (name-char-listp (coerce (code-point-name cp ver) 'list))
    :enable name-ok
    :use name-ok-holds)

  (defruled code-point-name-is-empty-in-terms-of-general-category
    (equal (equal (code-point-name cp ver) "")
           (b* ((gc (code-point-general-category cp ver)))
             (or (general-category-case gc :control)
                 (general-category-case gc :surrogate)
                 (general-category-case gc :private-use)
                 (general-category-case gc :unassigned))))
    :enable (name-ok
             named-ok
             nameless-ranges
             code-point-in-general-category-ranges
             equal-of-general-category-control
             equal-of-general-category-surrogate
             equal-of-general-category-private-use
             equal-of-general-category-unassigned)
    :disable ((:e general-category-control)
              (:e general-category-surrogate)
              (:e general-category-private-use)
              (:e general-category-unassigned)
              named-ok-when-member-equal-of-named-ok-listp)
    :use (name-ok-holds
          named-ok-listp-of-the-other-code-points
          (:instance named-ok-when-member-equal-of-named-ok-listp
                     (acl2::a (code-point-fix cp))
                     (x (range-list-code-points
                         (ranges-complement
                          (nameless-ranges (version-fix ver)))))
                     (ver (version-fix ver)))))

  ;; The stability of names.

  (local
   (define name-stable-ok ((cp code-point-p))
     :returns (yes/no booleanp)
     (b* ((name16 (code-point-name cp (version-v16.0.0)))
          (name17 (code-point-name cp (version-v17.0.0)))
          (name18 (code-point-name cp (version-v18.0.0))))
       (and (or (equal name16 "")
                (equal name17 name16))
            (or (equal name17 "")
                (equal name18 name17))))
     :hooks nil))

  (local
   (std::deflist name-stable-ok-listp (x)
     :guard (code-point-listp x)
     (name-stable-ok x)))

  (defrulel name-stable-ok-listp-of-all-code-points
    (name-stable-ok-listp (all-code-points))
    :enable ((:e all-code-points))
    :disable name-stable-ok-listp-of-cons)

  (defrulel name-stable-ok-holds
    (name-stable-ok cp)
    :rule-classes nil
    :use (:instance name-stable-ok-when-member-equal-of-name-stable-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points)))
    :enable name-stable-ok
    :disable name-stable-ok-when-member-equal-of-name-stable-ok-listp)

  (defruledl code-point-name-in-terms-of-version-case
    (implies (syntaxp (not (quotep ver)))
             (equal (code-point-name cp ver)
                    (version-case
                     ver
                     :v16.0.0 (code-point-name cp (version-v16.0.0))
                     :v17.0.0 (code-point-name cp (version-v17.0.0))
                     :v18.0.0 (code-point-name cp (version-v18.0.0)))))
    :enable version-fix-in-terms-of-version-case
    :disable code-point-name-of-version-fix-ver
    :use code-point-name-of-version-fix-ver)

  (defruled code-point-name-of-later-version
    (implies (and (version<= ver1 ver2)
                  (not (equal (code-point-name cp ver1) "")))
             (equal (code-point-name cp ver2)
                    (code-point-name cp ver1)))
    :enable (name-stable-ok
             version<=
             version-rank
             code-point-name-in-terms-of-version-case)
    :use name-stable-ok-holds))
