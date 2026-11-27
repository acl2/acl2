; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the names of the characters (book names.lisp).
;
; The first part has examples of the three kinds of names,
; of the code points without a name,
; of the loose matching of names [UAX #44, Section 5.9.2, rule UAX44-LM2],
; and of the functions from a name to its code point.
;
; The second part has three tests on whole sets of code points,
; for each supported version:
; the rule for the names of the Hangul syllables
; gives the 11,172 names that the file DerivedName.txt lists for them;
; the code points with a name are as many as the listed names,
; the Hangul syllables and the code points of the ranges
; of the names that end in the code point, taken together;
; and the characters that the loose matching ignores as white space
; are, among the first 256 code points, those with the property White_Space.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../names")
(include-book "../white-space")
(include-book "../data/names/hangul-syllable-names")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test (form)
  `(assert-event ,form))

(defconst *v16* (version-v16.0.0))
(defconst *v17* (version-v17.0.0))
(defconst *v18* (version-v18.0.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names that are listed one by one [Unicode, Section 4.8, rule NR3].

(test (equal (code-point-name #x0020 *v16*) "SPACE"))
(test (equal (code-point-name #x0061 *v16*) "LATIN SMALL LETTER A"))
(test (equal (code-point-name #x00E9 *v17*)
             "LATIN SMALL LETTER E WITH ACUTE"))
(test (equal (code-point-name #x03BB *v18*) "GREEK SMALL LETTER LAMDA"))
(test (equal (code-point-name #x200B *v16*) "ZERO WIDTH SPACE"))
(test (equal (code-point-name #x1F600 *v16*) "GRINNING FACE"))
(test (equal (code-point-name #xE01EF *v16*) "VARIATION SELECTOR-256"))

; Names with digits and with hyphens.

(test (equal (code-point-name #x0F39 *v16*) "TIBETAN MARK TSA -PHRU"))
(test (equal (code-point-name #x0F60 *v16*) "TIBETAN LETTER -A"))
(test (equal (code-point-name #x0F68 *v16*) "TIBETAN LETTER A"))
(test (equal (code-point-name #x116C *v16*) "HANGUL JUNGSEONG OE"))
(test (equal (code-point-name #x1180 *v16*) "HANGUL JUNGSEONG O-E"))
(test (equal (code-point-name #x11C88 *v16*) "MARCHEN LETTER -A"))
(test (equal (code-point-name #x1FB3B *v16*) "BLOCK SEXTANT-23456"))

; A character has no name in the versions before the one that adds it.

(test (equal (code-point-name #x088F *v16*) ""))
(test (equal (code-point-name #x088F *v17*)
             "ARABIC LETTER NOON WITH RING ABOVE"))
(test (equal (code-point-name #x088F *v18*)
             "ARABIC LETTER NOON WITH RING ABOVE"))
(test (equal (code-point-name #x0B53 *v16*) ""))
(test (equal (code-point-name #x0B53 *v17*) ""))
(test (equal (code-point-name #x0B53 *v18*) "ORIYA SIGN DOT ABOVE"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names of the Hangul syllables [Unicode, Section 4.8, rule NR1].

; The short names of some jamo.
; The leading consonant U+110B has the empty string.

(test (equal (jamo-short-name #x1100 *v16*) "G"))
(test (equal (jamo-short-name #x110B *v16*) ""))
(test (equal (jamo-short-name #x1111 *v16*) "P"))
(test (equal (jamo-short-name #x1161 *v16*) "A"))
(test (equal (jamo-short-name #x1171 *v16*) "WI"))
(test (equal (jamo-short-name #x11B6 *v16*) "LH"))
(test (equal (jamo-short-name #x11C2 *v16*) "H"))
(test (equal (jamo-short-name #x0041 *v16*) "")) ; not a jamo
(test (equal (jamo-short-name #x1113 *v16*) "")) ; a jamo of no syllable

; The first and the last syllable,
; the example of the Unicode Standard [Unicode, Section 3.12],
; and a syllable whose leading consonant has the empty short name.

(test (equal (code-point-name #xAC00 *v16*) "HANGUL SYLLABLE GA"))
(test (equal (code-point-name #xD7A3 *v16*) "HANGUL SYLLABLE HIH"))
(test (equal (code-point-name #xD4DB *v16*) "HANGUL SYLLABLE PWILH"))
(test (equal (code-point-name #xC544 *v16*) "HANGUL SYLLABLE A"))
(test (equal (code-point-name #xD55C *v17*) "HANGUL SYLLABLE HAN"))
(test (equal (code-point-name #xAE00 *v18*) "HANGUL SYLLABLE GEUL"))
(test (equal (hangul-syllable-name #xD4DB *v16*) "HANGUL SYLLABLE PWILH"))

; The code points next to the syllables.

(test (equal (code-point-name #xABFF *v16*) "")) ; not assigned
(test (equal (code-point-name #xD7A4 *v16*) "")) ; not assigned

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names that end in the code point [Unicode, Section 4.8, rule NR2].

; The code point is written with four to six hexadecimal digits.

(test (equal (code-point-hex #x0000) "0000"))
(test (equal (code-point-hex #x0061) "0061"))
(test (equal (code-point-hex #xFFFF) "FFFF"))
(test (equal (code-point-hex #x10000) "10000"))
(test (equal (code-point-hex #xFABCD) "FABCD"))
(test (equal (code-point-hex #x100000) "100000"))
(test (equal (code-point-hex #x10FFFF) "10FFFF"))

; One name of each family that Unicode 16.0.0 has.

(test (equal (code-point-name #x4E00 *v16*) "CJK UNIFIED IDEOGRAPH-4E00"))
(test (equal (code-point-name #x20000 *v16*) "CJK UNIFIED IDEOGRAPH-20000"))
(test (equal (code-point-name #xF900 *v16*)
             "CJK COMPATIBILITY IDEOGRAPH-F900"))
(test (equal (code-point-name #x2F800 *v16*)
             "CJK COMPATIBILITY IDEOGRAPH-2F800"))
(test (equal (code-point-name #x13460 *v16*) "EGYPTIAN HIEROGLYPH-13460"))
(test (equal (code-point-name #x17000 *v16*) "TANGUT IDEOGRAPH-17000"))
(test (equal (code-point-name #x18B00 *v16*)
             "KHITAN SMALL SCRIPT CHARACTER-18B00"))
(test (equal (code-point-name #x1B170 *v16*) "NUSHU CHARACTER-1B170"))

; The ends of some ranges.

(test (equal (code-point-name #x33FF *v16*) "SQUARE GAL"))
(test (equal (code-point-name #x3400 *v16*) "CJK UNIFIED IDEOGRAPH-3400"))
(test (equal (code-point-name #x4DBF *v16*) "CJK UNIFIED IDEOGRAPH-4DBF"))
(test (equal (code-point-name #x4DC0 *v16*)
             "HEXAGRAM FOR THE CREATIVE HEAVEN"))
(test (equal (code-point-name #x9FFF *v16*) "CJK UNIFIED IDEOGRAPH-9FFF"))
(test (equal (code-point-name #xA000 *v16*) "YI SYLLABLE IT"))
(test (equal (code-point-name #xFA6D *v16*)
             "CJK COMPATIBILITY IDEOGRAPH-FA6D"))
(test (equal (code-point-name #xFA6E *v16*) "")) ; not assigned
(test (equal (code-point-name #xFA70 *v16*)
             "CJK COMPATIBILITY IDEOGRAPH-FA70"))

; A range of one code point.

(test (equal (code-point-name #x18CFE *v16*) "")) ; not assigned
(test (equal (code-point-name #x18CFF *v16*)
             "KHITAN SMALL SCRIPT CHARACTER-18CFF"))

; The ranges grow from a version to the next.

(test (equal (code-point-name #x187F8 *v16*) ""))
(test (equal (code-point-name #x187F8 *v17*) "TANGUT IDEOGRAPH-187F8"))
(test (equal (code-point-name #x323AF *v16*) "CJK UNIFIED IDEOGRAPH-323AF"))
(test (equal (code-point-name #x323B0 *v16*) ""))
(test (equal (code-point-name #x323B0 *v17*) "CJK UNIFIED IDEOGRAPH-323B0"))
(test (equal (code-point-name #x33479 *v17*) "CJK UNIFIED IDEOGRAPH-33479"))
(test (equal (code-point-name #x3347A *v17*) ""))
(test (equal (code-point-name #x18CD6 *v17*) ""))
(test (equal (code-point-name #x18CD6 *v18*)
             "KHITAN SMALL SCRIPT CHARACTER-18CD6"))

; Unicode 18.0.0 adds two families.

(test (equal (code-point-name #x18E00 *v16*) ""))
(test (equal (code-point-name #x18E00 *v17*) ""))
(test (equal (code-point-name #x18E00 *v18*) "JURCHEN CHARACTER-18E00"))
(test (equal (code-point-name #x19191 *v18*) "JURCHEN CHARACTER-19191"))
(test (equal (code-point-name #x19192 *v18*) ""))
(test (equal (code-point-name #x3D000 *v17*) ""))
(test (equal (code-point-name #x3D000 *v18*) "SMALL SEAL CHARACTER-3D000"))
(test (equal (code-point-name #x3FC3F *v18*) "SMALL SEAL CHARACTER-3FC3F"))
(test (equal (code-point-name #x3FC40 *v18*) ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The code points without a name [Unicode, Section 4.8, rule NR4].

(test (equal (code-point-name #x0000 *v16*) "")) ; a control code
(test (equal (code-point-name #x000A *v16*) "")) ; a control code
(test (equal (code-point-name #x009F *v16*) "")) ; a control code
(test (equal (code-point-name #xD800 *v16*) "")) ; a surrogate code point
(test (equal (code-point-name #xE000 *v16*) "")) ; a private use code point
(test (equal (code-point-name #x10FFFD *v16*) "")) ; a private use code point
(test (equal (code-point-name #xFDD0 *v16*) "")) ; a noncharacter
(test (equal (code-point-name #xFFFF *v16*) "")) ; a noncharacter
(test (equal (code-point-name #x0378 *v16*) "")) ; not assigned
(test (equal (code-point-name #x0378 *v18*) "")) ; not assigned

; The format characters have names.

(test (equal (code-point-name #x00AD *v16*) "SOFT HYPHEN"))
(test (equal (code-point-name #x200D *v16*) "ZERO WIDTH JOINER"))
(test (equal (code-point-name #xFEFF *v16*) "ZERO WIDTH NO-BREAK SPACE"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The loose matching of names [UAX #44, Section 5.9.2, rule UAX44-LM2].

; The key of a string has no spaces, underscores or medial hyphens,
; and its letters are small.

(test (equal (name-loose-key "LATIN SMALL LETTER A") "latinsmalllettera"))
(test (equal (name-loose-key "Latin_Small_Letter_A") "latinsmalllettera"))
(test (equal (name-loose-key "  latin small  letter a ") "latinsmalllettera"))
(test (equal (name-loose-key "LatinSmallLetterA") "latinsmalllettera"))
(test (equal (name-loose-key "ZERO WIDTH SPACE") "zerowidthspace"))
(test (equal (name-loose-key "zero-width space") "zerowidthspace"))
(test (equal (name-loose-key "") ""))

; The examples of medial hyphens in UAX #44.

(test (equal (name-loose-key "CJK COMPATIBILITY IDEOGRAPH-2F800")
             "cjkcompatibilityideograph2f800"))
(test (equal (name-loose-key "BLOCK SEXTANT-136") "blocksextant136"))
(test (equal (name-loose-key "LINEAR A SIGN A709-2 L2") "linearasigna7092l2"))
(test (equal (name-loose-key "DOMINO TILE VERTICAL-06-03")
             "dominotilevertical0603"))

; A hyphen with a space before it or after it is not medial: it is kept.

(test (equal (name-loose-key "TIBETAN MARK TSA -PHRU") "tibetanmarktsa-phru"))
(test (equal (name-loose-key "TIBETAN LETTER -A") "tibetanletter-a"))
(test (equal (name-loose-key "TIBETAN LETTER A") "tibetanlettera"))
(test (equal (name-loose-key "MARCHEN LETTER -A") "marchenletter-a"))
(test (equal (name-loose-key "MARCHEN LETTER A") "marchenlettera"))
(test (equal (name-loose-key "A- B") "a-b"))
(test (equal (name-loose-key "-A") "-a"))
(test (equal (name-loose-key "A-") "a-"))
(test (equal (name-loose-key "A--B") "a--b"))

; So is a hyphen next to an underscore.

(test (equal (name-loose-key "A_-B") "a-b"))

; The medial hyphen of the name of U+1180 is kept;
; U+116C has the same name without it.

(test (equal (name-loose-key "HANGUL JUNGSEONG O-E") "hanguljungseongo-e"))
(test (equal (name-loose-key "hangul_jungseong_o-e") "hanguljungseongo-e"))
(test (equal (name-loose-key "HANGUL JUNGSEONG OE") "hanguljungseongoe"))

; The characters that the matching ignores, and those that it does not.

(test (name-ignored-char-p #\Space))
(test (name-ignored-char-p #\_))
(test (name-ignored-char-p #\Tab))
(test (name-ignored-char-p #\Newline))
(test (name-ignored-char-p (code-char #xA0))) ; NO-BREAK SPACE
(test (not (name-ignored-char-p #\-)))
(test (not (name-ignored-char-p #\A)))
(test (not (name-ignored-char-p #\.)))
(test (equal (name-loose-key "LATIN.SMALL") "latin.small"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From a name to its code point.

; The exact name.

(test (equal (name-code-point "SPACE" *v16*) #x0020))
(test (equal (name-code-point "LATIN SMALL LETTER A" *v16*) #x0061))
(test (equal (name-code-point "GRINNING FACE" *v17*) #x1F600))
(test (equal (name-code-point "TIBETAN LETTER -A" *v16*) #x0F60))
(test (equal (name-code-point "TIBETAN LETTER A" *v16*) #x0F68))
(test (equal (name-code-point "HANGUL JUNGSEONG O-E" *v16*) #x1180))
(test (equal (name-code-point "HANGUL JUNGSEONG OE" *v16*) #x116C))
(test (equal (name-code-point "HANGUL SYLLABLE GA" *v16*) #xAC00))
(test (equal (name-code-point "HANGUL SYLLABLE HIH" *v16*) #xD7A3))
(test (equal (name-code-point "HANGUL SYLLABLE PWILH" *v16*) #xD4DB))
(test (equal (name-code-point "HANGUL SYLLABLE A" *v16*) #xC544))
(test (equal (name-code-point "CJK UNIFIED IDEOGRAPH-4E00" *v16*) #x4E00))
(test (equal (name-code-point "CJK COMPATIBILITY IDEOGRAPH-2F800" *v16*)
             #x2F800))
(test (equal (name-code-point "TANGUT IDEOGRAPH-18D00" *v16*) #x18D00))
(test (equal (name-code-point "KHITAN SMALL SCRIPT CHARACTER-18CFF" *v16*)
             #x18CFF))

; Strings that are not the name of a code point.

(test (not (name-code-point "" *v16*)))
(test (not (name-code-point "NO SUCH NAME" *v16*)))
(test (not (name-code-point "latin small letter a" *v16*)))
(test (not (name-code-point "LATIN SMALL LETTER  A" *v16*)))
(test (not (name-code-point " LATIN SMALL LETTER A" *v16*)))
(test (not (name-code-point "ZERO-WIDTH SPACE" *v16*)))
(test (not (name-code-point "HANGUL SYLLABLE" *v16*)))
(test (not (name-code-point "HANGUL SYLLABLE " *v16*)))
(test (not (name-code-point "HANGUL SYLLABLE X" *v16*)))
(test (not (name-code-point "HANGUL SYLLABLE GAA" *v16*)))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-" *v16*)))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-4e00" *v16*)))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-04E00" *v16*)))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-4DC0" *v16*)))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-F900" *v16*)))
(test (not (name-code-point "CJK COMPATIBILITY IDEOGRAPH-4E00" *v16*)))
(test (not (name-code-point "TANGUT IDEOGRAPH-110000" *v16*)))

; A name of a later version is not a name in an earlier one.

(test (not (name-code-point "ARABIC LETTER NOON WITH RING ABOVE" *v16*)))
(test (equal (name-code-point "ARABIC LETTER NOON WITH RING ABOVE" *v17*)
             #x088F))
(test (not (name-code-point "JURCHEN CHARACTER-18E00" *v17*)))
(test (equal (name-code-point "JURCHEN CHARACTER-18E00" *v18*) #x18E00))
(test (not (name-code-point "CJK UNIFIED IDEOGRAPH-323B0" *v16*)))
(test (equal (name-code-point "CJK UNIFIED IDEOGRAPH-323B0" *v17*) #x323B0))

; Loose matching.

(test (equal (loose-name-code-point "latin small letter a" *v16*) #x0061))
(test (equal (loose-name-code-point "Latin_Small_Letter_A" *v16*) #x0061))
(test (equal (loose-name-code-point "LATINSMALLLETTERA" *v16*) #x0061))
(test (equal (loose-name-code-point "zero-width space" *v16*) #x200B))
(test (equal (loose-name-code-point "Zero Width No Break Space" *v16*)
             #xFEFF))
(test (equal (loose-name-code-point "tibetan letter -a" *v16*) #x0F60))
(test (equal (loose-name-code-point "tibetan letter a" *v16*) #x0F68))
(test (equal (loose-name-code-point "tibetan-letter-a" *v16*) #x0F68))
(test (equal (loose-name-code-point "hangul jungseong o-e" *v16*) #x1180))
(test (equal (loose-name-code-point "hangul jungseong oe" *v16*) #x116C))
(test (equal (loose-name-code-point "hangul syllable pwilh" *v16*) #xD4DB))
(test (equal (loose-name-code-point "HangulSyllableGa" *v16*) #xAC00))
(test (equal (loose-name-code-point "hangul-syllable-a" *v16*) #xC544))
(test (equal (loose-name-code-point "cjk unified ideograph 4e00" *v16*)
             #x4E00))
(test (equal (loose-name-code-point "CJK_Unified_Ideograph-4E00" *v16*)
             #x4E00))
(test (equal (loose-name-code-point "block sextant 23456" *v16*) #x1FB3B))
(test (not (loose-name-code-point "" *v16*)))
(test (not (loose-name-code-point "no such name" *v16*)))
(test (not (loose-name-code-point "latin small letter" *v16*)))
(test (not (loose-name-code-point "latin.small.letter.a" *v16*)))
(test (not (loose-name-code-point "cjk unified ideograph 04e00" *v16*)))
(test (not (loose-name-code-point "cjk unified ideograph 4dc0" *v16*)))
(test (not (loose-name-code-point "hangul syllable" *v16*)))

; The keys of the listed names are stored in a table for each version.

(test (equal (name-key-code-point "latinsmalllettera" *v16*) #x0061))
(test (not (name-key-code-point "LATINSMALLLETTERA" *v16*)))
(test (not (name-key-code-point "latin small letter a" *v16*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rule for the names of the Hangul syllables
; gives the names that the file DerivedName.txt lists for them.

; The names, by the rule, of the code points from S,
; as long as they are Hangul syllables.

(define hangul-syllable-names-from ((s natp) (ver versionp))
  :returns (names string-listp
                  :hints (("Goal" :induct t :in-theory (enable string-listp))))
  (b* ((s (nfix s))
       ((unless (hangul-syllable-p s)) nil))
    (cons (hangul-syllable-name s ver)
          (hangul-syllable-names-from (+ 1 s) ver)))
  :measure (nfix (- #x110000 (nfix s)))
  :hints (("Goal" :in-theory (enable o-p o-finp o<
                                     hangul-syllable-p
                                     code-point-p))))

(test (equal (len *hangul-syllable-names*) 11172))
(test (equal (hangul-syllable-names-from #xAC00 *v16*)
             *hangul-syllable-names*))
(test (equal (hangul-syllable-names-from #xAC00 *v17*)
             *hangul-syllable-names*))
(test (equal (hangul-syllable-names-from #xAC00 *v18*)
             *hangul-syllable-names*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The code points with a name are as many as
; the listed names, the 11,172 Hangul syllables,
; and the code points of the ranges of the names that end in the code point,
; taken together: no code point is counted twice.

; COUNT plus the number of code points of the list that have a name.

(define named-code-point-count ((cps code-point-listp)
                                (ver versionp)
                                (count natp))
  :returns (new-count natp :hints (("Goal" :induct t)))
  (cond ((endp cps) (nfix count))
        ((equal (code-point-name (car cps) ver) "")
         (named-code-point-count (cdr cps) ver count))
        (t (named-code-point-count (cdr cps) ver (+ 1 (nfix count))))))

; The number of code points of the ranges of a list of patterns.

(define name-patterns-size ((patterns name-pattern-listp))
  :returns (size natp :hints (("Goal" :induct t)))
  (if (endp patterns)
      0
    (+ (range-size (name-pattern->range (car patterns)))
       (name-patterns-size (cdr patterns)))))

(test (equal (name-patterns-size (name-patterns *v16*)) 109689))
(test (equal (name-patterns-size (name-patterns *v17*)) 114035))
(test (equal (name-patterns-size (name-patterns *v18*)) 126285))

; The three numbers for a version, added.

(define name-kinds-size ((ver versionp))
  :returns (size natp)
  (+ (treemap::size (listed-names ver))
     (+ 1 (- #xD7A3 #xAC00))
     (name-patterns-size (name-patterns ver))))

(test (equal (name-kinds-size *v16*) 154998))
(test (equal (name-kinds-size *v17*) 159801))
(test (equal (name-kinds-size *v18*) 172808))

(test (equal (named-code-point-count (all-code-points) *v16* 0)
             (name-kinds-size *v16*)))
(test (equal (named-code-point-count (all-code-points) *v17* 0)
             (name-kinds-size *v17*)))
(test (equal (named-code-point-count (all-code-points) *v18* 0)
             (name-kinds-size *v18*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The loose matching ignores white space [UAX #44, Section 5.9.2].
; A string of ACL2 has characters with the codes below 256;
; the ones that NAME-IGNORED-CHAR-P ignores
; are those with the property White_Space, and the underscore.

; Check this for the codes below CODE.

(define name-ignored-chars-below-ok ((code natp) (ver versionp))
  :guard (<= code 256)
  :returns (yes/no booleanp)
  (b* (((when (zp code)) t)
       (code (- code 1)))
    (and (equal (name-ignored-char-p (code-char code))
                (or (white-space-p code ver)
                    (equal code (char-code #\_))))
         (name-ignored-chars-below-ok code ver)))
  :guard-hints (("Goal" :in-theory (enable code-point-p))))

(test (name-ignored-chars-below-ok 256 *v16*))
(test (name-ignored-chars-below-ok 256 *v17*))
(test (name-ignored-chars-below-ok 256 *v18*))
