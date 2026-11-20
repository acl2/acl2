; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some examples of the functions of the library, as tests.
; The thorough tests are in the other books of this directory.

(defmacro test (form)
  `(assert-event ,form))

(defconst *v16* (version-v16.0.0))
(defconst *v17* (version-v17.0.0))
(defconst *v18* (version-v18.0.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Code points and scalar values.

(test (code-point-p 0))
(test (code-point-p #x10FFFF))
(test (not (code-point-p #x110000)))
(test (not (code-point-p -1)))
(test (not (code-point-p #\a)))
(test (scalar-value-p (char-code #\a)))
(test (scalar-value-p #xD7FF)) ; last before the surrogates
(test (code-point-p #xD800)) ; a surrogate is a code point ...
(test (not (scalar-value-p #xD800))) ; ... but not a scalar value
(test (not (scalar-value-p #xDFFF)))
(test (scalar-value-p #xE000)) ; first after the surrogates
(test (surrogate-p #xDBFF))
(test (not (surrogate-p #xE000)))
(test (scalar-value-listp (list #x66 #x6E #x2028)))
(test (not (scalar-value-listp (list #x66 #xD800))))
(test (code-point-listp (list #x66 #xD800)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; XID_Start and XID_Continue.

; ASCII letters start identifiers; the underscore and digits only continue.

(test (xid-start-p (char-code #\a) *v16*))
(test (xid-start-p (char-code #\Z) *v16*))
(test (not (xid-start-p (char-code #\_) *v16*)))
(test (xid-continue-p (char-code #\_) *v16*))
(test (not (xid-start-p (char-code #\0) *v16*)))
(test (xid-continue-p (char-code #\9) *v16*))
(test (not (xid-continue-p (char-code #\Space) *v16*)))
(test (not (xid-continue-p (char-code #\-) *v16*)))

; Other letters start; combining marks only continue.

(test (xid-start-p #x03BB *v16*)) ; GREEK SMALL LETTER LAMDA
(test (xid-start-p #x4E00 *v16*)) ; CJK UNIFIED IDEOGRAPH-4E00
(test (xid-start-p #x00E9 *v16*)) ; LATIN SMALL LETTER E WITH ACUTE
(test (not (xid-start-p #x0301 *v16*))) ; COMBINING ACUTE ACCENT
(test (xid-continue-p #x0301 *v16*))

; ZERO WIDTH JOINER (and ZERO WIDTH NON-JOINER) have XID_Continue;
; it is Unicode Technical Standard #39, Unicode Security Mechanisms,
; not UAX #31, that restricts them.

(test (not (xid-start-p #x200D *v16*))) ; ZERO WIDTH JOINER
(test (xid-continue-p #x200D *v16*))

; Emoji, surrogates, noncharacters and non-code-points have neither.

(test (not (xid-continue-p #x1F600 *v16*))) ; GRINNING FACE
(test (not (xid-continue-p #xD800 *v16*)))
(test (not (xid-continue-p #x10FFFF *v16*)))

; The version matters:
; U+088F ARABIC LETTER NOON WITH RING ABOVE was added in Unicode 17.0.0.

(test (not (xid-start-p #x088F *v16*)))
(test (xid-start-p #x088F *v17*))
(test (xid-start-p #x088F *v18*))

; And U+0558 was added in Unicode 18.0.0.

(test (not (xid-start-p #x0558 *v17*)))
(test (xid-start-p #x0558 *v18*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifiers.

(test (xid-identifier-p (list (char-code #\x) (char-code #\1)) *v16*))
(test (not (xid-identifier-p (list (char-code #\1) (char-code #\x))
                             *v16*)))
(test (not (xid-identifier-p (list (char-code #\a) (char-code #\-))
                             *v16*)))
(test (not (xid-identifier-p nil *v16*)))

; An underscore can continue an identifier but cannot start one.

(test (not (xid-identifier-p (list (char-code #\_) (char-code #\x))
                             *v16*)))
(test (xid-continue-listp (list (char-code #\_) (char-code #\x)) *v16*))
(test (xid-continue-listp nil *v16*))

; An identifier is still one after it is normalized.
; Here the two LATIN SMALL LETTER E WITH ACUTE are decomposed,
; and the letter s and its two combining marks are composed.

(test (xid-identifier-p (nfd '(#x00E9 #x0074 #x00E9) *v16*) *v16*))
(test (xid-identifier-p (nfc '(#x0073 #x0323 #x0307) *v16*) *v16*))

; The XID properties leave out the code points
; that would make this fail [UAX #31, Section 5.1].
; U+0E33 THAI CHARACTER SARA AM is a letter,
; but its NFKC form starts with a combining mark:
; it can continue an identifier and cannot start one.
; The NFKC form of U+037A GREEK YPOGEGRAMMENI starts with a space:
; it can do neither.

(test (not (xid-start-p #x0E33 *v16*)))
(test (xid-continue-p #x0E33 *v16*))
(test (equal (nfkc '(#x0E33) *v16*) '(#x0E4D #x0E32)))
(test (not (xid-continue-p #x037A *v16*)))
(test (equal (nfkc '(#x037A) *v16*) '(#x0020 #x0345)))

; Something that is not an identifier can have an NFKC form that is one,
; but not an NFC form that is one:
; the NFKC form of U+2122 TRADE MARK SIGN is TM.

(test (not (xid-identifier-p '(#x2122) *v16*)))
(test (not (xid-identifier-p (nfc '(#x2122) *v16*) *v16*)))
(test (equal (nfkc '(#x2122) *v16*)
             (list (char-code #\T) (char-code #\M))))
(test (xid-identifier-p (nfkc '(#x2122) *v16*) *v16*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pattern_White_Space.

(test (pattern-white-space-p (char-code #\Space) *v16*))
(test (pattern-white-space-p (char-code #\Tab) *v16*))
(test (pattern-white-space-p (char-code #\Newline) *v16*))
(test (pattern-white-space-p #x0085 *v16*)) ; NEXT LINE
(test (pattern-white-space-p #x200E *v16*)) ; LEFT-TO-RIGHT MARK
(test (pattern-white-space-p #x2028 *v16*)) ; LINE SEPARATOR
(test (not (pattern-white-space-p #x00A0 *v16*))) ; NO-BREAK SPACE
(test (not (pattern-white-space-p #x3000 *v16*))) ; IDEOGRAPHIC SPACE
(test (not (pattern-white-space-p (char-code #\a) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bidirectional controls.

(test (bidi-control-p #x202E *v16*)) ; RIGHT-TO-LEFT OVERRIDE
(test (equal (bidi-explicit-formatting-class #x202E *v16*)
             (bidi-formatting-class-rlo)))
(test (bidi-explicit-formatting-p #x2066 *v16*)) ; LEFT-TO-RIGHT ISOLATE
(test (equal (bidi-explicit-formatting-class #x2069 *v17*)
             (bidi-formatting-class-pdi)))
(test (bidi-control-p #x200F *v16*)) ; RIGHT-TO-LEFT MARK is a control ...
(test (not (bidi-explicit-formatting-p #x200F *v16*))) ; ... but not explicit
(test (not (bidi-control-p (char-code #\a) *v16*)))
(test (not (bidi-explicit-formatting-class (char-code #\a) *v16*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Combining classes.

(test (equal (canonical-combining-class (char-code #\a) *v16*) 0))
(test (equal (canonical-combining-class #x0301 *v16*) 230)) ; above
(test (equal (canonical-combining-class #x0323 *v16*) 220)) ; below
(test (equal (canonical-combining-class #x0345 *v16*) 240)) ; iota subscript
(test (equal (canonical-combining-class #xD800 *v16*) 0))
(test (starter-p (char-code #\a) *v16*))
(test (not (starter-p #x0301 *v16*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Decompositions and compositions.

; U+1E69 LATIN SMALL LETTER S WITH DOT BELOW AND DOT ABOVE
; maps to U+1E63 U+0307, and U+1E63 maps to U+0073 U+0323.

(test (mv-let (canonical mapping) (decomposition-mapping #x1E69 *v16*)
        (and canonical (equal mapping '(#x1E63 #x0307)))))
(test (equal (decomposition #x1E69 nil *v16*) '(#x0073 #x0323 #x0307)))
(test (equal (composition #x0073 #x0323 *v16*) #x1E63))
(test (equal (composition #x1E63 #x0307 *v16*) #x1E69))
(test (not (composition #x0073 #x0073 *v16*)))

; U+FB01 LATIN SMALL LIGATURE FI has a compatibility mapping only.

(test (mv-let (canonical mapping) (decomposition-mapping #xFB01 *v16*)
        (and (not canonical) (equal mapping '(#x0066 #x0069)))))
(test (equal (decomposition #xFB01 nil *v16*) '(#xFB01)))
(test (equal (decomposition #xFB01 t *v16*) '(#x0066 #x0069)))

; U+212B ANGSTROM SIGN maps to U+00C5, which is why nothing composes to it.

(test (equal (decomposition #x212B nil *v16*) '(#x0041 #x030A)))
(test (full-composition-exclusion-p #x212B *v16*))
(test (equal (composition #x0041 #x030A *v16*) #x00C5))

; Hangul: U+D55C is the syllable HAN = H (U+1112) A (U+1161) N (U+11AB),
; and U+D558 is the syllable HA.

(test (hangul-syllable-p #xD55C))
(test (hangul-syllable-p #xAC00)) ; the first syllable
(test (hangul-syllable-p #xD7A3)) ; the last syllable
(test (not (hangul-syllable-p #xD7A4)))
(test (hangul-lv-syllable-p #xD558))
(test (not (hangul-lv-syllable-p #xD55C)))
(test (equal (hangul-syllable-decomposition #xD55C) '(#x1112 #x1161 #x11AB)))
(test (equal (hangul-syllable-decomposition-mapping #xD55C) '(#xD558 #x11AB)))
(test (equal (hangul-syllable-decomposition #xD558) '(#x1112 #x1161)))
(test (equal (hangul-composition #x1112 #x1161) #xD558))
(test (equal (hangul-composition #xD558 #x11AB) #xD55C))
(test (not (hangul-composition #xD55C #x11AB))) ; an LVT syllable is complete

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Normalization.

; The marks below and above a letter are put in a canonical order,
; and the letter composes with both.

(test (equal (nfd '(#x0073 #x0307 #x0323) *v16*) '(#x0073 #x0323 #x0307)))
(test (equal (nfc '(#x0073 #x0307 #x0323) *v16*) '(#x1E69)))
(test (equal (nfc '(#x1E9B #x0323) *v16*) '(#x1E9B #x0323)))
(test (equal (nfkc '(#x1E9B #x0323) *v16*) '(#x1E69)))
(test (equal (nfkd '(#x1E9B #x0323) *v16*) '(#x0073 #x0323 #x0307)))

; A mark that does not compose blocks the marks of its class after it,
; but not the marks of a higher class.

(test (equal (nfc '(#x0061 #x0305 #x0301) *v16*) '(#x0061 #x0305 #x0301)))
(test (equal (nfc '(#x0061 #x031B #x0301) *v16*) '(#x00E1 #x031B)))
(test (equal (nfc '(#x0061 #x0323 #x0301) *v16*) '(#x1EA1 #x0301)))

; Hangul syllables are decomposed and recomposed.

(test (equal (nfd '(#xD55C #xAE00) *v16*)
             '(#x1112 #x1161 #x11AB #x1100 #x1173 #x11AF)))
(test (equal (nfc '(#x1112 #x1161 #x11AB #x1100 #x1173 #x11AF) *v16*)
             '(#xD55C #xAE00)))

; ASCII is left alone; so is a lone surrogate.

(test (equal (nfc '(#x66 #x6F #x6F) *v17*) '(#x66 #x6F #x6F)))
(test (equal (nfkc '(#xD800) *v17*) '(#xD800)))

; U+16D6A KIRAT RAI VOWEL SIGN AU, added in Unicode 16.0.0,
; has a decomposition of depth two.

(test (equal (nfd '(#x16D6A) *v16*) '(#x16D63 #x16D67 #x16D67)))
(test (equal (nfd '(#x16D6A) *v17*) '(#x16D63 #x16D67 #x16D67)))

; Being in Normalization Form C.
; A letter and a mark that compose are not in that form,
; and the letter that they compose to is.
; A letter and a mark that do not compose are in that form.
; U+212B ANGSTROM SIGN is not: its form is U+00C5.
; Marks that are not in canonical order are not in that form.

(test (not (nfc-memberp '(#x0065 #x0301) *v16*)))
(test (nfc-memberp '(#x00E9) *v16*))
(test (nfc-memberp '(#x0071 #x0301) *v16*))
(test (not (nfc-memberp '(#x212B) *v16*)))
(test (nfc-memberp '(#x00C5) *v16*))
(test (not (nfc-memberp '(#x0071 #x0307 #x0323) *v16*)))
(test (nfc-memberp '(#x0071 #x0323 #x0307) *v16*))
(test (nfc-memberp '(#x66 #x6F #x6F) *v17*))
(test (nfc-memberp nil *v17*))

; Being in the other three forms.
; U+00E9 LATIN SMALL LETTER E WITH ACUTE is in NFC and NFKC,
; and its decomposition is in NFD and NFKD.
; U+00B5 MICRO SIGN is in NFD and NFC;
; its compatibility decomposition, U+03BC GREEK SMALL LETTER MU,
; is in all four forms.

(test (not (nfd-memberp '(#x00E9) *v16*)))
(test (nfd-memberp '(#x0065 #x0301) *v16*))
(test (nfkc-memberp '(#x00E9) *v16*))
(test (nfkd-memberp '(#x0065 #x0301) *v16*))
(test (nfd-memberp '(#x00B5) *v16*))
(test (nfc-memberp '(#x00B5) *v16*))
(test (not (nfkd-memberp '(#x00B5) *v16*)))
(test (not (nfkc-memberp '(#x00B5) *v16*)))
(test (nfkd-memberp '(#x03BC) *v16*))
(test (nfkc-memberp '(#x03BC) *v16*))
(test (nfd-memberp '(#x03BC) *v16*))
(test (nfc-memberp '(#x03BC) *v16*))

; Canonical and compatibility equivalence.
; U+00E9 LATIN SMALL LETTER E WITH ACUTE and its decomposition
; are canonical equivalents, and so compatibility equivalents.
; Two marks of different classes are canonical equivalents in either order;
; two marks of the same class are not.
; U+212B ANGSTROM SIGN and U+00C5 are canonical equivalents.
; U+FB01 LATIN SMALL LIGATURE FI and the letters f, i
; are compatibility equivalents, but not canonical equivalents.
; U+2122 TRADE MARK SIGN and the letters T, M are compatibility equivalents;
; the letters are an identifier, and the sign is not.

(test (canonical-equivalent-p '(#x00E9) '(#x0065 #x0301) *v16*))
(test (compatibility-equivalent-p '(#x00E9) '(#x0065 #x0301) *v16*))
(test (canonical-equivalent-p '(#x0071 #x0307 #x0323)
                              '(#x0071 #x0323 #x0307)
                              *v16*))
(test (not (canonical-equivalent-p '(#x0071 #x0301 #x0307)
                                   '(#x0071 #x0307 #x0301)
                                   *v16*)))
(test (canonical-equivalent-p '(#x212B) '(#x00C5) *v16*))
(test (not (canonical-equivalent-p '(#x0065) '(#x00E9) *v16*)))
(test (compatibility-equivalent-p '(#xFB01) '(#x66 #x69) *v16*))
(test (not (canonical-equivalent-p '(#xFB01) '(#x66 #x69) *v16*)))
(test (compatibility-equivalent-p '(#x2122) '(#x54 #x4D) *v17*))
(test (xid-identifier-p '(#x54 #x4D) *v17*))
(test (not (xid-identifier-p '(#x2122) *v17*)))
(test (canonical-equivalent-p nil nil *v18*))

; The dollar sign and the underscore, at the start of a list, are left alone,
; and what follows them is normalized as if they were not there.

(test (optional-start-p (char-code #\$)))
(test (optional-start-p (char-code #\_)))
(test (not (optional-start-p (char-code #\a))))
(test (not (xid-start-p (char-code #\_) *v16*)))
(test (xid-continue-p (char-code #\_) *v16*))
(test (not (xid-continue-p (char-code #\$) *v16*)))
(test (equal (nfc '(#x5F #x0065 #x0301) *v16*) '(#x5F #x00E9)))
(test (equal (nfc '(#x5F #x0301 #x0065 #x0301) *v16*) '(#x5F #x0301 #x00E9)))
(test (equal (nfd '(#x24 #x00E9) *v16*) '(#x24 #x0065 #x0301)))
(test (equal (nfkc '(#x24 #xFB01) *v17*) '(#x24 #x66 #x69)))
(test (nfc-memberp '(#x5F #x00E9) *v18*))
(test (not (nfc-memberp '(#x5F #x0065 #x0301) *v18*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Quick checks.

(test (equal (nfc-quick-check (char-code #\a) *v16*)
             (quick-check-value-yes)))
(test (equal (nfc-quick-check #x0301 *v16*)
             (quick-check-value-maybe)))
(test (equal (nfc-quick-check #x212B *v16*)
             (quick-check-value-no)))
(test (equal (nfd-quick-check #x00E9 *v16*)
             (quick-check-value-no)))
(test (equal (nfd-quick-check #x0301 *v16*)
             (quick-check-value-yes)))
(test (equal (nfkc-quick-check #xFB01 *v16*)
             (quick-check-value-no)))

; The quick check of a list, for the two decomposed forms:
; every code point has the value `yes', and the list is in canonical order.
; U+00E9 LATIN SMALL LETTER E WITH ACUTE has the value `no' for both forms.
; U+00B5 MICRO SIGN has the value `yes' for NFD and `no' for NFKD.
; Two marks that are out of canonical order have the value `yes'.

(test (nfd-quick-check-yes-p #x0065 *v16*))
(test (not (nfd-quick-check-yes-p #x00E9 *v16*)))
(test (nfd-quick-check-yes-p #x00B5 *v16*))
(test (not (nfkd-quick-check-yes-p #x00B5 *v16*)))
(test (nfd-quick-check-yes-listp '(#x0065 #x0301) *v16*))
(test (nfkd-quick-check-yes-listp '(#x0065 #x0301) *v16*))
(test (not (nfd-quick-check-yes-listp '(#x0061 #x00E9) *v17*)))
(test (nfd-quick-check-yes-listp '(#x0071 #x0307 #x0323) *v18*))
(test (not (canonically-ordered-p '(#x0071 #x0307 #x0323) *v18*)))
(test (not (nfd-memberp '(#x0071 #x0307 #x0323) *v18*)))
(test (canonically-ordered-p '(#x0071 #x0323 #x0307) *v18*))
(test (nfd-memberp '(#x0071 #x0323 #x0307) *v18*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; General_Category: one code point for each of the thirty values.

(defmacro test-general-category (cp ver constructor)
  `(test (equal (code-point-general-category ,cp ,ver) (,constructor))))

(test-general-category #x0041 *v17* general-category-uppercase-letter) ; A
(test-general-category #x0061 *v17* general-category-lowercase-letter) ; a
(test-general-category #x01C5 *v17* general-category-titlecase-letter)
(test-general-category #x02B0 *v17* general-category-modifier-letter)
(test-general-category #x4E00 *v17* general-category-other-letter)
(test-general-category #x0301 *v17* general-category-nonspacing-mark)
(test-general-category #x0903 *v17* general-category-spacing-mark)
(test-general-category #x20DD *v17* general-category-enclosing-mark)
(test-general-category #x0030 *v17* general-category-decimal-number) ; 0
(test-general-category #x2160 *v17* general-category-letter-number)
(test-general-category #x00B2 *v17* general-category-other-number)
(test-general-category #x005F *v17* general-category-connector-punctuation)
(test-general-category #x002D *v17* general-category-dash-punctuation)
(test-general-category #x0028 *v17* general-category-open-punctuation)
(test-general-category #x0029 *v17* general-category-close-punctuation)
(test-general-category #x00AB *v17* general-category-initial-punctuation)
(test-general-category #x00BB *v17* general-category-final-punctuation)
(test-general-category #x0021 *v17* general-category-other-punctuation)
(test-general-category #x002B *v17* general-category-math-symbol)
(test-general-category #x0024 *v17* general-category-currency-symbol)
(test-general-category #x005E *v17* general-category-modifier-symbol)
(test-general-category #x00A9 *v17* general-category-other-symbol)
(test-general-category #x0020 *v17* general-category-space-separator)
(test-general-category #x2028 *v17* general-category-line-separator)
(test-general-category #x2029 *v17* general-category-paragraph-separator)
(test-general-category #x0000 *v17* general-category-control)
(test-general-category #x200D *v17* general-category-format)
(test-general-category #xD800 *v17* general-category-surrogate)
(test-general-category #xE000 *v17* general-category-private-use)
(test-general-category #x0378 *v17* general-category-unassigned)
(test-general-category #x10FFFF *v17* general-category-unassigned)

; The property is not stable:
; U+0295 LATIN LETTER PHARYNGEAL VOICED FRICATIVE changed in Unicode 17.0.0.

(test-general-category #x0295 *v16* general-category-lowercase-letter)
(test-general-category #x0295 *v17* general-category-other-letter)
(test-general-category #x0295 *v18* general-category-other-letter)

; Abbreviations and major classes.

(test (equal (general-category-abbreviation
              (code-point-general-category #x0041 *v17*))
             "Lu"))
(test (equal (general-category-abbreviation (general-category-unassigned))
             "Cn"))
(test (general-category-letter-p (code-point-general-category #x4E00 *v17*)))
(test (general-category-cased-letter-p
       (code-point-general-category #x01C5 *v17*)))
(test (not (general-category-cased-letter-p
            (code-point-general-category #x4E00 *v17*))))
(test (general-category-mark-p (code-point-general-category #x0301 *v17*)))
(test (general-category-number-p (code-point-general-category #x2160 *v17*)))
(test (general-category-punctuation-p
       (code-point-general-category #x005F *v17*)))
(test (general-category-symbol-p (code-point-general-category #x002B *v17*)))
(test (general-category-separator-p
       (code-point-general-category #x2028 *v17*)))
(test (general-category-other-p (code-point-general-category #xD800 *v17*)))
(test (not (general-category-letter-p
            (code-point-general-category #x0030 *v17*))))

; Assigned code points.  U+088F was assigned in Unicode 17.0.0
; and U+0558 in Unicode 18.0.0.  Surrogates and private-use code points
; count as assigned; noncharacters do not.

(test (assigned-p #x0041 *v16*))
(test (not (assigned-p #x0378 *v18*)))
(test (not (assigned-p #x088F *v16*)))
(test (assigned-p #x088F *v17*))
(test (not (assigned-p #x0558 *v17*)))
(test (assigned-p #x0558 *v18*))
(test (assigned-p #xD800 *v16*))
(test (assigned-p #xE000 *v16*))
(test (not (assigned-p #xFFFF *v16*)))

; The code points that have a value, as ranges.

(test (equal (general-category-ranges (general-category-line-separator) *v17*)
             (list (range #x2028 #x2028))))
(test (equal (general-category-ranges (general-category-surrogate) *v16*)
             (list (range #xD800 #xDFFF))))
(test (equal (range-list-size
              (general-category-ranges (general-category-format) *v17*))
             170))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Default_Ignorable_Code_Point.

(test (default-ignorable-p #x00AD *v17*)) ; SOFT HYPHEN
(test (default-ignorable-p #x200D *v17*)) ; ZERO WIDTH JOINER
(test (default-ignorable-p #xFE0F *v17*)) ; VARIATION SELECTOR-16
(test (default-ignorable-p #xE0FFF *v17*)) ; unassigned, reserved for these
(test (not (default-ignorable-p #x0041 *v17*)))
(test (not (default-ignorable-p #x0600 *v17*))) ; ARABIC NUMBER SIGN

; Variation_Selector and Join_Control.

(test (variation-selector-p #x180B *v16*))
(test (variation-selector-p #xFE0F *v17*))
(test (variation-selector-p #xE01EF *v18*))
(test (not (variation-selector-p #xFE10 *v17*)))
(test (not (variation-selector-p #x180E *v17*))) ; MONGOLIAN VOWEL SEPARATOR
(test (join-control-p #x200C *v16*)) ; ZERO WIDTH NON-JOINER
(test (join-control-p #x200D *v18*)) ; ZERO WIDTH JOINER
(test (not (join-control-p #x200B *v17*))) ; ZERO WIDTH SPACE

; Noncharacter_Code_Point.

(test (noncharacter-p #xFDD0 *v16*))
(test (noncharacter-p #xFDEF *v16*))
(test (noncharacter-p #xFFFE *v17*))
(test (noncharacter-p #x1FFFF *v17*))
(test (noncharacter-p #x10FFFF *v18*))
(test (not (noncharacter-p #xFDF0 *v17*)))
(test (not (noncharacter-p #xFFFD *v17*))) ; REPLACEMENT CHARACTER

; Deprecated and Prepended_Concatenation_Mark.

(test (deprecated-p #x0149 *v17*)) ; LATIN SMALL LETTER N PRECEDED BY APOSTROPHE
(test (deprecated-p #xE0001 *v17*)) ; LANGUAGE TAG
(test (not (deprecated-p #x0041 *v17*)))
(test (prepended-concatenation-mark-p #x0600 *v17*)) ; ARABIC NUMBER SIGN
(test (prepended-concatenation-mark-p #x06DD *v17*)) ; ARABIC END OF AYAH
(test (not (prepended-concatenation-mark-p #x0041 *v17*)))

; Pattern_Syntax.

(test (pattern-syntax-p (char-code #\+) *v16*))
(test (pattern-syntax-p (char-code #\() *v16*))
(test (pattern-syntax-p #x2190 *v17*)) ; LEFTWARDS ARROW
(test (not (pattern-syntax-p (char-code #\_) *v16*)))
(test (not (pattern-syntax-p (char-code #\a) *v16*)))
(test (not (pattern-syntax-p (char-code #\Space) *v16*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The compact way of writing a list of runs of General_Category:
; each triple becomes a run built by the typed constructors.

(test (equal (general-category-run-table
              (#x0041 #x005A "Lu")
              (#x005B #x005B "Ps"))
             (list (general-category-run #x0041
                                         #x005A
                                         (general-category-uppercase-letter))
                   (general-category-run #x005B
                                         #x005B
                                         (general-category-open-punctuation)))))
(test (general-category-run-listp
       (general-category-run-table (#x0000 #x001F "Cc") (#x0020 #x0020 "Zs"))))
(test (equal (general-category-run-table) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The code points that compose with others.

; The letter s composes with a combining mark after it;
; U+0307 COMBINING DOT ABOVE composes with a letter before it.
; The letter q composes with nothing, and neither does a parenthesis.
; The equals sign composes with U+0338 COMBINING LONG SOLIDUS OVERLAY.

(test (composes-with-following-p #x0073 *v16*))
(test (not (composes-with-previous-p #x0073 *v16*)))
(test (composes-with-previous-p #x0307 *v16*))
(test (not (composes-with-following-p #x0071 *v16*)))
(test (not (composes-with-following-p #x0028 *v16*)))
(test (composes-with-following-p #x003D *v16*))
(test (composes-with-previous-p #x0338 *v16*))
(test (equal (composition #x003D #x0338 *v16*) #x2260))

; A composite can compose again:
; U+1E63 LATIN SMALL LETTER S WITH DOT BELOW composes with U+0307.

(test (composes-with-following-p #x1E63 *v16*))

; Hangul: a leading consonant and an LV syllable compose with what follows;
; a vowel and a trailing consonant compose with what precedes;
; an LVT syllable composes with nothing.

(test (composes-with-following-p #x1112 *v16*))
(test (composes-with-following-p #xD558 *v16*))
(test (composes-with-previous-p #x1161 *v16*))
(test (composes-with-previous-p #x11AB *v16*))
(test (not (composes-with-following-p #xD55C *v16*)))
(test (not (composes-with-previous-p #xD55C *v16*)))

; The sets of the first and of the second code points of the pairs
; that compose to primary composites have the same sizes in the three versions.

(test (equal (treeset::cardinality (canonical-composition-firsts *v16*)) 391))
(test (equal (treeset::cardinality (canonical-composition-firsts *v17*)) 391))
(test (equal (treeset::cardinality (canonical-composition-firsts *v18*)) 391))
(test (equal (treeset::cardinality (canonical-composition-seconds *v16*)) 72))
(test (equal (treeset::cardinality (canonical-composition-seconds *v17*)) 72))
(test (equal (treeset::cardinality (canonical-composition-seconds *v18*)) 72))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Code points that are inert under normalization.

; ASCII punctuation, digits and the space are inert,
; except for the three characters < = >.
; Of the ASCII letters, only Q and q are.

(test (normalization-inert-p #x0028 *v16*))
(test (normalization-inert-p #x003B *v16*))
(test (normalization-inert-p #x0030 *v16*))
(test (normalization-inert-p #x0020 *v16*))
(test (not (normalization-inert-p #x003D *v16*)))
(test (not (normalization-inert-p #x0041 *v16*)))
(test (normalization-inert-p #x0051 *v16*))
(test (normalization-inert-p #x0071 *v16*))

; U+2028 LINE SEPARATOR and U+200B ZERO WIDTH SPACE are inert.
; U+00A0 NO-BREAK SPACE and U+3000 IDEOGRAPHIC SPACE are not:
; they have compatibility decompositions.
; A combining mark is not: it is not a starter.
; The Hangul jamo and syllables are not.

(test (normalization-inert-p #x2028 *v16*))
(test (normalization-inert-p #x200B *v16*))
(test (not (normalization-inert-p #x00A0 *v16*)))
(test (not (normalization-inert-p #x3000 *v16*)))
(test (not (normalization-inert-p #x0301 *v16*)))
(test (not (normalization-inert-p #x1112 *v16*)))
(test (not (normalization-inert-p #xD55C *v16*)))

; A code point that is not assigned is inert:
; U+0558 before Unicode 18.0.0.

(test (normalization-inert-p #x0558 *v17*))

; What is before and what is after a parenthesis is normalized separately.
; The equals sign is different: it composes with the mark after it.

(test (equal (nfc '(#x0065 #x0301 #x0028 #x0073 #x0307 #x0323) *v16*)
             (append (nfc '(#x0065 #x0301) *v16*)
                     (list #x0028)
                     (nfc '(#x0073 #x0307 #x0323) *v16*))))
(test (equal (nfc '(#x0028 #x0338) *v16*) '(#x0028 #x0338)))
(test (equal (nfc '(#x003D #x0338) *v16*) '(#x2260)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Where ASCII code points of the canonical forms come from.

; U+037E GREEK QUESTION MARK becomes a semicolon,
; U+1FEF GREEK VARIA becomes a grave accent,
; and U+212A KELVIN SIGN becomes the letter K.

(test (equal (nfc '(#x037E) *v16*) '(#x003B)))
(test (equal (nfc '(#x1FEF) *v16*) '(#x0060)))
(test (equal (nfc '(#x212A) *v16*) '(#x004B)))
(test (equal (nfd '(#x037E) *v18*) '(#x003B)))

; The letter A comes out of U+00C0 LATIN CAPITAL LETTER A WITH GRAVE
; in NFD, and not in NFC.

(test (member-equal #x0041 (nfd '(#x00C0) *v16*)))
(test (not (member-equal #x0041 (nfc '(#x00C0) *v16*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The code points that the composed forms change.

; U+00A0 NO-BREAK SPACE is changed by NFKC and not by NFC.
; U+037E GREEK QUESTION MARK is changed by both.
; U+00C5 LATIN CAPITAL LETTER A WITH RING ABOVE is changed by neither.
; These are the code points whose quick check value is `no'.

(test (nfkc-changes-p #x00A0 *v16*))
(test (not (nfc-changes-p #x00A0 *v16*)))
(test (nfc-changes-p #x037E *v16*))
(test (nfkc-changes-p #x037E *v16*))
(test (not (nfc-changes-p #x00C5 *v16*)))
(test (not (nfkc-changes-p #x00C5 *v16*)))
(test (quick-check-value-case (nfkc-quick-check #x00A0 *v16*) :no))
(test (quick-check-value-case (nfc-quick-check #x00A0 *v16*) :yes))

; A combining mark alone is not changed, although its value is `maybe'.

(test (not (nfc-changes-p #x0301 *v16*)))
(test (quick-check-value-case (nfc-quick-check #x0301 *v16*) :maybe))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Stream-Safe Text Format.

; A letter followed by 30 combining marks is in the format;
; with 31 marks it is not,
; and the process puts U+034F COMBINING GRAPHEME JOINER before the last one.

(test (stream-safe-p (cons #x0061 (make-list 30 :initial-element #x0301))
                     *v16*))
(test (not (stream-safe-p (cons #x0061
                                (make-list 31 :initial-element #x0301))
                          *v16*)))
(test (equal (stream-safe-process
              (cons #x0061 (make-list 31 :initial-element #x0301))
              *v16*)
             (append (cons #x0061 (make-list 30 :initial-element #x0301))
                     (list #x034F #x0301))))
(test (stream-safe-p (stream-safe-process
                      (cons #x0061 (make-list 100 :initial-element #x0301))
                      *v16*)
                     *v16*))

; The count is taken in Normalization Form KD.
; U+0F73 TIBETAN VOWEL SIGN II is a starter,
; but its decomposition is two non-starters.
; So 15 of them in a row are in the format, and 16 are not;
; the process puts the joiner before the sixteenth.

(test (starter-p #x0F73 *v16*))
(test (equal (decomposition #x0F73 t *v16*) '(#x0F71 #x0F72)))
(test (not (starter-p #x0F71 *v16*)))
(test (not (starter-p #x0F72 *v16*)))
(test (stream-safe-p (make-list 15 :initial-element #x0F73) *v16*))
(test (not (stream-safe-p (make-list 16 :initial-element #x0F73) *v16*)))
(test (equal (stream-safe-process (make-list 16 :initial-element #x0F73)
                                  *v16*)
             (append (make-list 15 :initial-element #x0F73)
                     (list #x034F #x0F73))))

; ASCII text is in the format, and the process leaves it alone.

(test (stream-safe-p '(#x66 #x6F #x6F) *v17*))
(test (equal (stream-safe-process '(#x66 #x6F #x6F) *v17*)
             '(#x66 #x6F #x6F)))
(test (equal (stream-safe-process nil *v18*) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ASCII code points in Normalization Form C.

; A letter that comes out of a decomposition composes again,
; possibly with another mark than the one it came with:
; U+00C5 LATIN CAPITAL LETTER A WITH RING ABOVE and U+0323 COMBINING DOT BELOW
; give U+1EA0 LATIN CAPITAL LETTER A WITH DOT BELOW
; and U+030A COMBINING RING ABOVE.

(test (equal (nfd '(#x00C5 #x0323) *v16*) '(#x0041 #x0323 #x030A)))
(test (equal (nfc '(#x00C5 #x0323) *v16*) '(#x1EA0 #x030A)))
(test (not (member-equal #x0041 (nfc '(#x00C5 #x0323) *v16*))))

; U+226E NOT LESS-THAN is the less-than sign and a mark, and stays composed.

(test (equal (nfd '(#x226E) *v16*) '(#x003C #x0338)))
(test (equal (nfc '(#x226E) *v16*) '(#x226E)))

; A letter that is in the list may not be in its form.

(test (not (member-equal #x0041 (nfc '(#x0041 #x0300) *v16*))))

; The letter K is in the form of U+212A KELVIN SIGN.

(test (member-equal #x004B (nfc '(#x212A) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Being in a form, on the two sides of an inert code point.
; Here the code point is a parenthesis;
; what is before it is in Normalization Form C in the first list
; and not in the second one.

(test (nfc-memberp '(#x00E9 #x0028 #x0073) *v16*))
(test (not (nfc-memberp '(#x0065 #x0301 #x0028 #x0073) *v16*)))
(test (nfd-memberp '(#x0065 #x0301 #x0028 #x0073) *v16*))
(test (not (nfd-memberp '(#x0065 #x0301 #x0028 #x00E9) *v16*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Stream-Safe Text Format and the normalization forms.

; Normalizing does not change whether text is in the format.
; U+00E1 LATIN SMALL LETTER A WITH ACUTE and 30 more acute accents
; are 31 non-starters in a row in Normalization Form KD.

(test (not (stream-safe-p (cons #x00E1 (make-list 30 :initial-element #x0301))
                          *v16*)))
(test (not (stream-safe-p
            (nfd (cons #x00E1 (make-list 30 :initial-element #x0301)) *v16*)
            *v16*)))
(test (not (stream-safe-p
            (nfkc (cons #x00E1 (make-list 30 :initial-element #x0301)) *v16*)
            *v16*)))

; The process keeps text in its normalization form.
; This list is in Normalization Forms C and KC, and so is the result;
; its decomposed form is in Normalization Forms D and KD,
; and so is the result for it.

(test (nfc-memberp (cons #x00E1 (make-list 30 :initial-element #x0301))
                   *v16*))
(test (equal (stream-safe-process
              (cons #x00E1 (make-list 30 :initial-element #x0301))
              *v16*)
             (append (cons #x00E1 (make-list 29 :initial-element #x0301))
                     (list #x034F #x0301))))
(test (nfc-memberp (stream-safe-process
                    (cons #x00E1 (make-list 30 :initial-element #x0301))
                    *v16*)
                   *v16*))
(test (nfkc-memberp (stream-safe-process
                     (cons #x00E1 (make-list 30 :initial-element #x0301))
                     *v16*)
                    *v16*))
(test (nfd-memberp (stream-safe-process
                    (cons #x0061 (make-list 31 :initial-element #x0301))
                    *v16*)
                   *v16*))
(test (nfkd-memberp (stream-safe-process
                     (cons #x0061 (make-list 31 :initial-element #x0301))
                     *v16*)
                    *v16*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Operations on lists of ranges.

; The results are in normal form:
; ranges that overlap or touch are merged, and empty ranges are dropped.

(test (equal (ranges-union (list (range #x41 #x5A))
                           (list (range #x61 #x7A)))
             (list (range #x41 #x5A) (range #x61 #x7A))))
(test (equal (ranges-union (list (range 0 5) (range 20 30))
                           (list (range 6 9) (range 25 40)))
             (list (range 0 9) (range 20 40))))
(test (equal (ranges-normalize
              (list (range 10 20) (range 0 9) (range 15 30) (range 5 3)))
             (list (range 0 30))))
(test (ranges-normalized-p (list (range 0 9) (range 20 40))))
(test (not (ranges-normalized-p (list (range 0 9) (range 10 40)))))
(test (equal (ranges-complement nil)
             (list (range 0 #x10FFFF))))
(test (equal (ranges-complement (list (range 0 #x10FFFF)))
             nil))
(test (equal (ranges-complement (list (range #xD800 #xDFFF)))
             (list (range 0 #xD7FF) (range #xE000 #x10FFFF))))
(test (equal (range-list-code-points (list (range 3 5) (range 9 9)))
             (list 3 4 5 9)))

; The ASCII code points that have XID_Start are the letters;
; those that have XID_Continue and not XID_Start
; are the digits and the underscore.

(test (equal (ranges-intersection (list (range 0 #x7F))
                                  (xid-start-ranges *v16*))
             (list (range #x41 #x5A) (range #x61 #x7A))))
(test (equal (ranges-difference
              (ranges-intersection (xid-continue-ranges *v16*)
                                   (list (range 0 #x7F)))
              (xid-start-ranges *v16*))
             (list (range #x30 #x39) (range #x5F #x5F))))

; No code point has both Pattern_White_Space and Pattern_Syntax;
; the code points of Pattern_White_Space that are not ASCII are five.

(test (equal (ranges-intersection (pattern-white-space-ranges *v16*)
                                  (pattern-syntax-ranges *v16*))
             nil))
(test (equal (ranges-difference (pattern-white-space-ranges *v16*)
                                (list (range 0 #x7F)))
             (list (range #x85 #x85)
                   (range #x200E #x200F)
                   (range #x2028 #x2029))))

; The number of the assigned code points of each version,
; which counts the surrogates and the private-use code points.

(test (equal (range-list-size
              (ranges-complement
               (general-category-ranges (general-category-unassigned) *v16*)))
             294579))
(test (equal (range-list-size
              (ranges-complement
               (general-category-ranges (general-category-unassigned) *v17*)))
             299382))
(test (equal (range-list-size
              (ranges-complement
               (general-category-ranges (general-category-unassigned) *v18*)))
             312389))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From a version to a later one.

(test (version<= *v16* *v16*))
(test (version<= *v16* *v17*))
(test (version<= *v16* *v18*))
(test (not (version<= *v18* *v17*)))

; Unicode 17.0.0 assigns 4,803 code points more than Unicode 16.0.0,
; and Unicode 18.0.0 assigns 13,007 more than Unicode 17.0.0.
; No code point stops being assigned.

(test (equal (range-list-size
              (ranges-difference
               (general-category-ranges (general-category-unassigned) *v16*)
               (general-category-ranges (general-category-unassigned) *v17*)))
             4803))
(test (equal (range-list-size
              (ranges-difference
               (general-category-ranges (general-category-unassigned) *v17*)
               (general-category-ranges (general-category-unassigned) *v18*)))
             13007))
(test (equal (ranges-difference
              (general-category-ranges (general-category-unassigned) *v17*)
              (general-category-ranges (general-category-unassigned) *v16*))
             nil))

; The code points that got XID_Start in Unicode 17.0.0 are 4,647,
; one of them U+088F ARABIC LETTER NOON WITH RING ABOVE;
; no code point lost the property.

(test (equal (range-list-size
              (ranges-difference (xid-start-ranges *v17*)
                                 (xid-start-ranges *v16*)))
             4647))
(test (code-point-in-ranges-p
       #x088F
       (ranges-difference (xid-start-ranges *v17*)
                          (xid-start-ranges *v16*))))
(test (equal (ranges-difference (xid-start-ranges *v16*)
                                (xid-start-ranges *v17*))
             nil))

; The General_Category: the thirty values.

(test (equal (len (general-category-values)) 30))
(test (equal (general-category-abbreviation (car (general-category-values)))
             "Lu"))

; The one change to an existing character, in the supported versions,
; is U+0295 LATIN LETTER PHARYNGEAL VOICED FRICATIVE, in Unicode 17.0.0.
; The other code points whose value is not the same in two versions
; are those that the later version adds.

(test (equal (general-category-changes-of-assigned *v16* *v17*)
             (list (range #x0295 #x0295))))
(test (equal (general-category-changes-of-assigned *v17* *v18*)
             nil))
(test (equal (general-category-changes-of-assigned *v16* *v18*)
             (list (range #x0295 #x0295))))
(test (equal (range-list-size (general-category-changes *v16* *v17*))
             4804))
(test (equal (range-list-size (general-category-changes *v17* *v18*))
             13007))
(test (equal (general-category-changes *v17* *v17*)
             nil))
(test (code-point-in-ranges-p #x088F (general-category-changes *v16* *v17*)))
(test (not (code-point-in-ranges-p (char-code #\a)
                                   (general-category-changes *v16* *v18*))))

; The code points of three values never change.

(test (equal (general-category-ranges (general-category-control) *v18*)
             (list (range #x00 #x1F) (range #x7F #x9F))))
(test (equal (general-category-ranges (general-category-surrogate) *v18*)
             (list (range #xD800 #xDFFF))))
(test (equal (general-category-ranges (general-category-private-use) *v18*)
             (list (range #xE000 #xF8FF)
                   (range #xF0000 #xFFFFD)
                   (range #x100000 #x10FFFD))))

; Normalization is the same in a later version
; for text whose characters are assigned in the earlier one.

(test (assigned-listp '(#x0065 #x0301 #x0028 #xD55C) *v16*))
(test (equal (nfc '(#x0065 #x0301 #x0028 #xD55C) *v18*)
             (nfc '(#x0065 #x0301 #x0028 #xD55C) *v16*)))
(test (equal (nfkd '(#x0065 #x0301 #x0028 #xD55C) *v18*)
             (nfkd '(#x0065 #x0301 #x0028 #xD55C) *v16*)))

; It need not be the same for other text.
; U+1ACF COMBINING DOUBLE CARON was added in Unicode 17.0.0,
; with combining class 230.
; In Unicode 16.0.0 it is not assigned, so its class is 0,
; and U+0323 COMBINING DOT BELOW after it does not move before it;
; in Unicode 17.0.0 the dot below moves and composes with the letter,
; which gives U+1EA1 LATIN SMALL LETTER A WITH DOT BELOW.

(test (not (assigned-p #x1ACF *v16*)))
(test (assigned-p #x1ACF *v17*))
(test (equal (canonical-combining-class #x1ACF *v16*) 0))
(test (equal (canonical-combining-class #x1ACF *v17*) 230))
(test (equal (nfc '(#x0061 #x1ACF #x0323) *v16*)
             '(#x0061 #x1ACF #x0323)))
(test (equal (nfc '(#x0061 #x1ACF #x0323) *v17*)
             '(#x1EA1 #x1ACF)))

; An identifier of a version is an identifier of the later versions.

(test (xid-identifier-p '(#x0078 #x00E9 #x0031) *v16*))
(test (xid-identifier-p '(#x0078 #x00E9 #x0031) *v18*))
(test (not (xid-identifier-p '(#x088F) *v16*)))
(test (xid-identifier-p '(#x088F) *v17*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tables of runs.

(test (equal (script-run-table (#x0041 #x005A "Latn"))
             (list (script-run #x0041 #x005A (script-latin)))))
(test (equal (script-extensions-run-table (#x3001 #x3003 "Bopo" "Hang"))
             (list (script-extensions-run
                    #x3001 #x3003
                    (list (script-bopomofo) (script-hangul))))))
(test (equal (bidi-class-run-table (#x0041 #x005A "L") (#x005B #x0060 "ON"))
             (list (bidi-class-run #x0041 #x005A (bidi-class-left-to-right))
                   (bidi-class-run #x005B #x0060
                                   (bidi-class-other-neutral)))))
(test (equal (block-run-table (#x0000 #x007F "Basic Latin"))
             (list (block-run #x0000 #x007F "Basic Latin"))))
(test (equal (identifier-type-run-table
              (#x018D #x018D "Technical" "Obsolete"))
             (list (identifier-type-run
                    #x018D #x018D
                    (list (identifier-type-technical)
                          (identifier-type-obsolete))))))
(test (script-run-list-covers-p 0 2 (script-run-table (0 1 "Latn")
                                                      (2 2 "Grek"))))
(test (not (script-run-list-covers-p 0 3 (script-run-table (0 1 "Latn")
                                                           (3 3 "Grek")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Script and Script_Extensions.

(test (equal (script-code (script-latin)) "Latn"))
(test (equal (script-name (script-old-hungarian)) "Old_Hungarian"))
(test (equal (len (script-values)) 179))

(test (equal (code-point-script (char-code #\a) *v16*) (script-latin)))
(test (equal (code-point-script #x03B1 *v16*) (script-greek)))
(test (equal (code-point-script #x4E00 *v16*) (script-han)))
(test (equal (code-point-script (char-code #\Space) *v16*) (script-common)))
(test (equal (code-point-script #x0301 *v16*) (script-inherited)))
(test (equal (code-point-script #x0378 *v16*) (script-unknown))) ; unassigned
(test (equal (code-point-script #xE000 *v16*) (script-unknown))) ; private use

; The Sidetic script was added in Unicode 17.0.0.

(test (equal (code-point-script #x10940 *v16*) (script-unknown)))
(test (equal (code-point-script #x10940 *v17*) (script-sidetic)))

; The script extensions of a letter are its script.
; U+3001 IDEOGRAPHIC COMMA has the script Common
; and is used with seven scripts;
; U+0301 COMBINING ACUTE ACCENT has the script Inherited
; and is used with eight.

(test (equal (code-point-script-extensions (char-code #\a) *v16*)
             (list (script-latin))))
(test (equal (code-point-script-extensions #x3001 *v16*)
             (list (script-bopomofo) (script-hangul) (script-han)
                   (script-hiragana) (script-katakana) (script-mongolian)
                   (script-yi))))
(test (equal (len (code-point-script-extensions #x0301 *v16*)) 8))
(test (member-equal (script-latin)
                    (code-point-script-extensions #x0301 *v16*)))
(test (not (member-equal (script-inherited)
                         (code-point-script-extensions #x0301 *v16*))))

; Counts: the code points whose script is Latin,
; and those whose script extensions have Latin.

(test (equal (range-list-size (script-ranges (script-latin) *v16*)) 1487))
(test (equal (range-list-size (script-ranges (script-latin) *v18*)) 1653))
(test (equal (range-list-size (script-extensions-ranges (script-latin) *v16*))
             1555))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bidi_Class.

(defmacro test-bidi-class (cp ver abbreviation)
  `(test (equal (bidi-class-abbreviation (code-point-bidi-class ,cp ,ver))
                ,abbreviation)))

(test-bidi-class (char-code #\a) *v16* "L")
(test-bidi-class #x05D0 *v16* "R") ; HEBREW LETTER ALEF
(test-bidi-class #x0627 *v16* "AL") ; ARABIC LETTER ALEF
(test-bidi-class (char-code #\0) *v16* "EN")
(test-bidi-class #x0660 *v16* "AN") ; ARABIC-INDIC DIGIT ZERO
(test-bidi-class (char-code #\+) *v16* "ES")
(test-bidi-class (char-code #\$) *v16* "ET")
(test-bidi-class (char-code #\,) *v16* "CS")
(test-bidi-class #x0301 *v16* "NSM")
(test-bidi-class (char-code #\Space) *v16* "WS")
(test-bidi-class 9 *v16* "S") ; tab
(test-bidi-class 10 *v16* "B") ; line feed
(test-bidi-class #x202E *v16* "RLO")

; Code points that are not assigned have default classes:
; U+05FF, in the Hebrew block, is R; U+0378 is L.

(test (not (assigned-p #x05FF *v16*)))
(test-bidi-class #x05FF *v16* "R")
(test-bidi-class #x0378 *v16* "L")

(test (bidi-class-right-to-left-p (code-point-bidi-class #x0627 *v16*)))
(test (not (bidi-class-right-to-left-p
            (code-point-bidi-class (char-code #\a) *v16*))))
(test (bidi-class-explicit-formatting-p (code-point-bidi-class #x202E *v16*)))

; The property is not stable:
; U+1B3A BALINESE VOWEL SIGN RA REPA changed in Unicode 18.0.0.

(test-bidi-class #x1B3A *v17* "NSM")
(test-bidi-class #x1B3A *v18* "L")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Block.

(test (equal (code-point-block (char-code #\a) *v16*) "Basic Latin"))
(test (equal (code-point-block #x2118 *v16*) "Letterlike Symbols"))
(test (equal (block-ranges "Letterlike Symbols" *v16*)
             (list (range #x2100 #x214F))))
(test (equal (block-ranges "Letterlike Symbols" *v18*)
             (list (range #x2100 #x214F))))
(test (equal (code-point-block #x2FE0 *v16*) "No_Block"))
(test (equal (block-ranges "No Such Block" *v16*) nil))
(test (equal (len (block-names *v16*)) 338))
(test (equal (len (block-names *v17*)) 346))
(test (equal (len (block-names *v18*)) 353))

; The Sidetic block was added in Unicode 17.0.0.

(test (equal (block-ranges "Sidetic" *v16*) nil))
(test (equal (block-ranges "Sidetic" *v17*) (list (range #x10940 #x1095F))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ID_Start and ID_Continue.

(test (id-start-p (char-code #\a) *v16*))
(test (not (id-start-p (char-code #\_) *v16*)))
(test (id-continue-p (char-code #\_) *v16*))

; U+037A GREEK YPOGEGRAMMENI has ID_Start and not XID_Start;
; U+0E33 THAI CHARACTER SARA AM has ID_Start,
; and of the XID properties only XID_Continue.

(test (id-start-p #x037A *v16*))
(test (not (xid-start-p #x037A *v16*)))
(test (id-start-p #x0E33 *v16*))
(test (not (xid-start-p #x0E33 *v16*)))
(test (xid-continue-p #x0E33 *v16*))
(test (equal (range-list-size (id-start-not-xid-start-ranges)) 23))
(test (equal (range-list-size (id-continue-not-xid-continue-ranges)) 19))

; U+2118 SCRIPT CAPITAL P is a symbol with Other_ID_Start;
; U+00B7 MIDDLE DOT is punctuation with Other_ID_Continue.

(test (other-id-start-p #x2118 *v16*))
(test (id-start-p #x2118 *v16*))
(test (other-id-continue-p #x00B7 *v16*))
(test (id-continue-p #x00B7 *v16*))
(test (not (id-start-p #x00B7 *v16*)))

(test (equal (range-list-size (id-start-ranges *v16*)) 141269))
(test (equal (range-list-size (id-continue-ranges *v18*)) 162100))
(test (not (id-start-p #x088F *v16*)))
(test (id-start-p #x088F *v17*))

; The mathematical notation profile.

(test (id-compat-math-start-p #x2202 *v16*)) ; PARTIAL DIFFERENTIAL
(test (id-compat-math-continue-p #x2202 *v16*))
(test (id-compat-math-continue-p #x00B2 *v16*)) ; SUPERSCRIPT TWO
(test (not (id-compat-math-start-p #x00B2 *v16*)))
(test (not (id-compat-math-continue-p (char-code #\a) *v16*)))
(test (equal (range-list-size (id-compat-math-start-ranges *v18*)) 13))
(test (equal (range-list-size (id-compat-math-continue-ranges *v18*)) 43))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Emoji properties.

; U+1F600 GRINNING FACE.

(test (emoji-p #x1F600 *v16*))
(test (emoji-presentation-p #x1F600 *v16*))
(test (extended-pictographic-p #x1F600 *v16*))

; The number sign is an emoji, because of the keycap sequences,
; but it is not shown as one by default, and it is not a pictograph.

(test (emoji-p (char-code #\#) *v16*))
(test (emoji-component-p (char-code #\#) *v16*))
(test (not (emoji-presentation-p (char-code #\#) *v16*)))
(test (not (extended-pictographic-p (char-code #\#) *v16*)))

; U+00A9 COPYRIGHT SIGN is an emoji that is shown as text by default.

(test (emoji-p #x00A9 *v16*))
(test (not (emoji-presentation-p #x00A9 *v16*)))

(test (emoji-modifier-p #x1F3FB *v16*))
(test (emoji-modifier-base-p #x1F44D *v16*)) ; THUMBS UP SIGN
(test (regional-indicator-p #x1F1E6 *v16*))
(test (emoji-component-p #x200D *v16*)) ; ZERO WIDTH JOINER
(test (not (emoji-p #x200D *v16*)))
(test (not (emoji-p (char-code #\a) *v16*)))

; Emoji are added in each version;
; Extended_Pictographic lost code points in 17.0.0 and in 18.0.0.

(test (equal (range-list-size (emoji-ranges *v16*)) 1431))
(test (equal (range-list-size (emoji-ranges *v17*)) 1438))
(test (equal (range-list-size (emoji-ranges *v18*)) 1447))
(test (equal (range-list-size (extended-pictographic-ranges *v16*)) 3537))
(test (equal (range-list-size (extended-pictographic-ranges *v17*)) 2848))
(test (equal (range-list-size (extended-pictographic-ranges *v18*)) 2830))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Decimal digits.

(test (equal (decimal-digit-value (char-code #\7) *v16*) 7))
(test (equal (decimal-digit-value #x0667 *v16*) 7)) ; ARABIC-INDIC DIGIT SEVEN
(test (equal (decimal-digit-value #xFF19 *v16*) 9)) ; FULLWIDTH DIGIT NINE
(test (not (decimal-digit-value (char-code #\a) *v16*)))
(test (not (decimal-digit-value #x00B2 *v16*))) ; SUPERSCRIPT TWO
(test (not (decimal-digit-p #x2460 *v16*))) ; CIRCLED DIGIT ONE

; The zero of the system of a digit.
; Two digits are of the same system when they have the same zero.

(test (equal (decimal-digit-zero (char-code #\7) *v16*) (char-code #\0)))
(test (equal (decimal-digit-zero #x0667 *v16*) #x0660))
(test (not (equal (decimal-digit-zero (char-code #\7) *v16*)
                  (decimal-digit-zero #x0667 *v16*))))

(test (equal (treemap::size (decimal-digit-values *v16*)) 760))
(test (equal (treemap::size (decimal-digit-values *v18*)) 770))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier_Status and Identifier_Type.

(test (identifier-allowed-p (char-code #\a) *v16*))
(test (equal (code-point-identifier-types (char-code #\a) *v16*)
             (list (identifier-type-recommended))))

; The apostrophe is allowed although it does not have XID_Continue.

(test (identifier-allowed-p (char-code #\') *v16*))
(test (equal (code-point-identifier-types (char-code #\') *v16*)
             (list (identifier-type-inclusion))))
(test (not (xid-continue-p (char-code #\') *v16*)))

(test (not (identifier-allowed-p (char-code #\$) *v16*)))
(test (equal (code-point-identifier-types (char-code #\$) *v16*)
             (list (identifier-type-not-xid))))

; U+00AA FEMININE ORDINAL INDICATOR is changed by NFKC.

(test (equal (code-point-identifier-types #x00AA *v16*)
             (list (identifier-type-not-nfkc))))
(test (nfkc-changes-p #x00AA *v16*))

; A code point can have more than one type.

(test (equal (code-point-identifier-types #x018D *v16*)
             (list (identifier-type-technical) (identifier-type-obsolete))))

; An unassigned code point.

(test (equal (code-point-identifier-types #x0378 *v16*)
             (list (identifier-type-not-character))))

; U+0149 is changed by NFKC but its type is Deprecated.

(test (equal (code-point-identifier-types #x0149 *v16*)
             (list (identifier-type-deprecated))))
(test (nfkc-changes-p #x0149 *v16*))

; The properties are not stable.
; Unicode 17.0.0 restricted many characters that Unicode 16.0.0 allowed,
; among them U+0114 LATIN CAPITAL LETTER E WITH BREVE
; and the ideograph U+4E12.

(test (identifier-allowed-p #x0114 *v16*))
(test (not (identifier-allowed-p #x0114 *v17*)))
(test (equal (code-point-identifier-types #x0114 *v17*)
             (list (identifier-type-uncommon-use))))
(test (identifier-allowed-p #x4E12 *v16*))
(test (not (identifier-allowed-p #x4E12 *v17*)))
(test (identifier-allowed-p #x4E00 *v17*))
(test (equal (range-list-size (identifier-allowed-ranges *v16*)) 112778))
(test (equal (range-list-size (identifier-allowed-ranges *v17*)) 33791))
(test (equal (range-list-size (identifier-allowed-ranges *v18*)) 33792))

; The allowed code points of Unicode 17.0.0
; are the 33,773 that are Recommended and the 18 that are Inclusion.

(test (equal (range-list-size
              (identifier-type-ranges (identifier-type-recommended) *v17*))
             33773))
(test (equal (range-list-size
              (identifier-type-ranges (identifier-type-inclusion) *v17*))
             18))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prototypes of confusable characters.

; U+0441 CYRILLIC SMALL LETTER ES looks like the letter c;
; U+0153 LATIN SMALL LIGATURE OE looks like o followed by e.

(test (equal (prototype #x0441 *v17*) '(#x63)))
(test (equal (prototype #x0153 *v17*) '(#x6F #x65)))
(test (equal (prototype #x63 *v17*) '(#x63)))
(test (own-prototype-p #x63 *v17*))
(test (not (own-prototype-p #x0441 *v17*)))
(test (equal (replace-by-prototypes '(#x0441 #x0153) *v17*)
             '(#x63 #x6F #x65)))

; The digit one, the capital letter I and the vertical line
; look like the small letter l.

(test (equal (prototype #x31 *v17*) '(#x6C)))
(test (equal (prototype #x49 *v17*) '(#x6C)))
(test (equal (prototype #x7C *v17*) '(#x6C)))

; The data changes between versions:
; the prototype of U+01C6 LATIN SMALL LETTER DZ WITH CARON.

(test (equal (prototype #x1C6 *v16*) '(#x64 #x17E)))
(test (equal (prototype #x1C6 *v17*) '(#x64 #x17E)))
(test (equal (prototype #x1C6 *v18*) '(#x64 #x7A #x306)))

; The longest prototype is the one of
; U+FDFA ARABIC LIGATURE SALLALLAHOU ALAYHE WASALLAM.

(test (equal (len (prototype #xFDFA *v17*)) 18))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Skeletons and confusable strings.

; The examples of UTS #39, Section 4.

(defconst *paypal* '(#x70 #x61 #x79 #x70 #x61 #x6C))
(defconst *paypal-with-cyrillic-a* '(#x70 #x430 #x79 #x70 #x430 #x6C))
(defconst *scope* '(#x73 #x63 #x6F #x70 #x65))
(defconst *scope-in-cyrillic* '(#x455 #x441 #x43E #x440 #x435))
(defconst *ljeto-with-digraph* '(#x1C9 #x65 #x74 #x6F))
(defconst *ljeto* '(#x6C #x6A #x65 #x74 #x6F))

(test (equal (skeleton *paypal* *v17*) *paypal*))
(test (equal (skeleton *paypal-with-cyrillic-a* *v17*) *paypal*))
(test (confusable-p *paypal* *paypal-with-cyrillic-a* *v17*))
(test (mixed-script-confusable-p *paypal* *paypal-with-cyrillic-a* *v17*))
(test (not (single-script-confusable-p *paypal* *paypal-with-cyrillic-a*
                                       *v17*)))
(test (not (whole-script-confusable-p *paypal* *paypal-with-cyrillic-a*
                                      *v17*)))

(test (confusable-p *scope* *scope-in-cyrillic* *v17*))
(test (whole-script-confusable-p *scope* *scope-in-cyrillic* *v17*))
(test (mixed-script-confusable-p *scope* *scope-in-cyrillic* *v17*))

(test (confusable-p *ljeto-with-digraph* *ljeto* *v17*))
(test (single-script-confusable-p *ljeto-with-digraph* *ljeto* *v17*))
(test (not (mixed-script-confusable-p *ljeto-with-digraph* *ljeto* *v17*)))

(test (not (confusable-p *paypal* *scope* *v17*)))

; The second step removes the default ignorable code points,
; such as U+200D ZERO WIDTH JOINER and U+00AD SOFT HYPHEN.

(test (equal (remove-default-ignorable '(#x61 #x200D #x62 #xAD) *v17*)
             '(#x61 #x62)))
(test (equal (internal-skeleton '(#x61 #x200D #x62 #xAD) *v17*)
             '(#x61 #x62)))
(test (equal (internal-skeleton '(#x200D) *v17*) nil))

; The first step is canonical decomposition:
; a list and its NFC form have the same skeleton.
; U+00E9 is e with acute; U+0301 is the combining acute accent.

(test (equal (internal-skeleton '(#xE9) *v17*)
             (internal-skeleton '(#x65 #x301) *v17*)))
(test (confusable-p '(#xE9) '(#x65 #x301) *v17*))

; The skeleton is defined here for the lists
; that are displayed in the order in which they are stored.
; U+05D0 HEBREW LETTER ALEF and U+0627 ARABIC LETTER ALEF are not such,
; and neither is U+202E RIGHT-TO-LEFT OVERRIDE.

(test (right-to-left-free-p *paypal-with-cyrillic-a* *v17*))
(test (right-to-left-code-point-p #x05D0 *v17*))
(test (right-to-left-code-point-p #x0627 *v17*))
(test (right-to-left-code-point-p #x202E *v17*))
(test (not (right-to-left-code-point-p #x202D *v17*))) ; LEFT-TO-RIGHT OVERRIDE
(test (not (right-to-left-free-p '(#x61 #x05D0) *v17*)))
(test (not (right-to-left-free-p '(#x61 #x202E #x62) *v17*)))

; Neither are the Arabic-Indic digits, whose class is AN (Arabic_Number):
; U+0661, a space and U+0662 are displayed with U+0662 first.
; The European digits, whose class is EN, are.

(test (right-to-left-code-point-p #x0661 *v17*))
(test (not (right-to-left-free-p '(#x0661 #x20 #x0662) *v17*)))
(test (not (right-to-left-code-point-p #x31 *v17*)))
(test (right-to-left-free-p '(#x31 #x20 #x32) *v17*))

; Taking the internal skeleton a second time changes nothing
; in Unicode 18.0.0.  In Unicode 16.0.0 and 17.0.0 it does, for
; thirteen code points, such as U+01C6 LATIN SMALL LETTER DZ WITH CARON,
; whose internal skeleton ends with U+030C COMBINING CARON,
; which has the prototype U+0306 COMBINING BREVE.

(test (equal (internal-skeleton '(#x1C6) *v17*) '(#x64 #x7A #x30C)))
(test (equal (internal-skeleton '(#x64 #x7A #x30C) *v17*)
             '(#x64 #x7A #x306)))
(test (equal (internal-skeleton '(#x1C6) *v18*) '(#x64 #x7A #x306)))
(test (equal (internal-skeleton '(#x64 #x7A #x306) *v18*)
             '(#x64 #x7A #x306)))
(test (equal (len (internal-skeleton-unstable-code-points *v16*)) 13))
(test (equal (internal-skeleton-unstable-code-points *v16*)
             (internal-skeleton-unstable-code-points *v17*)))
(test (equal (internal-skeleton-unstable-code-points *v18*) nil))
(test (not (internal-skeleton-stable-listp '(#x61 #x1C6) *v17*)))
(test (internal-skeleton-stable-listp '(#x61 #x1C6) *v18*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Mixed-script detection.

; The resolved script set of a list, as :all or as a list of codes.

(define resolved-script-codes ((cps code-point-listp) (ver versionp))
  (b* ((set (resolved-script-set cps ver)))
    (script-set-case set
                     :all :all
                     :of (writing-system-list-codes set.members))))

; The examples of UTS #39, Table 1a, in the order of the table.
; The second and third are "Circle" written in Cyrillic letters,
; and with Cyrillic letters in place of three of the Latin ones;
; the fourth has the digit one in place of the letter l;
; the fifth and the sixth have mathematical sans-serif letters,
; whose Script_Extensions is Common;
; the last two are Japanese.

(test (equal (resolved-script-codes '(#x43 #x69 #x72 #x63 #x6C #x65) *v17*)
             '("Latn")))
(test (equal (resolved-script-codes '(#x421 #x456 #x433 #x441 #x4C0 #x435)
                                    *v17*)
             '("Cyrl")))
(test (equal (resolved-script-codes '(#x421 #x69 #x72 #x441 #x6C #x435)
                                    *v17*)
             nil))
(test (equal (resolved-script-codes '(#x43 #x69 #x72 #x63 #x31 #x65) *v17*)
             '("Latn")))
(test (equal (resolved-script-codes
              '(#x43 #x1D5C2 #x1D5CB #x1D5BC #x1D5C5 #x1D5BE) *v17*)
             '("Latn")))
(test (equal (resolved-script-codes
              '(#x1D5A2 #x1D5C2 #x1D5CB #x1D5BC #x1D5C5 #x1D5BE) *v17*)
             :all))
(test (equal (resolved-script-codes '(#x3006 #x5207) *v17*)
             '("Hani" "Hanb" "Jpan" "Kore")))
(test (equal (resolved-script-codes '(#x306D #x30AC) *v17*)
             '("Jpan")))

(test (single-script-p '(#x43 #x69 #x72 #x63 #x6C #x65) *v17*))
(test (mixed-script-p '(#x421 #x69 #x72 #x441 #x6C #x435) *v17*))
(test (not (single-script-p '(#x421 #x69 #x72 #x441 #x6C #x435) *v17*)))
(test (single-script-p '(#x3006 #x5207) *v17*))
(test (single-script-p nil *v17*))

; From Unicode 18.0.0 on, there is one more writing system, Hntl
; (traditional Han with Latin), which Latin and Han characters have.
; So a list of a Latin letter and a Han character,
; mixed-script before, is single-script.

(test (equal (resolved-script-codes '(#x43 #x69 #x72 #x63 #x6C #x65) *v18*)
             '("Latn" "Hntl")))
(test (equal (resolved-script-codes '(#x3006 #x5207) *v18*)
             '("Hani" "Hanb" "Hntl" "Jpan" "Kore")))
(test (mixed-script-p '(#x61 #x5207) *v17*))
(test (equal (resolved-script-codes '(#x61 #x5207) *v18*) '("Hntl")))
(test (single-script-p '(#x61 #x5207) *v18*))

; The augmented script set of a code point.
; U+30FC KATAKANA-HIRAGANA PROLONGED SOUND MARK
; has both Japanese syllabaries in its Script_Extensions.

(test (equal (script-set-kind (code-point-augmented-script-set #x31 *v17*))
             :all))
(test (equal (writing-system-list-codes
              (script-set-of->members
               (code-point-augmented-script-set #x30FC *v17*)))
             '("Hira" "Kana" "Jpan")))
(test (script-set-in (writing-system-japanese)
                     (code-point-augmented-script-set #x30FC *v17*)))
(test (script-set-in (writing-system-script (script-greek))
                     (code-point-augmented-script-set #x31 *v17*)))
(test (not (script-set-in (writing-system-script (script-greek))
                          (code-point-augmented-script-set #x61 *v17*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Mixed-number detection.

; ASCII digits only; ASCII and Arabic-Indic digits;
; U+0660 ARABIC-INDIC DIGIT ZERO and
; U+06F0 EXTENDED ARABIC-INDIC DIGIT ZERO, of two systems;
; U+09EA BENGALI DIGIT FOUR and the digit eight.

(test (not (mixed-number-systems-p '(#x61 #x31 #x32 #x39) *v17*)))
(test (equal (decimal-digit-zeros '(#x61 #x31 #x32 #x39) *v17*) '(#x30)))
(test (mixed-number-systems-p '(#x31 #x662) *v17*))
(test (mixed-number-systems-p '(#x660 #x6F0) *v17*))
(test (mixed-number-systems-p '(#x9EA #x38) *v17*))
(test (not (mixed-number-systems-p '(#x661 #x662 #x669) *v17*)))
(test (not (mixed-number-systems-p '(#x61 #x62) *v17*)))
(test (equal (decimal-digit-zeros '(#x61 #x62) *v17*) nil))

; U+2163 ROMAN NUMERAL FOUR is not a decimal digit and is ignored.

(test (not (mixed-number-systems-p '(#x31 #x2163) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifier chunks.

; The code points of an ASCII string.

(defun char-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (cons (char-code (car chars))
          (char-codes (cdr chars)))))

(defmacro ascii (string)
  `(char-codes (coerce ,string 'list)))

; The examples of UTS #55, Section 5.1.2.1, in the order of its table.

(test (equal (identifier-chunks (ascii "TypeII") *v17*)
             (list (ascii "Type") (ascii "II"))))
(test (equal (identifier-chunks (ascii "OCaml") *v17*)
             (list (ascii "O") (ascii "Caml"))))

; HTTP followed by a word in Cyrillic letters, the first one uppercase.

(test (equal (identifier-chunks
              (append (ascii "HTTP") '(#x417 #x430 #x43F #x440 #x43E #x441))
              *v17*)
             (list (ascii "HTTP") '(#x417 #x430 #x43F #x440 #x43E #x441))))
(test (equal (identifier-chunks (ascii "UAX9ClauseHL4") *v17*)
             (list (ascii "UAX9") (ascii "Clause") (ascii "HL4"))))
(test (equal (identifier-chunks (ascii "LOUD_SNAKE") *v17*)
             (list (ascii "LOUD") (ascii "_") (ascii "SNAKE"))))
(test (equal (identifier-chunks (ascii "Fancy_Snake") *v17*)
             (list (ascii "Fancy") (ascii "_") (ascii "Snake"))))
(test (equal (identifier-chunks (ascii "snake-kebab") *v17*)
             (list (ascii "snake") (ascii "-") (ascii "kebab"))))

; U+00B7 MIDDLE DOT is Other_Punctuation and makes no boundary.

(test (equal (identifier-chunks
              (append (ascii "Paral") '(#xB7) (ascii "lel")) *v17*)
             (list (append (ascii "Paral") '(#xB7) (ascii "lel")))))
(test (equal (identifier-chunks (ascii "microB") *v17*)
             (list (ascii "micro") (ascii "B"))))

; U+15AF CANADIAN SYLLABICS AIVILIK B is an Other_Letter:
; no boundary after a lowercase letter.

(test (equal (identifier-chunks (append (ascii "micro") '(#x15AF)) *v17*)
             (list (append (ascii "micro") '(#x15AF)))))

; HTTP followed by a word in Devanagari, which has no case.

(test (equal (identifier-chunks
              (append (ascii "HTTP") '(#x938 #x930 #x94D #x935 #x930)) *v17*)
             (list (append (ascii "HTTP")
                           '(#x938 #x930 #x94D #x935 #x930)))))
(test (equal (identifier-chunks (ascii "dromedaryCamel") *v17*)
             (list (ascii "dromedary") (ascii "Camel"))))
(test (equal (identifier-chunks (ascii "snakeELEPHANTSnake") *v17*)
             (list (ascii "snake") (ascii "ELEPHANT") (ascii "Snake"))))

; Marks after a letter count as that letter:
; e, U+0301 COMBINING ACUTE ACCENT, A.

(test (equal (identifier-chunks '(#x65 #x301 #x41) *v17*)
             '((#x65 #x301) (#x41))))

; Titlecase letters.  U+01C5 is Latin: there is a boundary before it,
; and after it when an uppercase letter follows.
; U+1F88 is Greek: a boundary after a lowercase letter,
; here U+03B1 GREEK SMALL LETTER ALPHA, but none before
; U+0391 GREEK CAPITAL LETTER ALPHA.

(test (equal (identifier-chunks '(#x61 #x1C5 #x62) *v17*)
             '((#x61) (#x1C5 #x62))))
(test (equal (identifier-chunks '(#x1C5 #x41) *v17*)
             '((#x1C5) (#x41))))
(test (equal (identifier-chunks '(#x3B1 #x1F88) *v17*)
             '((#x3B1) (#x1F88))))
(test (equal (identifier-chunks '(#x1F88 #x391) *v17*)
             '((#x1F88 #x391))))
(test (chunk-non-greek-titlecase-p #x1C5 *v17*))
(test (not (chunk-non-greek-titlecase-p #x1F88 *v17*)))

; The empty list has no chunk; no chunk is empty.

(test (equal (identifier-chunks nil *v17*) nil))
(test (equal (identifier-chunks (ascii "_") *v17*) (list (ascii "_"))))
(test (equal (identifier-chunks (ascii "__") *v17*)
             (list (ascii "_") (ascii "_"))))

; There are thirty-one titlecase letters in each version: four Latin ones,
; and twenty-seven Greek ones.

(test (equal (range-list-code-points
              (ranges-difference
               (general-category-ranges (general-category-titlecase-letter)
                                        *v17*)
               (script-ranges (script-greek) *v17*)))
             '(#x1C5 #x1C8 #x1CB #x1F2)))
(test (equal (len (range-list-code-points
                   (general-category-ranges
                    (general-category-titlecase-letter) *v16*)))
             31))
(test (equal (len (range-list-code-points
                   (general-category-ranges
                    (general-category-titlecase-letter) *v17*)))
             31))
(test (equal (len (range-list-code-points
                   (general-category-ranges
                    (general-category-titlecase-letter) *v18*)))
             31))
