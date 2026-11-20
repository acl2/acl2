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
