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

; ZWNJ and ZWJ have XID_Continue
; (it is UTS #39, not UAX #31, that restricts them).

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
(test (equal (bidi-formatting-class #x202E *v16*)
             (bidi-formatting-class-rlo)))
(test (bidi-explicit-formatting-p #x2066 *v16*)) ; LEFT-TO-RIGHT ISOLATE
(test (equal (bidi-formatting-class #x2069 *v17*)
             (bidi-formatting-class-pdi)))
(test (bidi-control-p #x200F *v16*)) ; RIGHT-TO-LEFT MARK is a control ...
(test (not (bidi-explicit-formatting-p #x200F *v16*))) ; ... but not explicit
(test (not (bidi-control-p (char-code #\a) *v16*)))
(test (not (bidi-formatting-class (char-code #\a) *v16*)))

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
