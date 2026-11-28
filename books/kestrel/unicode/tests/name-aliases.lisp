; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the aliases of the names of the characters
; (book name-aliases.lisp).
;
; The first part has examples of the aliases of code points,
; and of the functions from an alias, or from a name or an alias,
; to its code point, exactly and by the loose matching of names.
; The second part counts the aliases of each type, for each supported version.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../name-aliases")

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

; The aliases of a code point, in the order of the file NameAliases.txt.

; A control code, which has no name.

(test (equal (code-point-name #x000A *v16*) ""))
(test (equal (code-point-name-aliases #x000A *v16*)
             (list (name-alias "LINE FEED" (name-alias-type-control))
                   (name-alias "NEW LINE" (name-alias-type-control))
                   (name-alias "END OF LINE" (name-alias-type-control))
                   (name-alias "LF" (name-alias-type-abbreviation))
                   (name-alias "NL" (name-alias-type-abbreviation))
                   (name-alias "EOL" (name-alias-type-abbreviation)))))
(test (equal (code-point-name-aliases #x0007 *v16*)
             (list (name-alias "ALERT" (name-alias-type-control))
                   (name-alias "BEL" (name-alias-type-abbreviation)))))

; A control code with an alias that was never in a standard.

(test (equal (code-point-name-aliases #x0080 *v16*)
             (list (name-alias "PADDING CHARACTER" (name-alias-type-figment))
                   (name-alias "PAD" (name-alias-type-abbreviation)))))

; A format character, which has a name.

(test (equal (code-point-name #xFEFF *v16*) "ZERO WIDTH NO-BREAK SPACE"))
(test (equal (code-point-name-aliases #xFEFF *v16*)
             (list (name-alias "BYTE ORDER MARK" (name-alias-type-alternate))
                   (name-alias "BOM" (name-alias-type-abbreviation))
                   (name-alias "ZWNBSP" (name-alias-type-abbreviation)))))
(test (equal (code-point-name-aliases #x200B *v16*)
             (list (name-alias "ZWSP" (name-alias-type-abbreviation)))))

; Variation selectors.

(test (equal (code-point-name-aliases #xFE00 *v16*)
             (list (name-alias "VS1" (name-alias-type-abbreviation)))))
(test (equal (code-point-name-aliases #xE01EF *v16*)
             (list (name-alias "VS256" (name-alias-type-abbreviation)))))

; Corrections of names.

(test (equal (code-point-name #xFE18 *v16*)
             (concatenate 'string
                          "PRESENTATION FORM FOR VERTICAL "
                          "RIGHT WHITE LENTICULAR BRAKCET")))
(test (equal (code-point-name-aliases #xFE18 *v16*)
             (list (name-alias
                    (concatenate 'string
                                 "PRESENTATION FORM FOR VERTICAL "
                                 "RIGHT WHITE LENTICULAR BRACKET")
                    (name-alias-type-correction)))))
(test (equal (code-point-name #x0FD0 *v16*)
             "TIBETAN MARK BSKA- SHOG GI MGO RGYAN"))
(test (equal (code-point-name-aliases #x0FD0 *v16*)
             (list (name-alias "TIBETAN MARK BKA- SHOG GI MGO RGYAN"
                               (name-alias-type-correction)))))

; Most code points have no alias.

(test (equal (code-point-name-aliases #x0061 *v16*) nil))
(test (equal (code-point-name-aliases #x4E00 *v16*) nil))
(test (equal (code-point-name-aliases #x0378 *v16*) nil))
(test (equal (code-point-name-aliases #xE000 *v16*) nil))

; Unicode 17.0.0 adds four corrections.

(test (equal (code-point-name #x16881 *v17*)
             "BAMUM LETTER PHASE-B PUNGAAM"))
(test (equal (code-point-name-aliases #x16881 *v16*) nil))
(test (equal (code-point-name-aliases #x16881 *v17*)
             (list (name-alias "BAMUM LETTER PHASE-B PUNGGAAM"
                               (name-alias-type-correction)))))
(test (equal (code-point-name-aliases #x16881 *v18*)
             (code-point-name-aliases #x16881 *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From an alias to its code point.

; The exact alias.

(test (equal (name-alias-code-point "LINE FEED" *v16*) #x000A))
(test (equal (name-alias-code-point "NEW LINE" *v16*) #x000A))
(test (equal (name-alias-code-point "LF" *v16*) #x000A))
(test (equal (name-alias-code-point "EOL" *v16*) #x000A))
(test (equal (name-alias-code-point "NULL" *v16*) #x0000))
(test (equal (name-alias-code-point "BEL" *v16*) #x0007))
(test (equal (name-alias-code-point "PADDING CHARACTER" *v16*) #x0080))
(test (equal (name-alias-code-point "SINGLE-SHIFT-2" *v16*) #x008E))
(test (equal (name-alias-code-point "BYTE ORDER MARK" *v16*) #xFEFF))
(test (equal (name-alias-code-point "BOM" *v16*) #xFEFF))
(test (equal (name-alias-code-point "ZWSP" *v16*) #x200B))
(test (equal (name-alias-code-point "VS256" *v16*) #xE01EF))
(test (equal (name-alias-code-point "TIBETAN MARK BKA- SHOG GI MGO RGYAN"
                                    *v16*)
             #x0FD0))

; Strings that are not aliases.

(test (not (name-alias-code-point "" *v16*)))
(test (not (name-alias-code-point "NO SUCH ALIAS" *v16*)))
(test (not (name-alias-code-point "lf" *v16*)))
(test (not (name-alias-code-point "LINE  FEED" *v16*)))
(test (not (name-alias-code-point "LINEFEED" *v16*)))
(test (not (name-alias-code-point "SINGLE SHIFT 2" *v16*)))

; A name is not an alias, and an alias is not a name.

(test (not (name-alias-code-point "LATIN SMALL LETTER A" *v16*)))
(test (not (name-alias-code-point "ZERO WIDTH NO-BREAK SPACE" *v16*)))
(test (not (name-code-point "LINE FEED" *v16*)))
(test (not (name-code-point "BYTE ORDER MARK" *v16*)))
(test (not (loose-name-code-point "byte order mark" *v16*)))

; An alias of a later version is not an alias in an earlier one.

(test (not (name-alias-code-point "BAMUM LETTER PHASE-B PUNGGAAM" *v16*)))
(test (equal (name-alias-code-point "BAMUM LETTER PHASE-B PUNGGAAM" *v17*)
             #x16881))
(test (equal (name-alias-code-point "BAMUM LETTER PHASE-B PUNGGAAM" *v18*)
             #x16881))

; Loose matching.

(test (equal (loose-name-alias-code-point "line feed" *v16*) #x000A))
(test (equal (loose-name-alias-code-point "Line_Feed" *v16*) #x000A))
(test (equal (loose-name-alias-code-point "LINEFEED" *v16*) #x000A))
(test (equal (loose-name-alias-code-point "lf" *v16*) #x000A))
(test (equal (loose-name-alias-code-point "bom" *v16*) #xFEFF))
(test (equal (loose-name-alias-code-point "single shift 2" *v16*) #x008E))
(test (equal (loose-name-alias-code-point "SingleShift2" *v16*) #x008E))
(test (not (loose-name-alias-code-point "" *v16*)))
(test (not (loose-name-alias-code-point "no such alias" *v16*)))
(test (not (loose-name-alias-code-point "latin small letter a" *v16*)))

; A hyphen with a space after it is not medial: it is kept
; [UAX #44, Section 5.9.2].

(test (equal (loose-name-alias-code-point
              "tibetan mark bka- shog gi mgo rgyan" *v16*)
             #x0FD0))
(test (not (loose-name-alias-code-point
            "tibetan mark bka shog gi mgo rgyan" *v16*)))

; The aliases PRIVATE USE-1 and PRIVATE USE-2 of two control codes.

(test (equal (name-alias-code-point "PRIVATE USE-1" *v16*) #x0091))
(test (equal (loose-name-alias-code-point "private-use-1" *v16*) #x0091))
(test (equal (loose-name-alias-code-point "private use 2" *v16*) #x0092))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The type of the alias that a string is.

(test (equal (find-name-alias "BOM" (code-point-name-aliases #xFEFF *v16*))
             (name-alias "BOM" (name-alias-type-abbreviation))))
(test (equal (find-name-alias "BYTE ORDER MARK"
                              (code-point-name-aliases #xFEFF *v16*))
             (name-alias "BYTE ORDER MARK" (name-alias-type-alternate))))
(test (not (find-name-alias "bom" (code-point-name-aliases #xFEFF *v16*))))
(test (not (find-name-alias "LF" (code-point-name-aliases #xFEFF *v16*))))
(test (equal (find-name-alias-by-key
              "byteordermark"
              (code-point-name-aliases #xFEFF *v16*))
             (name-alias "BYTE ORDER MARK" (name-alias-type-alternate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From a name or an alias to its code point.

; U+0007 was commonly called BELL before U+1F514 got that name
; [UAX #44, Section 5.9.2]; its aliases are ALERT and BEL.

(test (equal (name-or-alias-code-point "BELL" *v16*) #x1F514))
(test (equal (name-or-alias-code-point "BEL" *v16*) #x0007))
(test (equal (name-or-alias-code-point "ALERT" *v16*) #x0007))

(test (equal (name-or-alias-code-point "LATIN SMALL LETTER A" *v16*)
             #x0061))
(test (equal (name-or-alias-code-point "LINE FEED" *v16*) #x000A))
(test (equal (name-or-alias-code-point "ZERO WIDTH NO-BREAK SPACE" *v16*)
             #xFEFF))
(test (equal (name-or-alias-code-point "BYTE ORDER MARK" *v16*) #xFEFF))
(test (equal (name-or-alias-code-point "HANGUL SYLLABLE GA" *v16*) #xAC00))
(test (equal (name-or-alias-code-point "CJK UNIFIED IDEOGRAPH-4E00" *v16*)
             #x4E00))
(test (not (name-or-alias-code-point "" *v16*)))
(test (not (name-or-alias-code-point "NO SUCH NAME" *v16*)))
(test (not (name-or-alias-code-point "line feed" *v16*)))
(test (not (name-or-alias-code-point "latin small letter a" *v16*)))

(test (equal (loose-name-or-alias-code-point "latin small letter a" *v16*)
             #x0061))
(test (equal (loose-name-or-alias-code-point "line feed" *v16*) #x000A))
(test (equal (loose-name-or-alias-code-point "byte-order mark" *v16*)
             #xFEFF))
(test (equal (loose-name-or-alias-code-point "zero width no break space"
                                             *v16*)
             #xFEFF))
(test (equal (loose-name-or-alias-code-point "bell" *v16*) #x1F514))
(test (equal (loose-name-or-alias-code-point "bel" *v16*) #x0007))
(test (not (loose-name-or-alias-code-point "" *v16*)))
(test (not (loose-name-or-alias-code-point "no such name" *v16*)))

; The name of U+11EC and its correction,
; which UAX #44 gives as an example of a medial hyphen in an alias.

(test (equal (name-or-alias-code-point "HANGUL JONGSEONG IEUNG-KIYEOK" *v16*)
             #x11EC))
(test (equal (name-or-alias-code-point "HANGUL JONGSEONG YESIEUNG-KIYEOK"
                                       *v16*)
             #x11EC))
(test (equal (loose-name-or-alias-code-point
              "hangul jongseong yesieung kiyeok" *v16*)
             #x11EC))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The number of aliases of each type.

; COUNT plus the number of aliases of a list that have a type.

(define name-aliases-count-type ((aliases name-alias-listp)
                                 (type name-alias-type-p)
                                 (count natp))
  :returns (new-count natp :hints (("Goal" :induct t)))
  (cond ((endp aliases) (nfix count))
        ((equal (name-alias->type (car aliases))
                (name-alias-type-fix type))
         (name-aliases-count-type (cdr aliases) type (+ 1 (nfix count))))
        (t (name-aliases-count-type (cdr aliases) type count)))
  :hooks nil)

; COUNT plus the number of aliases, of the code points of a list,
; that have a type.

(define name-alias-count ((cps code-point-listp)
                          (type name-alias-type-p)
                          (ver versionp)
                          (count natp))
  :returns (new-count natp :hints (("Goal" :induct t)))
  (if (endp cps)
      (nfix count)
    (name-alias-count (cdr cps)
                      type
                      ver
                      (name-aliases-count-type
                       (code-point-name-aliases (car cps) ver)
                       type
                       count)))
  :hooks nil)

(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-correction) *v16* 0)
             35))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-control) *v16* 0)
             84))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-alternate) *v16* 0)
             1))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-figment) *v16* 0)
             3))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-abbreviation) *v16* 0)
             354))

(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-correction) *v17* 0)
             39))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-control) *v17* 0)
             84))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-alternate) *v17* 0)
             1))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-figment) *v17* 0)
             3))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-abbreviation) *v17* 0)
             354))

(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-correction) *v18* 0)
             39))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-control) *v18* 0)
             84))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-alternate) *v18* 0)
             1))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-figment) *v18* 0)
             3))
(test (equal (name-alias-count (all-code-points)
                               (name-alias-type-abbreviation) *v18* 0)
             354))

; The types add up to the number of aliases,
; which is the number of keys in the table of the keys of the aliases:
; no two aliases have the same key.

(test (equal (+ 35 84 1 3 354) 477))
(test (equal (+ 39 84 1 3 354) 481))
(test (equal (tmap::size (name-alias-keys *v16*)) 477))
(test (equal (tmap::size (name-alias-keys *v17*)) 481))
(test (equal (tmap::size (name-alias-keys *v18*)) 481))
