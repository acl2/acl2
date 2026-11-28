; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the labels of the code points without a name
; (book code-point-labels.lisp).
;
; Examples of the labels of the five types of code points that have them,
; of the function that gives a name or a label for every code point,
; and of the functions from a label to its code point,
; exactly and by the loose matching of names.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../code-point-labels")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test (form)
  `(assert-event ,form))

(defconst *v16* (version-v16.0.0))
(defconst *v17* (version-v17.0.0))
(defconst *v18* (version-v18.0.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The labels of the five types [Unicode, Section 4.8.2, Table 4-9].
; The code point is written with four to six digits:
; the example of the Unicode Standard is control-0008.

(test (equal (code-point-label #x0008 *v16*) "control-0008"))
(test (equal (code-point-label #x0000 *v16*) "control-0000"))
(test (equal (code-point-label #x009F *v16*) "control-009F"))
(test (equal (code-point-label #xE000 *v16*) "private-use-E000"))
(test (equal (code-point-label #xF0000 *v16*) "private-use-F0000"))
(test (equal (code-point-label #x10FFFD *v16*) "private-use-10FFFD"))
(test (equal (code-point-label #xD800 *v16*) "surrogate-D800"))
(test (equal (code-point-label #xDFFF *v16*) "surrogate-DFFF"))
(test (equal (code-point-label #xFDD0 *v16*) "noncharacter-FDD0"))
(test (equal (code-point-label #xFFFF *v16*) "noncharacter-FFFF"))
(test (equal (code-point-label #x10FFFF *v16*) "noncharacter-10FFFF"))
(test (equal (code-point-label #x0378 *v16*) "reserved-0378"))
(test (equal (code-point-label #x40000 *v18*) "reserved-40000"))

; The graphic and format code points have names and no labels.

(test (equal (code-point-label #x0041 *v16*) ""))
(test (equal (code-point-label #x4E00 *v16*) ""))
(test (equal (code-point-label #xAC00 *v16*) ""))
(test (equal (code-point-label #x200B *v16*) ""))
(test (equal (code-point-label #xFEFF *v16*) ""))

; A reserved code point of a version
; has a name and no label in the version that assigns a character to it.

(test (equal (code-point-label #x088F *v16*) "reserved-088F"))
(test (equal (code-point-label #x088F *v17*) ""))
(test (equal (code-point-label #x18E00 *v17*) "reserved-18E00"))
(test (equal (code-point-label #x18E00 *v18*) ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A name or a label for every code point [Unicode, Section 4.8.3].

(test (equal (code-point-name-or-label #x0041 *v16*)
             "LATIN CAPITAL LETTER A"))
(test (equal (code-point-name-or-label #x200B *v16*) "ZERO WIDTH SPACE"))
(test (equal (code-point-name-or-label #x4E00 *v16*)
             "CJK UNIFIED IDEOGRAPH-4E00"))
(test (equal (code-point-name-or-label #x0009 *v16*) "control-0009"))
(test (equal (code-point-name-or-label #xE000 *v16*) "private-use-E000"))
(test (equal (code-point-name-or-label #xD800 *v16*) "surrogate-D800"))
(test (equal (code-point-name-or-label #xFFFF *v16*) "noncharacter-FFFF"))
(test (equal (code-point-name-or-label #x0378 *v16*) "reserved-0378"))
(test (equal (code-point-name-or-label #x088F *v16*) "reserved-088F"))
(test (equal (code-point-name-or-label #x088F *v17*)
             "ARABIC LETTER NOON WITH RING ABOVE"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From a label to its code point.

; The exact label.

(test (equal (label-code-point "control-0008" *v16*) #x0008))
(test (equal (label-code-point "control-0000" *v16*) #x0000))
(test (equal (label-code-point "private-use-E000" *v16*) #xE000))
(test (equal (label-code-point "private-use-10FFFD" *v16*) #x10FFFD))
(test (equal (label-code-point "surrogate-D800" *v16*) #xD800))
(test (equal (label-code-point "noncharacter-FFFF" *v16*) #xFFFF))
(test (equal (label-code-point "noncharacter-10FFFF" *v16*) #x10FFFF))
(test (equal (label-code-point "reserved-0378" *v16*) #x0378))

; Strings that are not labels.
; The number of digits is the one of the label,
; and the type is the one of the code point.

(test (not (label-code-point "" *v16*)))
(test (not (label-code-point "control" *v16*)))
(test (not (label-code-point "control-" *v16*)))
(test (not (label-code-point "control-8" *v16*)))
(test (not (label-code-point "control-00008" *v16*)))
(test (not (label-code-point "control-000008" *v16*)))
(test (not (label-code-point "<control-0008>" *v16*)))
(test (not (label-code-point "CONTROL-0008" *v16*)))
(test (not (label-code-point "control 0008" *v16*)))
(test (not (label-code-point "control-000G" *v16*)))
(test (not (label-code-point "control-0041" *v16*)))
(test (not (label-code-point "reserved-0041" *v16*)))
(test (not (label-code-point "reserved-0008" *v16*)))
(test (not (label-code-point "private-use-e000" *v16*)))
(test (not (label-code-point "private-use-D800" *v16*)))
(test (not (label-code-point "noncharacter-110000" *v16*)))
(test (not (label-code-point "reserved-110000" *v16*)))
(test (not (label-code-point "unassigned-0378" *v16*)))

; A label of a version is not a label in the version
; that assigns a character to the code point.

(test (equal (label-code-point "reserved-088F" *v16*) #x088F))
(test (not (label-code-point "reserved-088F" *v17*)))

; Loose matching.

(test (equal (loose-label-code-point "CONTROL-0008" *v16*) #x0008))
(test (equal (loose-label-code-point "control 0008" *v16*) #x0008))
(test (equal (loose-label-code-point "Control_0008" *v16*) #x0008))
(test (equal (loose-label-code-point "control0008" *v16*) #x0008))
(test (equal (loose-label-code-point "private-use-e000" *v16*) #xE000))
(test (equal (loose-label-code-point "Private Use E000" *v16*) #xE000))
(test (equal (loose-label-code-point "NONCHARACTER-ffff" *v16*) #xFFFF))
(test (not (loose-label-code-point "control-8" *v16*)))
(test (not (loose-label-code-point "control-00008" *v16*)))
(test (not (loose-label-code-point "<control-0008>" *v16*)))
(test (not (loose-label-code-point "" *v16*)))

; The key of a label, and the number at its end.

(test (equal (name-loose-key "control-0008") "control0008"))
(test (equal (name-loose-key "private-use-E000") "privateusee000"))
(test (equal (label-key-value "control0008") 8))
(test (equal (label-key-value "privateusee000") #xE000))
(test (equal (label-key-code-point "control0008" *v16*) #x0008))
(test (equal (label-key-code-point "privateusee000" *v16*) #xE000))
(test (not (label-key-value "control")))
(test (not (label-key-value "control000g")))
(test (not (label-key-value "latinsmalllettera")))

; The keys of the aliases PRIVATE USE-1 and PRIVATE USE-2
; of the control codes U+0091 and U+0092
; have the form of the key of a label; they are not keys of labels.

(test (equal (name-loose-key "PRIVATE USE-1") "privateuse1"))
(test (equal (label-key-value "privateuse1") 1))
(test (not (label-key-code-point "privateuse1" *v16*)))
(test (not (loose-label-code-point "PRIVATE USE-1" *v16*)))
(test (equal (loose-name-alias-code-point "PRIVATE USE-1" *v16*) #x0091))
(test (equal (code-point-label #x0091 *v16*) "control-0091"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A label is not a name or an alias, and a name or an alias is not a label.

(test (not (loose-name-or-alias-code-point "control-0008" *v16*)))
(test (not (loose-name-or-alias-code-point "reserved-0378" *v16*)))
(test (not (loose-name-or-alias-code-point "private-use-E000" *v16*)))
(test (not (loose-label-code-point "LATIN SMALL LETTER A" *v16*)))
(test (not (loose-label-code-point "BACKSPACE" *v16*)))
(test (equal (name-alias-code-point "BACKSPACE" *v16*) #x0008))
