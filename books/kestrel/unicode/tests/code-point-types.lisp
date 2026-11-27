; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the basic types of code points (book code-point-types.lisp).
;
; The first part has examples of each type.
; The second part has, for each supported version,
; the number of code points of each type,
; counted on the ranges that BASIC-TYPE-RANGES gives.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../code-point-types")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test (form)
  `(assert-event ,form))

(defconst *v16* (version-v16.0.0))
(defconst *v17* (version-v17.0.0))
(defconst *v18* (version-v18.0.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Graphic: letters, marks, numbers, punctuation, symbols and spaces.

(test (equal (code-point-basic-type #x0041 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x0301 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x0031 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x002C *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x002B *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x0020 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x3000 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x4E00 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #xAC00 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x1F600 *v16*) (basic-type-graphic)))

; Format: the general categories Cf, Zl and Zp.

(test (equal (code-point-basic-type #x00AD *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #x200B *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #x200D *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #x202E *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #xFEFF *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #x2028 *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #x2029 *v16*) (basic-type-format)))
(test (equal (code-point-basic-type #xE0001 *v16*) (basic-type-format)))

; Control: U+0000 to U+001F and U+007F to U+009F.

(test (equal (code-point-basic-type #x0000 *v16*) (basic-type-control)))
(test (equal (code-point-basic-type #x000A *v16*) (basic-type-control)))
(test (equal (code-point-basic-type #x001F *v16*) (basic-type-control)))
(test (equal (code-point-basic-type #x007E *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x007F *v16*) (basic-type-control)))
(test (equal (code-point-basic-type #x009F *v16*) (basic-type-control)))
(test (equal (code-point-basic-type #x00A0 *v16*) (basic-type-graphic)))

; Private-use.

(test (equal (code-point-basic-type #xE000 *v16*) (basic-type-private-use)))
(test (equal (code-point-basic-type #xF8FF *v16*) (basic-type-private-use)))
(test (equal (code-point-basic-type #xF0000 *v16*) (basic-type-private-use)))
(test (equal (code-point-basic-type #xFFFFD *v16*) (basic-type-private-use)))
(test (equal (code-point-basic-type #x100000 *v16*)
             (basic-type-private-use)))
(test (equal (code-point-basic-type #x10FFFD *v16*)
             (basic-type-private-use)))

; Surrogate.

(test (equal (code-point-basic-type #xD7FF *v16*) (basic-type-reserved)))
(test (equal (code-point-basic-type #xD800 *v16*) (basic-type-surrogate)))
(test (equal (code-point-basic-type #xDBFF *v16*) (basic-type-surrogate)))
(test (equal (code-point-basic-type #xDC00 *v16*) (basic-type-surrogate)))
(test (equal (code-point-basic-type #xDFFF *v16*) (basic-type-surrogate)))

; Noncharacter.

(test (equal (code-point-basic-type #xFDCF *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #xFDD0 *v16*) (basic-type-noncharacter)))
(test (equal (code-point-basic-type #xFDEF *v16*) (basic-type-noncharacter)))
(test (equal (code-point-basic-type #xFDF0 *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #xFFFD *v16*) (basic-type-graphic)))
(test (equal (code-point-basic-type #xFFFE *v16*) (basic-type-noncharacter)))
(test (equal (code-point-basic-type #xFFFF *v16*) (basic-type-noncharacter)))
(test (equal (code-point-basic-type #x1FFFE *v16*)
             (basic-type-noncharacter)))
(test (equal (code-point-basic-type #xFFFFE *v16*)
             (basic-type-noncharacter)))
(test (equal (code-point-basic-type #x10FFFF *v16*)
             (basic-type-noncharacter)))

; Reserved.

(test (equal (code-point-basic-type #x0378 *v16*) (basic-type-reserved)))
(test (equal (code-point-basic-type #x0378 *v18*) (basic-type-reserved)))
(test (equal (code-point-basic-type #x40000 *v18*) (basic-type-reserved)))
(test (equal (code-point-basic-type #xE0000 *v18*) (basic-type-reserved)))

; A reserved code point of a version
; can have a character in a later version.

(test (equal (code-point-basic-type #x088F *v16*) (basic-type-reserved)))
(test (equal (code-point-basic-type #x088F *v17*) (basic-type-graphic)))
(test (equal (code-point-basic-type #x18E00 *v17*) (basic-type-reserved)))
(test (equal (code-point-basic-type #x18E00 *v18*) (basic-type-graphic)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The number of code points of each type.

; Four types have the same code points in every version.

(test (equal (range-list-size (basic-type-ranges (basic-type-control) *v16*))
             65))
(test (equal (range-list-size (basic-type-ranges (basic-type-control) *v17*))
             65))
(test (equal (range-list-size (basic-type-ranges (basic-type-control) *v18*))
             65))

(test (equal (range-list-size
              (basic-type-ranges (basic-type-private-use) *v16*))
             137468))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-private-use) *v17*))
             137468))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-private-use) *v18*))
             137468))

(test (equal (range-list-size
              (basic-type-ranges (basic-type-surrogate) *v16*))
             2048))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-surrogate) *v17*))
             2048))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-surrogate) *v18*))
             2048))

(test (equal (range-list-size
              (basic-type-ranges (basic-type-noncharacter) *v16*))
             66))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-noncharacter) *v17*))
             66))
(test (equal (range-list-size
              (basic-type-ranges (basic-type-noncharacter) *v18*))
             66))

; The format characters are also the same in the supported versions.

(test (equal (range-list-size (basic-type-ranges (basic-type-format) *v16*))
             172))
(test (equal (range-list-size (basic-type-ranges (basic-type-format) *v17*))
             172))
(test (equal (range-list-size (basic-type-ranges (basic-type-format) *v18*))
             172))

; Each version has more graphic characters,
; and as many fewer reserved code points.

(test (equal (range-list-size (basic-type-ranges (basic-type-graphic) *v16*))
             154826))
(test (equal (range-list-size (basic-type-ranges (basic-type-graphic) *v17*))
             159629))
(test (equal (range-list-size (basic-type-ranges (basic-type-graphic) *v18*))
             172636))

(test (equal (range-list-size (basic-type-ranges (basic-type-reserved) *v16*))
             819467))
(test (equal (range-list-size (basic-type-ranges (basic-type-reserved) *v17*))
             814664))
(test (equal (range-list-size (basic-type-ranges (basic-type-reserved) *v18*))
             801657))

; The seven numbers of a version add up to the number of code points.

(test (equal (+ 154826 172 65 137468 2048 66 819467) #x110000))
(test (equal (+ 159629 172 65 137468 2048 66 814664) #x110000))
(test (equal (+ 172636 172 65 137468 2048 66 801657) #x110000))
