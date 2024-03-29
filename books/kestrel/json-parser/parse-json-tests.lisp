; Tests for the JSON parser
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-json")
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;; NOTE: To see the Unicode characters in this file, try M-x
;; revert-buffer-with-coding-system utf-8.  But that may not be necessary
;; unless further tests introduce illegal UTF-8 characters.

;; TODO: Add more tests

;;;
;;; Tests of string parsing (focusing on Unicode support)
;;;

(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"Euro sign: \\u20AC.\"" 'list))
   (and (not erp)
        (equal string "Euro sign: €.")
        (equal chars nil))))

(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"A Hangul symbol: \\ud55c.\"" 'list))
   (and (not erp)
        (equal string "A Hangul symbol: 한.")
        (equal chars nil))))

;; Test involving a unicode escape for the slash character (mentioned in ECMA 404).
;; Also includes extra characters after the string
(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"test: \\u002f.\"EXTRACHARS" 'list))
   (and (not erp)
        (equal string "test: /.")
        (equal chars '(#\E #\X #\T #\R #\A #\C #\H #\A #\R #\S)))))

;; Variant of the above with upper case hex digit
(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"test: \\u002F.\"EXTRACHARS" 'list))
   (and (not erp)
        (equal string "test: /.")
        (equal chars '(#\E #\X #\T #\R #\A #\C #\H #\A #\R #\S)))))

;; Test involving a unicode escape that includes 2 surrogate code points: the G
;; clef character (from ECMA 404)
(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"\\uD834\\uDD1E\"" 'list))
   (and (not erp)
        ;; two equivalent tests:
        (and (equal string (coerce (code-point-to-utf-8-chars #x1D11E) 'string))
             (equal string "𝄞"))
        (null chars))))

; Same as above but with lower case hex digits
(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"\\ud834\\udd1e\"" 'list))
   (and (not erp)
        ;; two equivalent tests:
        (and (equal string (coerce (code-point-to-utf-8-chars #x1D11E) 'string))
             (equal string "𝄞"))
        (null chars))))

;; A test involving a symbol from the Desert alphabet.  Also includes some
;; extra characters after the string.
(assert!
 (mv-let (erp string chars)
   (parse-json-string (coerce "\"\\uD801\\uDC37\"12extraCHARS" 'list))
   (and (not erp)
        (equal string "𐐷")
        (equal chars '(#\1 #\2 #\e #\x #\t #\r #\a #\C #\H #\A #\R #\S)))))

;; A test involving characters not legal in UTF-8
(assert!
 (mv-let (erp string chars)
   (parse-json-string (list #\"
                            (code-char 255) ; not legal in UTF-8
                            (code-char 254) ; not legal in UTF-8
                            #\"))
   (and (not erp)
        ;; weird chars passed through (note; we avoid actually putting the
        ;; literal weird chars here, so that this whole file remains legal UTF-8):
        (equal string (coerce (list (code-char 255) ; not legal in UTF-8
                                    (code-char 254) ; not legal in UTF-8
                                    )
                              'string))
        (equal chars nil))))

;;;
;;; Tests of parsing larger objects
;;;

;; Parse a whole JSON object
(assert!
 (mv-let (erp res)
   (parse-string-as-json "{\"FirstName\" : \"John\", \"LastName\" : \"Smith\"}")
   (and (null erp)
        (equal res '(:OBJECT (("FirstName" . "John")
                              ("LastName" . "Smith")))))))

;; A version with Unicode escapes
(assert!
 (mv-let (erp res)
   (parse-string-as-json "{\"First\\u20ACName\" : \"Jo\\u20AC\hn\", \"LastName\" : \"Smith\"}")
   (and (null erp)
        (equal res '(:OBJECT (("First€Name" . "Jo€hn")
                              ("LastName" . "Smith")))))))

;; A test with various kinds of values
(assert!
 (mv-let (erp res)
   (parse-string-as-json "{\"name\" : \"Jo\\u20AC\hn\",
                         \"age\" : 20,
                         \"height\" : 123.456E7,
                         \"width\" : 123.456E1,
                         \"weight\" : 123.456E-7,
                         \"weight2\" : 1.23456E-5,
                         \"val\" : 0.00023456,
                         \"happy\" : true,
                         \"sad\" : false,
                         \"pets\" : null,
                         \"friends\" : [\"Shelly\",
                                        {\"name\" : \"Michael\", \"nickname\" : \"Mike\"},
                                        \"Darnell\",
                                        100,
                                        true,
                                        false,
                                        null]}")
   (and (null erp)
        (equal res '(:OBJECT (("name" . "Jo€hn")
                              ("age" . 20)
                              ("height" . 1234560000)
                              ("width" . 30864/25)
                              ("weight" . 1929/156250000)
                              ("weight2" . 1929/156250000)
                              ("val" . 733/3125000) ; same as 23456/100000000
                              ("happy" . :TRUE)
                              ("sad" . :FALSE)
                              ("pets" . :NULL)
                              ("friends" . (:ARRAY ("Shelly"
                                                    (:OBJECT (("name" . "Michael")
                                                              ("nickname" . "Mike")))
                                                    "Darnell" 100 :TRUE
                                                    :FALSE :NULL)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns :error or the parsed JSON object
(defun parse-string-as-json2 (str)
  (declare (xargs :guard (stringp str)))
  (mv-let (erp res)
    (parse-json (coerce str 'list))
    (if erp
        :error
      res)))

(assert-equal (parse-string-as-json2 "0") 0)
(assert-equal (parse-string-as-json2 "123") 123)
(assert-equal (parse-string-as-json2 "-123") -123)
(assert-equal (parse-string-as-json2 "10.5") 21/2)
(assert-equal (parse-string-as-json2 "-10.5") -21/2)
(assert-equal (parse-string-as-json2 "0.5") 1/2)
(assert-equal (parse-string-as-json2 "-0.5") -1/2)
(assert-equal (parse-string-as-json2 "1e2") 100)
(assert-equal (parse-string-as-json2 "1.5e2") 150)
(assert-equal (parse-string-as-json2 "-1e2") -100)
(assert-equal (parse-string-as-json2 "-1.5e2") -150)
(assert-equal (parse-string-as-json2 "4e-2") 4/100)
(assert-equal (parse-string-as-json2 "4.5e-2") (/ 9/2 100))
(assert-equal (parse-string-as-json2 "-4e-2") -4/100)
(assert-equal (parse-string-as-json2 "-4.5e-2") (- (/ 9/2 100)))

(assert-equal (parse-string-as-json2 "[1, 2, 3]") '(:array (1 2 3)))
(assert-equal (parse-string-as-json2 "{\"a\" : 1, \"b\" : 2}") '(:OBJECT (("a" . 1) ("b" . 2))))
