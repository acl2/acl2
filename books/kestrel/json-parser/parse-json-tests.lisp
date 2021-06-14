; Tests for the JSON parser
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-json")
(include-book "std/testing/assert-bang" :dir :system)

;; These tests focus on Unicode support

;; TODO: Add more tests

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


;; Parse a whole JSON object
(assert!
 (mv-let (erp res)
   (parse-json (coerce "{\"FirstName\" : \"John\", \"LastName\" : \"Smith\"}" 'list))
   (and (null erp)
        (equal res '(:OBJECT (("FirstName" . "John")
                              ("LastName" . "Smith")))))))

;; A version with Unicode escapes
(assert!
 (mv-let (erp res)
   (parse-json (coerce "{\"First\\u20ACName\" : \"Jo\\u20AC\hn\", \"LastName\" : \"Smith\"}" 'list))
   (and (null erp)
        (equal res '(:OBJECT (("First€Name" . "Jo€hn")
                              ("LastName" . "Smith")))))))

;; A test with various kinds of values
(assert!
 (mv-let (erp res)
   (parse-json (coerce "{\"name\" : \"Jo\\u20AC\hn\",
                         \"age\" : 20,
                         \"happy\" : true,
                         \"sad\" : false,
                         \"pets\" : null,
                         \"friends\" : [\"Shelly\",
                                        {\"name\" : \"Michael\", \"nickname\" : \"Mike\"},
                                        \"Darnell\",
                                        100,
                                        true,
                                        false,
                                        null]}"
                       'list))
   (and (null erp)
        (equal res '(:OBJECT (("name" . "Jo€hn")
                              ("age" . 20)
                              ("happy" . :TRUE)
                              ("sad" . :FALSE)
                              ("pets" . :NULL)
                              ("friends" . (:ARRAY ("Shelly"
                                                    (:OBJECT (("name" . "Michael")
                                                              ("nickname" . "Mike")))
                                                    "Darnell" 100 :TRUE
                                                    :FALSE :NULL)))))))))
