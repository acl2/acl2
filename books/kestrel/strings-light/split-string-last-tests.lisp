; Tests of split-string-last
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-string-last")

;; simple test
(assert-event
 (mv-let (foundp before after)
   (split-string-last "ABCDE" #\D)
   (and foundp
        (equal before "ABC")
        (equal after "E"))))

;; test where the given character does not appear in the string
(assert-event
 (mv-let (foundp before after)
   (split-string-last "ABCDE" #\Z)
   (and (not foundp)
        (equal before "ABCDE")
        (equal after ""))))

;; test where the given character appears multiple times
(assert-event
 (mv-let (foundp before after)
   (split-string-last "ABCDEDEFGH" #\D)
   (and foundp
        (equal before "ABCDE")
        (equal after "EFGH"))))

;; test where the given character appears at the beginning
(assert-event
 (mv-let (foundp before after)
   (split-string-last "DEFGH" #\D)
   (and foundp
        (equal before "")
        (equal after "EFGH"))))

;; test where the given character appears at the end
(assert-event
 (mv-let (foundp before after)
   (split-string-last "ABCD" #\D)
   (and foundp
        (equal before "ABC")
        (equal after ""))))

;; test where the given character is the entire string
(assert-event
 (mv-let (foundp before after)
   (split-string-last "D" #\D)
   (and foundp
        (equal before "")
        (equal after ""))))

;; test with the empty string
(assert-event
 (mv-let (foundp before after)
   (split-string-last "" #\D)
   (and (not foundp)
        (equal before "")
        (equal after ""))))
