; Tests of split-string
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-string")

;; simple test
(assert-event
 (mv-let (foundp before after)
   (split-string "ABCDE" #\D)
   (and foundp
        (equal before "ABC")
        (equal after "E"))))

;; test where the given character does not appear in the string
(assert-event
 (mv-let (foundp before after)
   (split-string "ABCDE" #\Z)
   (and (not foundp)
        (equal before "ABCDE")
        (equal after ""))))

;; test where the given character appears multiple times
;; note that we use the *last* occurrence.
(assert-event
 (mv-let (foundp before after)
   (split-string "ABCDEDEFGH" #\D)
   (and foundp
        (equal before "ABC")
        (equal after "EDEFGH"))))

;; test where the given character appears at the beginning
(assert-event
 (mv-let (foundp before after)
   (split-string "DEFGH" #\D)
   (and foundp
        (equal before "")
        (equal after "EFGH"))))

;; test where the given character appears at the end
(assert-event
 (mv-let (foundp before after)
   (split-string "ABCD" #\D)
   (and foundp
        (equal before "ABC")
        (equal after ""))))

;; test where the given character is the entire string
(assert-event
 (mv-let (foundp before after)
   (split-string "D" #\D)
   (and foundp
        (equal before "")
        (equal after ""))))

;; test with the empty string
(assert-event
 (mv-let (foundp before after)
   (split-string "" #\D)
   (and (not foundp)
        (equal before "")
        (equal after ""))))
