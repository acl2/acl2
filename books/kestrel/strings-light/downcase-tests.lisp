; Tests of downcase utilities
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "downcase")

;;;
;;; Tests of char-downcase-gen
;;;

;; upper-case letter
(assert-event (equal (char-downcase-gen #\A) #\a))

;; another upper-case letter
(assert-event (equal (char-downcase-gen #\Z) #\z))

;; lower-case letter is unchanged
(assert-event (equal (char-downcase-gen #\a) #\a))

;; digit is unchanged
(assert-event (equal (char-downcase-gen #\5) #\5))

;; punctuation is unchanged
(assert-event (equal (char-downcase-gen #\!) #\!))

;; space is unchanged
(assert-event (equal (char-downcase-gen #\Space) #\Space))

;;;
;;; Tests of chars-downcase-gen
;;;

;; simple test with all upper-case letters
(assert-event
 (equal (chars-downcase-gen '(#\A #\B #\C) nil)
        '(#\a #\b #\c)))

;; mixed case
(assert-event
 (equal (chars-downcase-gen '(#\H #\e #\L #\l #\O) nil)
        '(#\h #\e #\l #\l #\o)))

;; digits and punctuation are unchanged
(assert-event
 (equal (chars-downcase-gen '(#\A #\1 #\B #\!) nil)
        '(#\a #\1 #\b #\!)))

;; all lower-case letters are unchanged
(assert-event
 (equal (chars-downcase-gen '(#\a #\b #\c) nil)
        '(#\a #\b #\c)))

;; empty list
(assert-event
 (equal (chars-downcase-gen nil nil)
        nil))

;;;
;;; Tests of string-downcase-gen
;;;

;; simple test with all upper-case letters
(assert-event (equal (string-downcase-gen "ABC") "abc"))

;; mixed case
(assert-event (equal (string-downcase-gen "HeLlO") "hello"))

;; digits and punctuation are unchanged
(assert-event (equal (string-downcase-gen "A1B!") "a1b!"))

;; all lower-case letters are unchanged
(assert-event (equal (string-downcase-gen "abc") "abc"))

;; empty string
(assert-event (equal (string-downcase-gen "") ""))

;; string with spaces
(assert-event (equal (string-downcase-gen "Hello World") "hello world"))
