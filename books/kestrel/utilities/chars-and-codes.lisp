; A lightweight book about code-char and char-code
;
; Copyright (C) 2023-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These are better than the axioms code-char-char-code-is-identity and
;; char-code-code-char-is-identity.

;; These are better than the rules in
;; books/std/basic/code-char-char-code-with-force.lisp.

;; See also books/kestrel/utilities/strings/char-code-theorems.lisp.

(defthm code-char-of-char-code-simple
  (equal (code-char (char-code x))
         (if (characterp x)
             x
           (code-char 0) ; avoid unreadable character constant
           )))

(defthm char-code-of-code-char-simple
  (equal (char-code (code-char x))
         (if (and (natp x)
                  (< x 256))
             x
           0)))

(defthm equal-of-char-code-and-constant
  (implies (syntaxp (and (quotep k)
                         (not (quotep char)) ; prevents rare loops
                         ))
           (equal (equal (char-code char) k)
                  (and (natp k)
                       (< k 256)
                       (if (characterp char)
                           ;; We expect (code-char k) to be evaluated:
                           (equal char (code-char k))
                         (equal k 0))))))

(defthm equal-of-code-char-and-constant
  (implies (syntaxp (and (quotep k)
                         (not (quotep code)) ; prevents rare loops
                         ))
           (equal (equal (code-char code) k)
                  (and (characterp k)
                       (if (and (natp code)
                                (< code 256))
                           ;; We expect (char-code k) to be evaluated:
                           (equal code (char-code k))
                         ;; We expect (code-char 0) to be evaluated:
                         (equal k (code-char 0)))))))
