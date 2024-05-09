; A lightweight book about code-char and char-code
;
; Copyright (C) 2023 Kestrel Institute
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
