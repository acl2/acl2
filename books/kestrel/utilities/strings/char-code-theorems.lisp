; String Utilities -- Theorems about CHAR-CODE and CODE-CHAR
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/unsigned-byte-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection code-char-inverses-theorems
  :parents (string-utilities code-char char-code)
  :short "@(tsee code-char) and @(tsee char-code)
          are mutual inverses."

  (defrule char-code-of-code-char
    (equal (char-code (code-char code))
           (unsigned-byte-fix 8 code)))

  (defrule code-char-of-char-code
    (equal (code-char (char-code char))
           (char-fix char))
    ;; workaround to the forced hyp of axiom CODE-CHAR-CHAR-CODE-IS-IDENTITY:
    :use (:instance code-char-char-code-is-identity (c (char-fix char)))
    :disable code-char-char-code-is-identity))

(defsection code-char-injectivity-theorem
  :parents (string-utilities code-char)
  :short "@(tsee code-char) is injective on natural numbers below 256."
  :long
  (xdoc::topstring-p
   "Note that the injectivity of @(tsee char-code) over characters
    is expressed by the theorem
    <see topic='@(url str::char-code-lemmas)'>@('equal-of-char-code')</see>.")

  (defrule equal-of-code-chars
    (equal (equal (code-char x)
                  (code-char y))
           (equal (unsigned-byte-fix 8 x)
                  (unsigned-byte-fix 8 y)))))
