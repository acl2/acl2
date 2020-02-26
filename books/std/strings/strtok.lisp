; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "cat")
(include-book "eqv")
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "arithmetic"))
(local (include-book "std/lists/revappend" :dir :system))

(defsection strtok-aux
  :parents (strtok)
  :short "Fast implementation of @(see strtok)."

  (defund strtok-aux (x n xl delimiters curr acc)
    ;; x is the string we're tokenizing, xl is its length
    ;; n is our current position in x
    ;; delimiters are the list of chars to split on
    ;; curr is the current word we're accumulating in reverse order
    ;; acc is the string list of previously found words
    (declare (type string x)
             (type (integer 0 *) n xl)
             (xargs :guard (and (stringp x)
                                (natp xl)
                                (natp n)
                                (<= xl (length x))
                                (<= n xl)
                                (character-listp delimiters)
                                (character-listp curr)
                                (string-listp acc))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        (if curr
            (cons (rchars-to-string curr) acc)
          acc)
      (let* ((char1  (char x n))
             (matchp (member char1 delimiters)))
        (strtok-aux (the string x)
                    (the (integer 0 *) (+ 1 (lnfix n)))
                    (the integer xl)
                    delimiters
                    (if matchp nil (cons char1 curr))
                    (if (and matchp curr)
                        (cons (rchars-to-string curr) acc)
                      acc)))))

  (local (in-theory (enable strtok-aux)))

  (defthm true-listp-of-strtok-aux
    (implies (true-listp acc)
             (true-listp (strtok-aux x n xl delimiters curr acc)))
    :hints(("Goal" :induct (strtok-aux x n xl delimiters curr acc))))

  (defthm string-listp-of-strtok-aux
    (implies (string-listp acc)
             (string-listp (strtok-aux x n xl delimiters curr acc)))
    :hints(("Goal" :induct (strtok-aux x n xl delimiters curr acc))))

  (defcong streqv equal (strtok-aux x n xl delimiters curr acc) 1))



(defsection strtok
  :parents (std/strings)
  :short "Tokenize a string with character delimiters."

  :long "<p>@(call strtok) splits the string @('x') into a list of substrings,
based on @('delimiters'), a list of characters.  This is somewhat similar to
repeatedly calling the @('strtok') function in C.</p>

<p>As an example:</p>

@({
 (strtok \"foo bar, baz!\" (list #\\Space #\\, #\\!))
   -->
 (\"foo\" \"bar\" \"baz\")
})

<p>Note that all of the characters in @('delimiters') are removed, and no empty
strings are ever found in @('strtok')'s output.</p>"

  (definlined strtok (x delimiters)
    (declare (xargs :guard (and (stringp x)
                                (character-listp delimiters))))
    ;; Two tricks.
    ;;  - Use REV for better type-prescription
    ;;  - Use LEN of EXPLODE for better congruence
    (let ((rtokens (strtok-aux x 0 (mbe :logic (len (explode x))
                                        :exec (length x))
                               delimiters nil nil)))
      (mbe :logic (rev rtokens)
           :exec (reverse rtokens))))

  (local (in-theory (enable strtok)))

  (local (defthm lemma
           (implies (string-listp x)
                    (string-listp (acl2::rev x)))))

  (defthm string-listp-of-strtok
    (string-listp (strtok x delimiters)))

  (defcong streqv equal (strtok x delimiters) 1))
