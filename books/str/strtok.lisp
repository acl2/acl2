; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "xdoc/top" :dir :system)
(include-book "misc/definline" :dir :system)
(local (include-book "misc/assert" :dir :system))
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
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp xl)
                                (natp n)
                                (= xl (length x))
                                (<= n xl)
                                (character-listp delimiters)
                                (character-listp curr)
                                (string-listp acc))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        (if curr
            (cons (reverse (coerce curr 'string)) acc)
          acc)
      (let* ((char1  (char x n))
             (matchp (member char1 delimiters)))
        (strtok-aux (the string x)
                    (+ 1 (lnfix n))
                    (the integer xl)
                    delimiters
                    (if matchp nil (cons char1 curr))
                    (if (and matchp curr)
                        (cons (reverse (coerce curr 'string)) acc)
                      acc)))))

  (local (in-theory (enable strtok-aux)))

  (defthm true-listp-of-strtok-aux
    (implies (true-listp acc)
             (true-listp (strtok-aux x n xl delimiters curr acc)))
    :hints(("Goal" :induct (strtok-aux x n xl delimiters curr acc))))

  (defthm string-listp-of-strtok-aux
    (implies (and (stringp x)
                  (natp xl)
                  (natp n)
                  (= xl (length x))
                  (<= n xl)
                  (string-listp acc))
             (string-listp (strtok-aux x n xl delimiters curr acc)))
    :hints(("Goal" :induct (strtok-aux x n xl delimiters curr acc)))))



(defsection strtok
  :parents (str)
  :short "Tokenize a string with character delimiters."

  :long "<p>@(call strtok) splits the string @('x') into a list of substrings,
based on @('delimiters'), a list of characters.  This is somewhat similar to
repeatedly calling the @('strtok') function in C.</p>

<p>As an example:</p>

@({
 (strtok \"foo bar, baz!\" (list #\\Space #\\, #\\!))
   --&gt;
 (\"foo\" \"bar\" \"baz\")
})

<p>Note that all of the characters in @('delimiters') are removed, and no empty
strings are ever found in @('strtok')'s output.</p>"

  (definlined strtok (x delimiters)
    (declare (xargs :guard (and (stringp x)
                                (character-listp delimiters))))
    (reverse (strtok-aux x 0 (length x) delimiters nil nil)))

  (local (in-theory (enable strtok)))

  (defthm true-listp-of-strtok
    (true-listp (strtok x delimiters))
    :rule-classes :type-prescription)

  (local (defthm lemma
           (implies (and (string-listp x)
                         (string-listp y))
                    (string-listp (revappend x y)))))

  (defthm string-listp-of-strtok
    (implies (force (stringp x))
             (string-listp (strtok x delimiters))))

  (local
   (acl2::assert!
    (equal (strtok "foo bar
baz,
 heyo,
    beyo"
                (list #\Space #\, #\Newline))
           (list "foo" "bar" "baz" "heyo" "beyo")))))


