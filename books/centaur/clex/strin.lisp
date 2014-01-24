; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "linecol")
(include-book "charset-fns")
(include-book "charlist-fix")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/istrprefixp" :dir :system)
(local (include-book "arithmetic"))

(local (defthm consp-under-iff-when-true-listp
         (implies (true-listp x)
                  (iff (consp x)
                       x))))

(defaggregate strin
  :parents (sin)
  :short "Logical representation of the current state of a string input
stream."

  ((chars character-listp
          "Remaining characters in the input stream.  Note that you should
           typically access these with @(see strin-left), instead of directly
           with @(see strin->chars).")
   (line  posp :rule-classes :type-prescription
          "Current line number, starts at 1.")
   (col   natp :rule-classes :type-prescription
          "Current column number.")
   (file  stringp :rule-classes :type-prescription
          "A name describing where these characters are being read from,
           typically the name of some file."))

  :long "<p>A @('strin-p') structure is intended as a logical fiction to
explain the behavior of the @(see sin) (\"string input\") stobj.</p>

<p>You should not typically create or operate on @('strin-p') structures.
Doing so would create a lot of garbage, and the @(see sin) stobj is generally
more efficient.</p>

<p>We generally think of the line, col, and file fields as a sort of debugging
convenience that, while practically very useful, are not necessarily anything
we want to reason about.</p>

<p>Accordingly, we generally leave all @('strin-p') operations disabled, but
prove some property about their @('chars').</p>"

  :tag :strin)

(defthm strin->chars-under-iff
  (implies (strin-p x)
           (iff (consp (strin->chars x))
                (strin->chars x))))


(define strin-left ((x strin-p))
  :returns (chars character-listp)
  :parents (strin-p)
  :short "Remaining characters in a @(see strin-p)."
  :long "<p>This is an alternative to @(see strin->chars) that @(see
charlist-fix)es the characters.  This is generally preferable to using @(see
strin->chars) directly, and allows us to avoid @(see strin-p) hyps in many
theorems.</p>"
  (mbe :logic (charlist-fix (strin->chars x))
       :exec (strin->chars x))
  ///
  (defthm true-listp-of-strin-left
    (true-listp (strin-left x))
    :rule-classes :type-prescription)
  (defthm strin-left-of-make-strin
    (equal (strin-left (make-strin :chars chars
                                   :line line
                                   :col col
                                   :file file))
           (charlist-fix chars))))


(define empty-strin ()
  :parents (strin-p)
  :short "Create an empty @(see strin-p) structure."
  :long "<p>This is very unlikely to be useful to you.  It exists only because
we need an abstract @(see strin-p) corresponding to the initial @(see
sin$c).</p>

<p>We just leave this enabled.</p>"

  :enabled t
  (make-strin :chars nil
              :file ""
              :line 1
              :col 0))

(define strin-init ((contents stringp "The new contents to load into @('chars').")
                    (filename stringp "The new filename to use.")
                    (x        strin-p "Completely irrelevant."))
  :returns (strin "The newly reset @(see strin-p).")
  :parents (sin$c-init)
  :short "Reset a @(see strin-p) to contain a new string from a new file."
  :long "<p>This strange operation exists only because we need a logical
version of @(see sin$c-init) to use in our abstraction.  We just leave it
enabled.</p>"
  (declare (ignore x))
  :enabled t
  (make-strin :chars (coerce contents 'list)
              :file  filename
              :line  1
              :col   0))

(define strin-endp ((x strin-p))
  :parents (strin-p)
  :short "Are we at the end of the input stream?"
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (atom (strin-left x)))

(define strin-len ((x strin-p))
  :parents (strin-p)
  :short "How many characters are left in the input stream?"
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (len (strin-left x)))

(define strin-car ((x strin-p))
  :parents (strin-p)
  :short "Peek at the first character in the input stream."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (car (strin-left x)))

(define strin-nth ((n natp) (x strin-p))
  :parents (strin-p)
  :short "Peek at the @('n')th character in the input stream."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (nth n (strin-left x)))

(define strin-firstn ((n natp    "Number of characters to extract.")
                      (x strin-p "The input stream."))
  :guard (<= n (strin-len x))
  :parents (strin-p)
  :short "Extract the first @('n') characters as a string."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (coerce (take n (strin-left x)) 'string))

(define strin-cdr ((x strin-p))
  :returns (new-x strin-p :hyp :guard)
  :parents (strin-p)
  :short "Advance the input stream by 1 character."
  (b* (((strin x) x)
       (chars (strin-left x))
       ((when (atom chars))
        (change-strin x :chars nil))
       ((cons char1 rest) chars)
       ((when (eql char1 #\Newline))
        (change-strin x
                      :chars rest
                      :line (+ 1 x.line)
                      :col  0)))
    (change-strin x
                  :chars rest
                  :col (+ 1 x.col)))
  ///
  (defthm strin-left-of-strin-cdr
    (equal (strin-left (strin-cdr x))
           (cdr (strin-left x)))))

(define strin-nthcdr ((n natp) (x strin-p))
  :returns (new-x strin-p :hyp :guard)
  :parents (strin-p)
  :short "Advance the input stream by @('n') characters."
  (b* (((strin x) x)
       (chars (strin-left x))
       ((mv new-chars new-line new-col)
        (lc-nthcdr n chars x.line x.col)))
    (change-strin x
                  :chars new-chars
                  :line new-line
                  :col new-col))
  ///
  (defthm strin-left-of-strin-nthcdr
    (equal (strin-left (strin-nthcdr n x))
           (nthcdr n (strin-left x)))))

(define strin-matches-p ((lit stringp) (x strin-p))
  :parents (strin-p)
  :short "See if some string literal occurs (case sensitively) at the start of
the input stream."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (prefixp (coerce lit 'list) (strin-left x)))

(define strin-imatches-p ((lit stringp) (x strin-p))
  :parents (strin-p)
  :short "See if some string literal occurs (case insensitively) at the start
of the input stream."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (str::iprefixp (coerce lit 'list) (strin-left x)))

(define strin-count-charset ((set charset-p)
                             (x   strin-p))
  :parents (strin-p)
  :short "Count how many characters at the start of the input stream are
members of some particular character set."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (count-leading-charset (strin-left x) set))

(define strin-find ((lit stringp)
                    (x   strin-p))
  :returns (pos "Starting index of the first match, or @('nil') if there are
                 no matches.")
  :parents (strin-p)
  :short "Find the first occurrence of the string literal in the input stream,
and return its position."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (listpos (coerce lit 'list) (strin-left x)))

