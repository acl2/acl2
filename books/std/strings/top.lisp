; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "case-conversion")
(include-book "cat")
(include-book "digitp")
(include-book "eqv")
(include-book "firstn-chars")
(include-book "hexify")
(include-book "html-encode")
(include-book "ieqv")
(include-book "iprefixp")
(include-book "iless")
(include-book "isort")
(include-book "istrpos")
(include-book "istrprefixp")
(include-book "isubstrp")
(include-book "natstr")
(include-book "strline")
(include-book "pad")
(include-book "prefix-lines")
(include-book "strpos")
(include-book "strrpos")
(include-book "strprefixp")
(include-book "strnatless")
(include-book "strsplit")
(include-book "strsubst")
(include-book "strtok")
(include-book "strval")
(include-book "substrp")
(include-book "subseq")
(include-book "suffixp")
(include-book "symbols")

(defxdoc std/strings
  :short "A library with many useful functions for working with strings, and
for reasoning about ACL2's built-in string operations and these new
operations."

  :long "<p>The @('std/strings') library is a rudimentary string library for
ACL2.  The functions here are all in logic mode, with verified guards.  In many
cases, some effort has been spent to make them both efficient and relatively
straightforward to reason about.</p>

<h3>Loading the library</h3>

<p>Ordinarily, to use the library one should run</p>

@({
 (include-book \"std/strings/top\" :dir :system)
})

<p>All of the library's functions are found in the @('STR') package.</p>

<p>If you are willing to accept a trust tag, you may also include the
@('fast-cat') book for faster string-concatenation; see @(see cat) for
details.</p>

<h3>Copyright Information</h3>

<p>ACL2 String Library<br/>
Copyright (C) 2009-2014
<a href=\"http://www.centtech.com\">Centaur Technology</a>.</p>

<p>Contact:</p>
@({
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
})

<p>This program is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2 of the License, or (at your option) any
later version.</p>

<p>This program is distributed in the hope that it will be useful but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Suite 500, Boston, MA 02110-1335, USA.</p>")


;; Function groups...

(defsection equivalences
  :parents (std/strings)
  :short "Basic equivalence relations."

  :long "<p>The string library provides the various @(see acl2::equivalence)
relations about characters, character lists, and strings.  We end up with the
following @(see acl2::refinement) hierarchy:</p>

@({
                      equal
          ______________|________________
         |              |                |
       chareqv         list-equiv       streqv
         |              |                |
       ichareqv        charlisteqv      istreqv
                        |
                       icharlisteqv
})")

(defsection concatenation
  :parents (std/strings)
  :short "Functions for joining strings together."

  :long "<p><b><color rgb='#ff0000'>Efficiency Warning</color></b>.
Concatenating strings in ACL2 is fundamentally slow.  Why?  In Common Lisp,
strings are just arrays of characters, and there is not any mechanism for
efficiently splicing together arrays.  Any kind of string concatenation, then,
minimally requires creating a completely new array and copying all of the input
characters into it.  This makes it especially slow to repeatedly use, e.g.,
@(see cat) to build up a string.</p>

<p>To build strings more efficiently, a good general strategy is to build up a
reverse-order character list, and then convert it into a string at the end.
See for instance the functions @(see revappend-chars) and @(see
rchars-to-string), which make this rather easy to do.</p>")

(defsection coercion
  :parents (std/strings)
  :short "Functions for converting between strings, symbols, character lists,
and so on.")

(defsection ordering
  :parents (std/strings)
  :short "Functions for comparing and ordering strings in various ways.")

(defsection substrings
  :parents (std/strings)
  :short "Functions for detecting substrings, prefixes, and suffixes.")

(defsection numbers
  :parents (std/strings)
  :short "Functions for working with numbers in strings."
  :long "<p>See also @(see ordering) for some functions that can sort strings
in alphanumeric ways.</p>")

(defsection cases
  :parents (std/strings)
  :short "Functions for recognizing and translating between upper- and
lower-case.")

(defsection symbols
  :parents (std/strings)
  :short "Functions for working with symbols.")

(defsection substitution
  :parents (std/strings)
  :short "Functions for doing string replacement.")

(defsection lines
  :parents (std/strings)
  :short "Functions for operating on the lines of a string."

  :long "<p>Note that these functions generally work with Unix-style newline
characters, i.e., @('\\n') instead of something like @('\\r\\n').  Depending on
your application, this may or may not be appropriate.</p>

<p>One option for treating a string as lines is to just use, e.g., @(see
strtok) to literally split it into a list of lines.  The functions here are
generally meant to be more efficient, e.g., @(see prefix-lines) can add a
prefix to every line without constructing an temporary string list or doing any
intermediate string concatenation.</p>")

