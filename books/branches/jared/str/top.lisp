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

(defxdoc str
  :short "ACL2 String Library"
  :long "<p>This is a rudimentary string library for ACL2.</p>

<p>The functions here are all in logic mode, with verified guards.  In many
cases, some effort has been spent to make them both efficient and relatively
straightforward to reason about.</p>

<h3>Loading the library</h3>

<p>Ordinarily, to use the library one should run</p>
@({
 (include-book \"str/top\" :dir :system)
})

<p>The documentation is then available by typing @(':xdoc str').  All of the
library's functions are found in the @('STR') package.</p>

<p>If you are willing to accept a trust tag, you may also include the
@('fast-cat') book for faster string-concatenation; see @(see cat) for
details.</p>

<h3>Copyright Information</h3>

<p>ACL2 String Library<br/>
Copyright (C) 2009-2013
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
  :parents (str)
  :short "Basic equivalence relations."

  :long "<p>The string library provides the various @(see equivalence)
relations about characters, character lists, and strings.  We end up with the
following @(see refinement) hierarchy:</p>

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
  :parents (str)
  :short "Functions for concatenating strings and character lists.")

(defsection coercion
  :parents (str)
  :short "Functions for converting between strings, symbols, character lists,
and so on.")

(defsection ordering
  :parents (str)
  :short "Functions for comparing and ordering strings in various ways.")

(defsection substrings
  :parents (str)
  :short "Functions for detecting substrings, prefixes, and suffixes.")

(defsection numbers
  :parents (str)
  :short "Functions for working with numbers in strings."
  :long "<p>See also @(see ordering) for some functions that can sort strings
in alphanumeric ways.</p>")

(defsection case-conversion
  :parents (str)
  :short "Functions for recognizing upper- and lower-case characters,
converting between cases, etc.")

(defsection symbols
  :parents (str)
  :short "Functions for working with symbols.")

(defsection substitution
  :parents (str)
  :short "Functions for doing string replacement.")
