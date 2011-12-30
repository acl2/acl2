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
(include-book "suffixp")

(defxdoc str
  :short "ACL2 String Library"
  :long "<p>This is a rudimentary string library for ACL2.</p>

<p>The functions here are all in logic mode, with verified guards.  In many
cases, some effort has been spent to make them both efficient and relatively
straightforward to reason about.</p>

<h3>Loading the library</h3>

<p>Ordinarily, to use the library one should run</p>
<code>
 (include-book \"str/top\" :dir :system)
</code>

<p>The documentation is then available by typing <tt>:xdoc STR::str</tt>.  All
of the library's functions are found in the <tt>STR</tt> package, so you will
need to do one of the following.</p>

<p>If you are willing to accept a trust tag, you may also include the
<tt>fast-cat</tt> book for faster string-concatenation; see @(see cat) for
details.</p>

<ol>

<li>Type STR:: before the names of the functions,  OR</li>

<li>Additionally load a set of ACL2-package macros which are aliases for the
functions in the STR package.  To do this, run: <tt>(include-book
\"str/abbrevs\" :dir :system)</tt></li>

</ol>

<h3>Copyright Information</h3>

<p>ACL2 String Library<br/>
Copyright (C) 2009-2011 <a href=\"http://www.centtech.com\">Centaur
Technology</a>.</p>

<p>Contact:</p>
<code>
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
</code>

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
  :short "Basic equivalence relations.")

(defsection concatenation
  :parents (str)
  :short "Functions for concatenating strings and character lists.")

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
