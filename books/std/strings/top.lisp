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
(include-book "binary")
(include-book "case-conversion")
(include-book "cat")
(include-book "charset")
(include-book "charset-fns")
(include-book "decimal")
(include-book "digit-to-char")
(include-book "eqv")
(include-book "firstn-chars")
(include-book "hexify")
(include-book "hex")
(include-book "html-encode")
(include-book "url-encode")
(include-book "ieqv")
(include-book "iprefixp")
(include-book "iless")
(include-book "isort")
(include-book "istrpos")
(include-book "istrprefixp")
(include-book "isubstrp")
(include-book "strline")
(include-book "octal")
(include-book "pad")
(include-book "prefix-lines")
(include-book "strpos")
(include-book "strrpos")
(include-book "strprefixp")
(include-book "strnatless")
(include-book "strsplit")
(include-book "strsubst")
(include-book "strtok")
(include-book "substrp")
(include-book "subseq")
(include-book "suffixp")
(include-book "symbols")
(include-book "strrange-equiv")

(defxdoc std/strings
  :parents (std acl2::strings)
  :short "A library with many useful functions for working with strings, and
for reasoning about ACL2's built-in string operations and these new
operations."

  :long "<p>The @('std/strings') library is a rudimentary string library for
ACL2.  The functions here are all in logic mode, with verified guards.  In many
cases, some effort has been spent to make them both efficient and relatively
straightforward to reason about.</p>


<h3>Loading the library</h3>

<p><b>Note:</b> All of the library's functions are found in the @('STR')
package.</p>

<p>Ordinarily, to use the library one should run</p>

@({
 (include-book \"std/strings/top\" :dir :system)
})

<p>To keep the top book more lightweight, certain functionality is excluded by
default.  Here are additional books you may want to include:</p>

<ul>
<li>@('std/strings/base64') &mdash; support for @(see base64) encoding/decoding</li>
<li>@('std/strings/pretty') &mdash; support for @(see pretty-printing) ACL2 expressions</li>
</ul>

<h5>Advanced Options</h5>

<p>If you are willing to accept a trust tag, you may also include the
@('fast-cat') book for faster string-concatenation; see @(see cat) for
details.</p>

<p>If you only need some subset of the available functions, it's generally
reasonable to just include individual books instead of the @('top') book.
However, book names and dependencies do sometimes change, so in general we
recommend just loading the @('top') book.</p>

<p>If you want to be able to use the string operations but don't have any need
to reason about them, e.g., because you are writing code for macros, then you
might instead want to load either:</p>

<ul>
<li>@('std/strings/defs') &mdash; logic mode definitions, minimal theorems</li>
<li>@('std/strings/defs-program') &mdash; program mode definitions, no theorems</li>
</ul>

<p>These books may load slightly faster than the @('top') book and may help to
minimize the effects of loading the library on your theory.</p>")


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
