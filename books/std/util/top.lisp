; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "defaggregate")
(include-book "defaggrify-defrec")
(include-book "defalist")
(include-book "defconsts")
(include-book "defenum")
(include-book "deflist")
(include-book "defmapappend")
(include-book "defmvtypes")
(include-book "defprojection")
(include-book "define")
(include-book "defines")
(include-book "defrule")
(include-book "defredundant")
(include-book "defsum")
(include-book "defval")
(include-book "defval-tests")
(include-book "def-bound-theorems")

(defxdoc std/util
  :parents (std acl2::macro-libraries)
  :short "A macro library that automates defining types, introducing typed
functions, mapping over lists, and many other boilerplate tasks."

  :long "<p>We provide macros for</p>

<ol>

<li>Introducing data types (recognizers and basic theorems)
<ul>
 <li>simple enumerations (@(see defenum)),</li>
 <li>record types like @('struct')s in C (@(see defaggregate)),</li>
 <li>(beta) tagged union / variant / sum types (@(see defsum)),</li>
 <li>typed lists (@(see deflist)), and</li>
 <li>typed alists (@(see defalist))</li>
</ul></li>

<li>Projecting a function across a list and either
<ul>
 <li>cons the results together (@(see defprojection)), or</li>
 <li>append the results (@(see defmapappend)).</li>
</ul></li>

<li>Defining functions with documentation and related theorems (@(see define))</li>
<li>Writing mutually-recursive functions with induction schemes (@(see defines))</li>

<li>Automating other tedious tasks
<ul>
 <li>@(':type-prescription')s for @('mv')-returning functions (@(see defmvtypes))</li>
 <li>defining simple constants with @(see xdoc) documentation (@(see defval))</li>
 <li>defining constants that depend on stobjs, with @('mv') support (@(see defconsts))</li>
 <li>proving rewrite, type prescription, and linear rules about terms in
 @(tsee natp), @(tsee unsigned-byte-p), and @(tsee signed-byte-p).</li>
</ul></li>

</ol>


<h3>Loading the library</h3>

<p>You can load the full library with:</p>

@({
 (include-book \"std/util/top\" :dir :system)
})

<p>Alternately, you may find it convenient to just load individual books.  Each
major macro is typically defined in its own book, e.g., you could do:</p>

@({
 (include-book \"std/util/define\" :dir :system)
 (include-book \"std/util/defaggregate\" :dir :system)
 (include-book \"std/util/deflist\" :dir :system)
})

<p>Note that unlike many other @(see std) libraries, these macros are defined
in the @('STD::') package.  This is mainly to avoid name collisions with older
macros like @('deflist') from other libraries.</p>")
