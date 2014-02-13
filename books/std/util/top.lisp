; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "defaggregate")
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
 <li>defining simple constants with @(see xval) documentation (@(see defval))</li>
 <li>defining constants that depend on stobjs, with @('mv') support (@(see defconsts))</li>
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

