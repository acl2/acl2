; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "CUTIL")
(include-book "defaggregate")
(include-book "defalist")
(include-book "defenum")
(include-book "deflist")
(include-book "defmapappend")
(include-book "defmvtypes")
(include-book "defprojection")
(include-book "defsection")

#||
;; Fool the dependency scanner into also building the test files, even though
;; they're not needed.
(include-book "deflist-tests")
(include-book "defalist-tests")
(include-book "defmapappend-tests")
(include-book "defprojection-tests")
||#

(defxdoc cutil
  :short "Centaur Utility Library"

  :long "<p>We provide macros for</p>

<ol>

<li>Introducing data types (recognizers and basic theorems)
<ul>
 <li>simple enumerations (@(see defenum)),</li>
 <li>record types like <tt>struct</tt>s in C (@(see defaggregate)),</li>
 <li>typed lists (@(see deflist)), and</li>
 <li>typed alists (@(see defalist))</li>
</ul></li>

<li>Projecting a function across a list and either
<ul>
 <li>cons the results together (@(see defprojection)), or</li>
 <li>append the results (@(see defmapappend)).</li>
</ul></li>

<li>Structing books (@(see defsection))</li>

<li>Automating other tedious tasks
<ul>
 <li><tt>:type-prescription</tt>s for <tt>mv</tt>-returning functions (@(see defmvtypes))</li>
</ul></li>

</ol>


<h3>Loading the library</h3>

<p>A ttag-free version of the complete library can be loaded with:</p>

<code>
 (include-book \"cutil/top\" :dir :system)
</code>

<p>Or, if you really care about performance, you can load the <tt>top-opt</tt>,
which includes some optimizations but requires a ttag.</p>


<h3>Copyright Information</h3>

<p>CUTIL - Centaur Basic Utilities<br/>
Copyright (C) 2008-2011 <a href=\"http://www.centtech.com\">Centaur
Technology</a>.</p>

<p>Contact:</p>
<code>
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
</code>

<p>CUTIL is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.</p>

<p>This program is distributed in the hope that it will be useful but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Suite 500, Boston, MA 02110-1335, USA.</p>")








