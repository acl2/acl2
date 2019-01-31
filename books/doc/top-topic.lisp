; Centaur Book Documentation
; Copyright (C) 2008-2011 Centaur Technology
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

; This file was created 12/2013 by Matt Kaufmann, by extracting the defxdoc
; form acl2::top form from doc.lisp so that it is available for building the
; text-based version of the acl2+books combined manual.

(in-package "ACL2")

(include-book "xdoc/base" :dir :system)

(defxdoc top
   :short "User manual for the <a
href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2 Theorem Prover</a> and
the <a href='https://github.com/acl2/acl2/tree/master/books'>ACL2 Community Books</a>"

   :long "<h3>Introduction</h3>

<p><a href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2</a> is an
interactive theorem prover.  It combines a Lisp-based programming language for
developing formal models of systems with a reasoning engine that can prove
properties about these models.  It has been used to <a
href='http://en.wikipedia.org/wiki/Formal_verification'>formally verify</a>
many <see topic='@(url interesting-applications)'>interesting systems</see> in
academia and industry.</p>

<p>The <a href='https://github.com/acl2/acl2/tree/master/books'>ACL2 Community
Books</a> are the canonical set of open-source libraries (\"@(see books)\") for
ACL2.  They include lemma libraries for reasoning in many domains, macro
libraries for more quickly writing and documenting code, interfacing tools for
connecting ACL2 to other systems, productivity tools for better proof
automation and debugging, and specialty libraries for areas like @(see
hardware-verification).</p>

<p>This manual was generated on <b>@(`(:raw (oslib::date))`)</b>.  It covers
both ACL2 and the Community Books.  It is derived by combining</p>

<ul>

<li>the documentation for the ACL2 system itself&mdash;mostly written by Matt
Kaufmann and J Moore</li>

<li>the documentation for many Community Books&mdash;contributed by numerous
members of the ACL2 community</li>

</ul>

<p>Besides just importing the documentation, we also rearrange the topic
hierarchy to try to provide a coherent organization.</p>

<p>This manual is very much a work in progress.  If you would like to
contribute to its development, please join the <a
href='https://github.com/acl2/'>acl2 project on GitHub</a>!</p>")
