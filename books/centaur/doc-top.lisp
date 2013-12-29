; Centaur Book Documentation
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

; This file was created 12/2013 by Matt Kaufmann, by extracting the defxdoc
; form acl2::top form from doc.lisp so that it is available for building the
; text-based version of the acl2+books combined manual.

(in-package "ACL2")

(include-book "xdoc/base" :dir :system)

(defxdoc acl2::top
   :short "User manual for the <a
href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2 Theorem Prover</a> and
the <a href='http://acl2-books.googlecode.com/'>ACL2 Community Books</a>"

   :long "<h3>Introduction</h3>

<p><a href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2</a> is an
interactive theorem prover.  It combines a Lisp-based programming language for
developing formal models of systems with a reasoning engine that can prove
properties about these models.  It has been used to <a
href='http://en.wikipedia.org/wiki/Formal_verification'>formally verify</a>
many <see topic='@(url interesting-applications)'>interesting systems</see> in
academia and industry.</p>

<p>The <a href='http://acl2-books.googlecode.com/'>ACL2 Community Books</a> are
the canonical set of open-source libraries (\"@(see books)\") for ACL2.  They
include lemma libraries for reasoning in many domains, macro libraries for more
quickly writing and documenting code, interfacing tools for connecting ACL2 to
other systems, productivity tools for better proof automation and debugging,
and specialty libraries for areas like @(see hardware-verification).</p>

<p>This manual was generated on <b>@(`(:raw (oslib::date))`)</b>.  It covers
both ACL2 and the Community Books.  It is derived by combining the classic
@(see doc-string)s found in the ACL2 source code and some books with the @(see
xdoc) topics found in other books.  Besides just importing the documentation,
we also rearrange the topic hierarchy to try to improve its organization.</p>

<p>This manual is very much a work in progress.  If you would like to
contribute to its development, please join the <a
href='https://code.google.com/p/acl2-books/'>acl2-books</a> project!</p>")
