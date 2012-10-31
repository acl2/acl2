; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

(in-package "ACL2")
(include-book "bits-between")
(include-book "bitsets")
(include-book "bitsets-opt")
;; (include-book "defaults")
(include-book "equal-by-logbitp")
(include-book "ihs-extensions")
(include-book "integer-length")
(include-book "sbitsets")
(include-book "part-select")
(include-book "extra-defs")

(defxdoc bitops
  :short "Centaur Bitops Library"

  :long "<p>We provide:</p>

<ol>

<li>Some books of arithmetic theorems that augment the @(see ihs) books,</li>

<li>A @(see bitsets) library for representing finite sets of (small) natural
numbers as bitmasks, and</li>

<li>A <see topic=\"@(url sbitsets)\">sparse bitsets</see> library for
representing sets of natural numbers with lists of offset/bitmask pairs.</li>

</ol>

<h3>Loading the Library</h3>

<p>Although there is a @('top.lisp') file, it's generally best to load only
what you actually want from the bitops library.  For arithmetic support, you
might try:</p>

@({
 (local (include-book \"bitops/ihs-extensions\" :dir :cbooks))
 (local (include-book \"bitops/equal-by-logbitp\" :dir :cbooks))
})

<p>For the bitsets library:</p>

@({
 (include-book \"bitops/bitsets\" :dir :cbooks)
})

<p>Or for the sparse bitsets library:</p>

@({
 (include-book \"bitops/sbitsets\" :dir :cbooks)
})

<h3>Copyright Information</h3>

<p>Centaur Bitops Library</p>

<p>Copyright (C) 2010-2011 <a href=\"http://www.centtech.com\">Centaur
Technology</a>.</p>

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
