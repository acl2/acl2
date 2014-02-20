; OSLIB -- Operating System Utilities
; Copyright (C) 2013 Centaur Technology
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

(in-package "OSLIB")

(include-book "argv")
(include-book "catpath")
(include-book "date")
(include-book "getpid")
(include-book "lisptype")
(include-book "ls")
(include-book "mkdir")
(include-book "file-types")
(include-book "tempfile")
(include-book "rmtree")

(defxdoc oslib
  :parents (acl2::interfacing-tools)
  :short "Operating System Utilities Library"

  :long "<p>This is a collection of ACL2 functions that allow you to do various
basic operating-system related tasks, e.g., you can get the current PID or user
name, file listings, etc.</p>

<p>Almost everything here necessarily requires a trust tag, because it is
implemented in raw Lisp.  We believe we have connected this functionality to
ACL2 in a sound way, using @(see read-acl2-oracle).</p>

<p>The library is far from complete since we tend to extend it only as the need
arises.  Most functions are not implemented on all Lisp and operating system
combinations, and will simply fail on unsupported Lisps.</p>


<h3>Loading the library</h3>

<p>You can load the full library with:</p>

@({
 (include-book \"oslib/top\" :dir :system)
})

<p>But it is often better, in this case, to just pick and choose the specific
books you want to load.</p>


<h3>Copyright Information</h3>

<p>OSLIB - Operating System Utilities<br/>
Copyright (C) 2013 <a href=\"http://www.centtech.com\">Centaur Technology</a>.</p>

<p>Contact:</p>
@({
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
})

<p>OSLIB is free software; you can redistribute it and/or modify it under the
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




