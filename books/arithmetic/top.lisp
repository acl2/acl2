; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; Matt Kaufmann, Bishop Brock, and John Cowles, with help from Art Flatau
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

#| Modified by John Cowles, University of Wyoming, Summer 1998
     Last modified 30 June 1998
   Modified by Jared Davis, January 2014, to add xdoc documentation.
|#

(in-package "ACL2")

(include-book "equalities")

; The following depends on nothing.

(include-book "rational-listp")

(include-book "nat-listp")

;; Ruben Gamboa added the following books for ACL2(r) (see :doc real).

#+:non-standard-analysis
(include-book ;; jared -- newline keeps these out of deps
 "realp")
#+:non-standard-analysis
(include-book ;; jared -- newline keeps these out of deps
 "real-listp")

; The following two depend individually on the first.

(include-book "inequalities")

(include-book "natp-posp")

(include-book "rationals")



(defxdoc arithmetic-1
  :parents (arithmetic)
  :short "The classic @('books/arithmetic') library is fast and lightweight.
It provides only modest support for reasoning about how basic operations like
@(see <), @(see +), @(see -), @(see *), @(see /), and @(see expt) relate to one
another over integers, rationals, and (for ACL2(r) users) the @(see real)s."

  :long "<h3>Introduction</h3>

<p>The original @('arithmetic') library dates back to the early days of ACL2.
Many people contributed to its development, especially Bishop Brock, John
Cowles, Matt Kaufmann, Art Flatau, and Ruben Gamboa.  The @('natp-posp') book
was contributed more recently by Panagiotis Manolios and Daron Vroon.  The
documentation was added by Jared Davis.</p>

<p>When should you use @('arithmetic')?  Later arithmetic libraries like
@('arithmetic-3') and @('arithmetic-5') are more comprehensive.  They support
reasoning about many operations that @('arithmetic') does not, e.g., @(see
floor) and @(see mod).</p>

<p>Later libraries typically also feature more sophisticated rules that can
automatically solve much harder goals that involve only the basic operators.
So, if you are facing hard arithmetic problems, or if your problems involve
operators that @('arithmetic') does not support, you should definitely consider
using other libraries.</p>

<p>On the other hand, if you have simpler arithmetic needs, the ordinary
@('arithmetic') library may be a fine choice.  It is lightweight and fast, and
typically does not cause rewriting loops.  It can also sometimes be easier to
understand what @('arithmetic') is doing than other libraries, i.e., it is less
likely to lead you to strange subgoals that you don't understand.</p>


<h3>Loading the Library</h3>

<p>To avoid getting locked into any particular arithmetic library, good
practice is to always only @(see local)ly include arithmetic books.  So, to
load the most complete version of the @('arithmetic') library, you should
typically use:</p>

@({
    (local (include-book \"arithmetic/top-with-meta\" :dir :system))
})

<p>In certain cases, more sophisticated users may wish to load only some
portion of the library.  A reasonable, slightly lighter-weight alternative
is:</p>

@({
    (local (include-book \"arithmetic/top\" :dir :system))
})


<h3>Copyright Information</h3>

<p>ACL2 books on arithmetic<br/>
Copyright (C) 1997 Computational Logic, Inc.</p>

<p>This book is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.</p>

<p>This book is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.</p>

<p>You should have received a copy of the GNU General Public License along with
this book; if not, write to the Free Software Foundation, Inc., 675 Mass Ave,
Cambridge, MA 02139, USA.</p>")
