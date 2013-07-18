; Standard IO Library
; Portions are Copyright (C) 2008-2013 Centaur Technology
; Portions are Copyright (C) 2004-2013 by Jared Davis
; See individual books for details
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

(in-package "ACL2")
(include-book "base")
(include-book "combine")
(include-book "nthcdr-bytes")
(include-book "read-file-bytes")
; (include-book "read-file-characters-no-error") ; omitted due to weird license stuff
(include-book "read-file-characters")
(include-book "read-file-lines")
(include-book "read-file-objects")
(include-book "read-ints")
(include-book "take-bytes")


(defxdoc std/io
  :parents (std io interfacing-tools)
  :short "A library for reasoning about file input/output operations."

  :long "<h3>Introduction</h3>

<p>The @('std/io') library provides:</p>

<ul>

<li>Basic lemmas about low-level, built-in ACL2 @(see io) operations like @(see
open-input-channel), @(see read-byte$), @(see close-output-channel), and so
on.  (These are especially useful for guard proofs about IO functions.)</li>

<li>A @(see file-measure) for proving the termination of functions that read
from files.</li>

<li>Extended low-level file input operations such as @(see read-bytes$), which
lets you efficiently read 16-, 32-, and 64-bits from a file at once.</li>

<li>High-level operations for reading whole files, such as @(see
read-file-bytes), @(see read-file-characters), and @(see
read-file-objects).</li>

</ul>

<p>Some basic information about low-level i/o facilities in ACL2 can be found
in @(see io), and for some  and also @(see logical-story-of-io).</p>

<h3>Loading the Library</h3>

<p>If you just want to load the whole IO library, you can include the @('top')
book, e.g.,</p>

@({ (include-book \"std/io/top\" :dir :system) })

<p>But this may be more than you need.  The library is split up into sensible
books that can generally be loaded individually.</p>")



(defxdoc logical-story-of-io
  :parents (std/io)
  :short "How file reading operations are modeled in the ACL2 logic."

  :long "<p>ACL2's @(see io) operations are available in @(':logic') mode (see
@(see defun-mode)).  This is somewhat tricky to justify in the logic, since,
e.g., the contents of a file is external to ACL2, can be changed over time, and
so on.</p>

<p>Practically speaking, most users don't need to pay any attention to the
details of this story.  Instead, they can just include the @(see std/io)
library, which develops the basic theorems that are necessary to reason about
the io primitives.</p>

<p>But if for some reason, you do want to understand the logical story, you
might start with this paper:</p>

<p>Jared Davis.  <a
href='http://www.ccs.neu.edu/home/pete/acl206/papers/davisb.pdf'>Reasoning
about ACL2 File Input</a>.  ACL2 Workshop 2006.</p>")
