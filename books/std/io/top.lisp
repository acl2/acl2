; ACL2 Standard Library
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "base")
(include-book "open-channels")
(include-book "combine")
(include-book "nthcdr-bytes")
(include-book "read-file-bytes")
(include-book "read-file-characters")
(include-book "read-file-lines")
(include-book "read-file-lines-no-newlines")
(include-book "read-file-objects")
(include-book "read-ints")
(include-book "take-bytes")
(include-book "print-objects")

#||
;; Books we won't actually include, but would like cert.pl to build for us.
 (include-book "unsound-read")                 ;; omitted due to ttags
 (include-book "read-string")                  ;; omitted due to ttags
 (include-book "read-file-characters-no-error") ;; omitted due to weird license stuff
||#


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
