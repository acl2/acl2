((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
list-theory.lisp
modeling/cert.acl2
modeling/Makefile
modeling/memories.lisp
modeling/nested-stobj-toy-isa.lisp
modeling/network-state-basic.lisp
modeling/network-state.lisp
patterned-congruences.lisp
proofs
split-types-examples.lisp
two-pass-constants")
 (:TITLE    "Simple demos for performing modeling and proofs in ACL2")
 (:AUTHOR/S "David Rager" "Matt Kaufmann")
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "modeling" "ACL2" "proofs" "examples" "demonstrations" "demos")
 (:ABSTRACT "Simple demos for performing modeling and proofs in ACL2.

The idea is to place code that demonstrates how to perform modeling in ACL2
inside the modeling directory.  As of May 2013, there isn't anything inside the
proofs directory, but I envision that it will be a place to store code that
demonstrates proof tricks.  For now, code that falls in neither of these two
categories should be placed at the root of books/demos (we may make a misc
subdirectory in the future).  Feel free to add your own subdirectories as
appropriate.

It might be difficult to decide whether a script warrants being placed inside
demos.  Ideally, every file in demos would demonstrate something.  For example,
there are many files inside books/make-event that demonstrate how to do
something in particular with make-event, and it would probably be better to
place these files in the demos directory (but we have not yet done so).

Any large project should be placed in the books/projects directory.  Things in
this directory should be relatively small.")

 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2012 David L. Rager <ragerdl@gmail.com>
for files not explicitly copyrighted otherwise

License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the 'Software'),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE."))
