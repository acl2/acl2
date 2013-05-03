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
place these files in the demos directory (but we have not yet done so).")

 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2012 David L. Rager <ragerdl@gmail.com>
for files not explicitly copyrighted otherwise

This program is free software; you can redistribute it and/or modify
it under the terms of Version 2 of the GNU General Public License as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA."))
