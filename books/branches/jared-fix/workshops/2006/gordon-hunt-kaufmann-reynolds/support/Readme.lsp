; The Makefile has modified the default value of INHIBIT from Makefile-generic
; in order that we see warnings in the .out files.  We should see
; Double-rewrite warnings there that correspond exactly to comments about
; Double-rewrite (notice the upper-case D) in the .lisp files.

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
basic.lisp
data.lisp
guarded.lisp
log
script.lisp
stobjs.lisp
")
 (:TITLE    "An Embedding of the ACL2 Logic in HOL")
 (:AUTHOR/S ; non-empty list of author strings
  "Michael J. C. Gordon"
  "Warren A. Hunt, Jr."
  "Matt Kaufmann"
  "James Reynolds")
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
  "verification" "formal methods" "logic" "ACL2" "HOL" "HOL4"
  "first-order logic" "higher-order logic" "sound translation" "proof oracle")
 (:ABSTRACT "
This directory contains supporting materials for the ACL2 2006 workshop paper
with the indicated title and authors.")
  (:PERMISSION ; author/s permission for distribution and copying:
"ACL2/HOL supporting materials
Copyright (C) 2006 Michael J. C. Gordon, Warren A. Hunt, Jr., Matt Kaufmann,
and James Reynolds.

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA."))

Contents of this directory.

script.lisp     Input file for ACL2, to run the examples (with directions at
                the top)
log             Output file
data.lisp       Defines function make-instrs for making list of reads and
                writes for our tests
basic.lisp      Simple definition of read/write interpreter
guarded.lisp    Same as basic.lisp, except with guards for more efficient
                execution
stobjs.lisp     Rework of basic.lisp (and guarded.lisp) to use single-threaded
                objects (stobjs).  Here, these allow us to use true arrays in
                an applicative setting.

======================================================================

Full times can be seen by looking at log, where "run-gbc time" means cpu time
minus garbage collection, and "gbc time" means "garbage collection time".  Here
we report real times:

basic.lisp:    5.170 secs
guarded.lisp:  1.980 secs
stobjs.lisp:   0.140 secs
