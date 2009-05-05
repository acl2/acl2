((:FILES "
.:
all.acl2
all.lisp
bridge.acl2
bridge.lisp
copyright
defcode.acl2
defcode.lisp
defstruct-parsing.acl2
defstruct-parsing.lisp
hacker.acl2
hacker.lisp
hacker-pkg.lsp
Makefile
progn-bang-enh.acl2
progn-bang-enh.lisp
raw.acl2
raw.lisp
Readme.lsp
redefun.acl2
redefun.lisp
rewrite-code.acl2
rewrite-code.lisp
rewrite-code-pkg.lsp
subsumption.acl2
subsumption.lisp
table-guard.acl2
table-guard.lisp
"
)
 (:TITLE    "Hacking & Extending ACL2")
 (:AUTHOR/S "Peter C. Dillinger") ; With guidance & advice from Matt Kaufmann and Panagiotis Manolios
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "book contributions" "contributed books"
   "hacking" "system" "defcode" "redefun" "trust tags" "ttags"
   "extensions" "raw mode" "raw lisp"
   )
 (:ABSTRACT
"This support code is intended as a library to those who wish to use
trust tags to modify or extend core ACL2 behavior.  We add some other
constructs to the set of low-level tools enabled by trust tags that make
system modifications easier to specify and keep track of.  We also offer
some high-level tools that offer significant benefits (in both ease &
soundness) over more direct methods of overriding behavior.  See the
comments in Readme.lsp and individual files for more info.
")
 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2008 Peter C. Dillinger, the Georgia Tech Research Corporation,
                    and Northeastern University

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

#|
This was developed as part of ACL2s: "The ACL2 Sedan."

hacker-pkg.lsp
    Package & documentation topic/section used in preambles


all.lisp
    Book that includes all of the below

bridge.lisp
    Book for bridging the gap between ACL2 and raw Lisp

defcode.lisp
    Book for the DEFCODE construct (ttag required)

defstruct-parsing.lisp
    Book for parsing defstruct calls

hacker.lisp
    Basic book with hacking constructs

progn-bang-enh.lisp
    Used by defcode.lisp.  Subject to change. :)

raw.lisp
    Book for making raw definitions in a nice way

redefun.lisp
    Book for overriding and rewriting existing definitions

rewrite-code.lisp
    Book with tools for rewriting and copying existing code
    (used by redefun.lisp)

subsumption.lisp
    Book with constructs to do ttag subsumption

table-guard.lisp
    An example application of this stuff to allow extension of table
    guards, including the acl2-defaults-table.
|#
