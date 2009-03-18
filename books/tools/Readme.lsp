((:files
"
.:
Makefile
Readme.lsp
bstar.lisp
cws.lisp
defined-const.lisp
defsum.lisp
deftuple.lisp
flag.acl2
flag.lisp
flag-package.lsp
hons-archive.lisp
index.html
mv-nth.lisp
pack.lisp
progndollar.lisp
rulesets.lisp
safe-case.lisp
saved-errors.lisp
stobj-help.lisp
theory-tools.lisp
types-misc.lisp
with-arith4-help.lisp
")
 (:TITLE "Tools")
 (:AUTHOR/S
  "Sol Swords"
  "Jared Davis"
  )
 (:KEYWORDS
  "macro"
  )
 (:ABSTRACT "The books in this directory contain miscellaneous macros
and tools designed to make common constructs easier and less verbose
to write.  See index.html for more detailed documentation than this
abstract, and comments in the source files for more yet.

bstar.lisp defines the macro B* which is a drop-in replacement for
LET* with support for binding MVs and recognizing user-defined binder
forms.

cws.lisp defines CWS, which is a shortcut for printing expressions and
their values without typing formatting strings.

defined-const.lisp defines DEFINED-CONST, which produces a defconst and a
theorem saying what term it represents while only evaluating that term once (if
the HONS system is present) or twice (if not.)

hons-archive.lisp defines HAR-ZIP and HAR-UNZIP, which are a mechanism
for writing ACL2 objects to files and then loading them in other sessions.
It is only useful when the HONS system is present.

progndollar.lisp defines PROGN$, which evaluates several forms in
sequence for side effects.

safe-case.lisp is a drop-in replacement for case, but causes an error 
if none of the cases are matched.

saved-errors.lisp provides a way of customizing error messages for complex
generated events.

defsum and deftuple.lisp provide macros for defining product types
with constructors, accessors, recognizers, and appropriate theorems
for reasoning about them without reference to the underlying cons
representation.  DEFSUM defines a recursive sum-of-products type,
whereas DEFTUPLE defines a simple product type (tuple.)
Types-misc.lisp and theory-tools.lisp both exist primarily as support
for defsum and deftuple.

pattern-match.lisp provides user-extensible pattern-matching
functionality, especially useful for writing functions that deal with
sum-of-products data structures as defined by defsum.
")
 (:PERMISSION
  "{bstar,cws,defined-const,defsum,deftuple,pack,progndollar,theory-tools,types-misc}.lisp
 copyright (C) 2009 by Sol Swords <sswords@cs.utexas.edu>.

flag.lisp copyright 2008 by Jared Davis <jared@cs.utexas.edu> and Sol Swords.

safe-case.lisp copyright 2008 by Jared Davis <jared@cs.utexas.edu>.

This program is free software; you can redistribute it and/or 
modify it under the terms of the GNU General Public License as 
published by the Free Software Foundation; either version 2 of 
the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, 
but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
GNU General Public License for more details.

You should have received a copy of the GNU General Public 
License along with this program; if not, write to the Free 
Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
Boston, MA 02110-1301, USA."))
