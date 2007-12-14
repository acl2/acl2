((:files
"
.:
Makefile
bstar.lisp
cws.lisp
index.html
pack.lisp
progndollar.lisp
")
 (:TITLE "Macro Magic")
 (:AUTHOR/S
  "Sol Swords"
  )
 (:KEYWORDS
  "macro"
  )
 (:ABSTRACT "The books in this directory contain miscellaneous macros
to make common constructs easier and less verbose to write.  See
index.html for more detailed documentation than this abstract, and
comments in the source files for more yet.

bstar.lisp defines the macro B* which is a drop-in replacement for
LET* with support for binding MVs and recognizing user-defined binder
forms.

cws.lisp defines CWS, which is a shortcut for printing expressions and
their values without typing formatting strings.

progndollar.lisp defines PROGN$, which evaluates several forms in
sequence for side effects.

")
 (:PERMISSION
  "{bstar,cws,pack,progndollar}.lisp copyright (C) 2007 by Sol Swords
<sswords@cs.utexas.edu>.


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