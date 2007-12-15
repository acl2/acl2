((:files
"
.:
bash.lisp
beta-reduce.lisp
book-thms.lisp
bstar.lisp
computed-hint.lisp
cws.lisp
defmac.lisp
defopener.lisp
defp.lisp
defpun-exec-domain-example.lisp
defpun.lisp
dump-events.lisp
expander.lisp
find-lemmas.lisp
hacker.acl2
hacker.lisp
index.html
Makefile
pack.lisp
priorities.lisp
progndollar.lisp
README
Readme.lsp
simplify-defuns.lisp
simplify-defuns.txt
sticky-disable.lisp
untranslate-patterns.lisp
")
 (:TITLE "Tools")
 (:AUTHOR/S
  "Jared Davis"
  "Peter C. Dillinger"
  "David Greve"
  "Matt Kaufmann"
  "Panagiotis Manolios"
  "J Strother Moore"
  "Sandip Ray"
  "Jun Sawada"
  "Sol Swords"
  )
 (:KEYWORDS
  "macros" "tools" 
  )
 (:ABSTRACT "The books in this directory contain (for the most part)
miscellaneous macros and utility functions to make common constructs
easier and less verbose to write.  See index.html and README for more
detailed documentation than this abstract, and comments in the source
files for more yet.

bstar.lisp defines the macro B* which is a drop-in replacement for
LET* with support for binding MVs and recognizing user-defined binder
forms.

cws.lisp defines CWS, which is a shortcut for printing expressions and
their values without typing formatting strings.

progndollar.lisp defines PROGN$, which evaluates several forms in
sequence for side effects.

See README for brief descriptions of the other books.
")
 (:PERMISSION
  "{bstar,cws,pack,progndollar}.lisp:
copyright (C) 2007 by Sol Swords <sswords@cs.utexas.edu>.

{bash,book-thms,defmac,defopener,defp,simplify-defuns,sticky-disable}.lisp
copyright (C) by 2002, 2005-2007 by Matt Kaufmann

beta-reduce.lisp
copyright (C) 2007 by David Greve

computed-hints.lisp
copyright (C) 1999 by Jun Sawada

{defpun,priorities}.lisp
copyright (C) 2000, 2001 by Panagiotis Manolios and J Strother Moore

{defpun-exec-domain-example}.lisp
copyright (C) 2006 by Sandip Ray

{dump-events,expander}.lisp
copyright (C) 1997 by Computational Logic, Inc.

hacker.lisp
copyright (C) 2007 by Peter Dillinger

untranslate-patterns.lisp
copyright (C) 2006 by Jared Davis <jared@cs.utexas.edu>

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