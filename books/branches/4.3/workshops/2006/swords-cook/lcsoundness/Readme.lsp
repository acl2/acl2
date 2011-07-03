; Proof of the soundness of the simply typed lambda calculus
; Copyright (C) 2006 Sol Swords and William Cook.

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
LambdaCalcBasis.lisp
LambdaCalcSoundness.lisp
Makefile
Readme.lsp
defsum-thms.lisp
defsum.lisp
pattern-match.lisp
")
 (:TITLE    "Soundness of the Simply Typed Lambda Calculus")
 (:AUTHOR/S "Sol Swords" "William Cook")
 (:KEYWORDS
   "Lambda-calculus" "Programming languages" "Type theory")
 (:ABSTRACT "
To make it practical to mechanize proofs in programming language metatheory,
several capabilities are required of the theorem proving framework.  One must
be able to represent and efficiently reason about complex recursively-defined
expressions, define arbitrary induction schemes including mutual inductions
over several objects and inductions over derivations, and reason about variable
bindings with minimal overhead.  We introduce a method for performing these
proofs in ACL2, including a macro which automates the process of defining
functions and theorems to facilitate reasoning about recursive data types.  To
illustrate this method, we present a proof in ACL2 of the soundness of the
simply typed $\lambda$-calculus.
")
  (:PERMISSION ; author/s permission for distribution and copying:
"Soundness of the Simply Typed Lambda Calculus
Copyright (C) 2006 Sol Swords and William Cook

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
