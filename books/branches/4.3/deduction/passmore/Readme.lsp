; The Utrecht-Texas Equational Prover v-0-0
; A small, modest little prover inspired by the Argonne paradigm and written in ACL2.
; Written by G. O. Passmore (grant@math.utexas.edu)
;
; This ``Readme.Lsp'' is based on the default one that has the following
; copyright banner: `` Copyright (C) 2006  University of Texas at Austin ''

; See the end of top-level file prover.lisp for examples.

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
bewijs.lisp
general.lisp
paramod.lisp
prover.lisp
resolution.lisp
unification.lisp
weighting.lisp

")
 (:TITLE    "The Utrecht-Texas Equational Prover v0-0")
 (:AUTHOR/S "G. O. Passmore") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "" "contributed books")
 (:ABSTRACT "
   A modest little resolution/paramodulation/factoring/merging prover written in the Argonne style
   with Set-Of-Support, pick-given-ratio, mild term weighting, etc.
   Constantly evolving!")
  (:PERMISSION ; author/s permission for distribution and copying:
"The Utrecht-Texas Equational Prover
Copyright (C) 2006 Grant Olney Passmore (grant@math.utexas.edu)

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
