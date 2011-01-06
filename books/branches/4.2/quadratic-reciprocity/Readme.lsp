((:FILES
"
.:
Makefile
Readme.lsp
certify.lsp
eisenstein.lisp
euclid.lisp
euler.lisp
fermat.lisp
gauss.lisp
mersenne.lisp
")
 (:TITLE    "Quadratic reciprocity")
 (:AUTHOR/S 
  "David Russinoff"
  )
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
  "number theory" "quadratic reciprocity" "Euclid" "Fermat" "Guass"
   )
 (:ABSTRACT "This directory contains an ACL2 proof script for the law of
uadratic reciprocity:

  if p and q are distinct odd primes, then 
    (p is a quadratic residue mod q <=> q is a quadratic residue mod p)
     <=>
    ((p-1)/2) * ((q-1)/2) is even.

The proof is an adaptation of the author's Nqthm formalization of the same
theorem.  See file certify.lsp for more information.")
 (:PERMISSION
"An ACL2 Proof of Gauss's Law of Quadratic Reciprocity
Copyright (C) 2007 David Russinoff

This program is free software; you can redistribute it and/ormodify it under
the terms of the GNU General Public Licenseas published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc., 51
Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."
  ))
