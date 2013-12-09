((:FILES
  "
.:
Makefile
Readme.lsp
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
  "number theory" "quadratic reciprocity" "Euclid" "Fermat" "Gauss"
  )
 (:ABSTRACT "This directory contains an ACL2 proof script for the law of
quadratic reciprocity:

  if p and q are distinct odd primes, then 
    (p is a quadratic residue mod q <=> q is a quadratic residue mod p)
     <=>
    ((p-1)/2) * ((q-1)/2) is even.

The proof is an adaptation of the author's Nqthm formalization of the same
theorem:

http://www.cs.utexas.edu/users/boyer/ftp/nqthm/nqthm-1992/examples/basic/new-gauss.events

The script consists of six ACL2 books:

  euclid
     Divisibility, primes, and two theorems of Euclid:
     (1) The infinitude of the set of primes
     (2) if p is a prime and p divides a * b, then p divides either a or b.

  fermat
     Fermat's Theorem: if p is a prime and p does not divide m, then
     mod(m^(p-1),p) = 1.

  euler
     Quadratic residues and Euler's Criterion: if p is an odd prime and p does
     not divide m, then

          mod(m^((p-1)/2),p) = 1 if m is a quadratic residue mod p
                               p-1 if not.

     A by-product of the proof is Wilson's Theorem: mod((p-1)!,p) = p-1.
     As a consequence, we also prove the First Supplement to the Law of Quadratic
     Reciprocity: -1 is a quadratic residue mod p iff mod(p,4) = 1.

  gauss
      Gauss's Lemma:  Let p be an odd prime and let m be relatively prime to p.
      Let mu be the number of elements of the sequence

        (mod(m,p), mod(2*m,p), ..., mod(((p-1)/2)*m,p))

      that exceed (p-1)/2.  Then m is a quadratic residue mod p iff mu is even.
      As a corollary, we also prove the Second Supplement to the Law of Quadratic
      Reciprocity: 2 is a quadratic residue mod p iff mod(p,8) is either 1 or -1.

  eisenstein
      A formalization of Eisenstein's proof of quadratic reciprocity.

  mersenne
      An application to the Mersenne prime problem by way of a theorem of Euler:
      if p and 2*p+1 are both prime and mod(p,4) = 3, then 2^p-1 is divisible by
      2*p+1.")
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
