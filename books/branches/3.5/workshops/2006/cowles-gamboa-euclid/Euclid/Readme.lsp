((:FILES "
.:
Makefile
Readme.lsp
certify.lsp
ed1.acl2
ed1.lisp
ed2a.lisp
ed2b.lisp
ed3.acl2
ed3.lisp
ed4aa.acl2
ed4aa.lisp
ed4ab.acl2
ed4ab.lisp
ed4ba.acl2
ed4ba.lisp
ed4bb.acl2
ed4bb.lisp
ed4ca.acl2
ed4ca.lisp
ed4cb.acl2
ed4cb.lisp
ed4da.acl2
ed4da.lisp
ed4db.acl2
ed4db.lisp
ed5aa.acl2
ed5aa.lisp
ed5ba.lisp
ed6a.acl2
ed6a.lisp
fld-u-poly
prime-fac.acl2
prime-fac.lisp

./fld-u-poly:
Makefile
certify.lsp
coe-fld.acl2
coe-fld.lisp
fucongruencias-producto.acl2
fucongruencias-producto.lisp
fucongruencias-suma.acl2
fucongruencias-suma.lisp
fuforma-normal.acl2
fuforma-normal.lisp
fumonomio.acl2
fumonomio.lisp
fuopuesto.acl2
fuopuesto.lisp
fupolinomio.acl2
fupolinomio.lisp
fupolinomio-normalizado.acl2
fupolinomio-normalizado.lisp
fuproducto.acl2
fuproducto.lisp
fuquot-rem.acl2
fuquot-rem.lisp
fusuma.acl2
fusuma.lisp
futermino.acl2
futermino.lisp
") ;; NOTE: The book in ed5ba.lisp is left out of the above list
   ;;       because it requires ACL2r.(See :ABSTRACT below.) 

 (:TITLE "ACL2 Euclidean Domain Books")
 (:AUTHOR/S "John R. Cowles" "Ruben A. Gamboa")
 (:KEYWORDS
  "Euclidean domains" "unique factorization")
 (:ABSTRACT "
Readme.lsp
certify.lsp
prime-fac.lisp -  Unique Prime Factorization Theorem for Positive Integers.

ed1.lisp   -- Book 1   -- Multiplicative Identity Existence

ed2a.lisp  -- Book 2a  -- Multiplicative Size Property

ed2b.lisp  -- Book 2b  -- CounterExample.
              An Euclidean Domain without the
              Multiplicative Size Property.

ed3.lisp   -- Book 3   -- Algebraic Theory 
              Convenient notation and events for using the theory of an
              Euclidean Domain.

ed4aa.lisp -- Book 4aa -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is floor and Remainder is mod.
              This version uses quantifiers (defun-sk) and is non-executable.

ed4ab.lisp -- Book 4ab -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is floor and Remainder is mod.
              This version uses computable Skolem functions [in place of
              quantifiers (defun-sk)] and is executable.

ed4ba.lisp -- Book 4ba -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is truncate and Remainder is rem. 
              This version uses quantifiers (defun-sk) and is non-exedutable.

ed4bb.lisp -- Book 4bb -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is truncate and Remainder is rem. 
              This version uses computable Skolem functions [in place of
              quantifiers (defun-sk)] and is executable.

ed4ca.lisp -- Book 4ca -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is ceiling and Remainder is c-mod,
              a version of mod using ceiling in place of floor. 
              This version uses quantifiers (defun-sk) and is non-exedutable.

ed4cb.lisp -- Book 4cb -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is ceiling and Remainder is c-mod,
              a version of mod using ceiling in place of floor. 
              This version uses computable Skolem functions [in place of
              quantifiers (defun-sk)] and is executable.

ed4da.lisp -- Book 4da -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization. 
              Here Size is abs; Quotient is round and Remainder is rnd-rem,
              a version of rem using round in place of truncate.
              This version uses quantifiers (defun-sk) and is non-exedutable.

ed4db.lisp -- Book 4db -- Example: Integers.
              The Integers are shown to be an Euclidean Domain with
              unique factorization.
              Here Size is abs; Quotient is round and Remainder is rnd-rem,
              a version of rem using round in place of truncate.
              This version uses computable Skolem functions [in place of
              quantifiers (defun-sk)] and is executable.

ed5aa.lisp -- Book 5aa -- Example: Gaussian Integers.
              The Gaussian Integers, complex numbers with integer real and
              imaginary parts, are shown to be an Euclidean Domain with unique
              factorization. 
              Here Size is sqr-abs, the square of complex abs; Quotient is 
              based on rounding the real and imaginary parts of the complex 
              quotient and Remainder is a version of rem using the above rounding
              in place of truncate.
              This version uses quantifiers (defun-sk) and is non-exedutable.

ed5ba.lisp -- Book 5ba -- Example:
              Complex numbers of the form a+b(sqrt 2)i where a and b are integers
              are shown to be an Euclidean domain with unique factorization.
              This version uses ACL2r.
              This version uses quantifiers (defun-sk) and is non-exedutable.

ed6a.lisp  -- Book 6a  -- Example: Polynomials.
              Normalized Univariate Polynomials with Coefficents from an
              arbitrary Field are shown to be an Euclidean Domain with with
              Unique Factorization. Here Size is the degree of a polynomial;
              Quotient and Remainder are defined as expected for polynomials.
              This version uses quantifiers (defun-sk) and is non-exedutable.

fld-u-poly -- Directory containing books for Normalized Univariate Polynomials
              with Coefficents from an arbitrary Field

./fld-u-poly: -- ACL2 Books for Univariate Polynomials over a Field
certify.lsp
coe-fld.lisp                  -- Coefficients from a Field
fucongruencias-producto.lisp  -- Polynomial Product Congruences
fucongruencias-suma.lisp      -- Polynomial Sum Congruences
fuforma-normal.lisp           -- Normal Form for Polynomials
fumonomio.lisp                -- Monomials
fuopuesto.lisp                -- Polynomial Unary Minus
fupolinomio.lisp              -- (Unnormalized) Polynomials
fupolinomio-normalizado.lisp  -- Normalized Polynomials
fuproducto.lisp               -- Polynomial Products 
fuquot-rem.lisp               -- Polynomial Quotients and Remainders
fusuma.lisp                   -- Polynomial Sums
futermino.lisp                -- Terms
")
 (:PERMISSION 
"ACL2 Euclidean Domain books
Copyright (C) 2006 John R. Cowles and Ruben A. Gamboa,
University of Wyoming

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
