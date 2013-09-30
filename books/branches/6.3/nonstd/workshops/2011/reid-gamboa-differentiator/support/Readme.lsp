((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
  "Readme.lisp"
  "abs-derivative.lisp"
  "certify.lsp"
  "chain-composition.lisp"
  "composition-elem.lisp"
  "composition-helpers.lisp"
  "defderivative.lisp"
  "differentiator.lisp"
  "exp-minimal.lisp"
  "exp-properties.lisp"
  "inverse-composition.lisp"
  "inverse-derivative.lisp"
  "inverse-square.lisp"
  "inverse-trig-derivatives.lisp"
  "inverse-trig-ex.lisp"
  "ln-derivative-real.lisp"
  "nsa-ex.lisp"
  "product-composition.lisp"
  "sin-cos-minimal.lisp"
  "sqrt-derivative.lisp"
  "sum-composition.lisp"
)
(:TITLE    "Implementing an Automatic Differentiator in ACL2")
(:AUTHOR/S "Peter Reid"
           "Ruben Gamboa") 
(:KEYWORDS "automatic differentiation"
	   "differentiation rules"
           "ACL2(r)")
(:ABSTRACT 
 "The foundational theory of differentiation was developed as
part of the original release of ACL2(r). In work reported at
the last ACL2 Workshop, we presented theorems justifying the
usual differentiation rules, including the chain rule and the
derivative of inverse functions. However, the process of
applying these theorems to formalize the derivative of a
particular function is completely manual.  More recently, we
developed a macro and supporting functions that can automate
this process.  This macro uses the ACL2 table facility to
keep track of functions and their derivatives, and it also
interacts with the macro that introduces inverse functions in
ACL2(r), so that their derivatives can also be automated. In
this paper, we present the implementation of this macro and
related functions.
") 
(:PERMISSION ; author/s permission for distribution and copying:
 "ACL2 book Inverse Functions in ACL2(r)
  Copyright (C) 2011 Peter Reid, University of Oklahoma, 
  and Ruben Gamboa, University of Wyoming

  This book is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This book is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this book; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
  02110-1301, USA.")
(:NOTE
  "These files are intended for use with ACL2(r), not ACL2.
   Not included in this directory are other files related
   to this project (e.g., the proof that d e^x/dx = e^x).
   We selected these files because they represent the smallest
   subset of files that demonstratre various pieces of the project.")
)
