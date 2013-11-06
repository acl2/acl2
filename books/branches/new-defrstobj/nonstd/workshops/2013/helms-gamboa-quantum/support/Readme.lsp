((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
  "Readme.lisp"
  "quantum.lisp"
)
(:TITLE    "An Interpreter for Quantum Circuits")
(:AUTHOR/S "Lucas Helms"
           "Ruben Gamboa") 
(:KEYWORDS "Quantum circuits"
	   "Evaluators"
           "ACL2(r)")
(:ABSTRACT 
 "This paper describes an ACL2 interpreter for ``netlists'' describing
quantum circuits.  Several quantum gates are implemented, including
the Hadamard gate H, which rotates vectors by 45 degrees, necessitating
the use of irrational numbers, at least at the logical level.  Quantum
measurement presents an especially difficult challenge, because it
requires precise comparisons of irrational numbers and the use of random
numbers.  This paper does not address computation with irrational numbers
or the generation of random numbers, although future work includes the
development of pseudo-random generators for ACL2.

") 
(:PERMISSION ; author/s permission for distribution and copying:
 "ACL2 book Quantum Circuits in ACL2(r)
  Copyright (C) 2011 Lucas Helms and Ruben Gamboa, University of Wyoming

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
  "These files are intended for use with ACL2(r), not ACL2.")
)
