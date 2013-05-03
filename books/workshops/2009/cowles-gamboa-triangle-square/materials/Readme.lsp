((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
 .:
 Readme.lsp
 tri-sq.lisp
 log2.lisp

")
(:TITLE    "Solving TRIANGLE = SQUARE")
(:AUTHOR/S "John R. Cowles"
           "Ruben Gamboa") 
(:KEYWORDS "triangular numbers" 
           "Pell's equation"
           "Log base 2"
           "Floor Log base 2"
           "Ceiling Log base 2")
(:ABSTRACT 
 "For positive integer n, the triangular number, Delta_n, is defined by
      Delta_n = 1 + 2 + ... + (n-1) + n
              = n * (n + 1) / 2.
  The first 6 triangular numbers are Delta_1 = 1, Delta_2 = 3,
  Delta_3 = 6, Delta_4 = 10, Delta_5 = 15, and Delta_6 = 21.

  Problem. Find triangular numbers that are also squares.
           That is, find positive integers, n and k, such that
                    n * (n + 1) / 2 = k^2
                  or
                    n * (n + 1) = 2 * k^2.

  Clearly Delta_1 = 1 is a square. Are there other square triangular numbers?
  Are there infinitely many square triangular numbers?  These questions are
  answered below and the answers are formally verfied using ACL2.
  
  Define functions that compute floor of log base 2 and
  ceiling log base 2 for nonnegative integers n.

  Show these functions are correct.
  Show these functions use logarithmic number, in input n, 
  of arithmetic operations to compute their results.") 
(:PERMISSION ; author/s permission for distribution and copying:
 "ACL2 book Solving TRIANGLE = SQUARE
  Copyright (C) 2008 John R. Cowles and Ruben Gamboa, University of Wyoming

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
  02110-1301, USA."))