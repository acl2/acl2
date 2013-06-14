((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
  "Readme.lsp"
  "certify.lsp"
  "r-no-cover.lisp"
  "s-no-cover1.lisp"
  "s-no-cover.lisp"
  "verifying-macros.lisp"
  )
 (:TITLE    "Verifying Sierpinski and Riesel Numbers in ACL2")
 (:AUTHOR/S "John R. Cowles" "Ruben Gamboa")
 (:KEYWORDS "Sierpinski numbers" "Riesel numbers")
 (:ABSTRACT "
A Sierpinski number is an odd positive integer, k, such that no
positive integer in this infinite list is prime:

  k 2^1 + 1, k  2^2 + 1, k 2^3 + 1, ..., k 2^n + 1, ... .

A Riesel number is similar to a Sierpinski number, with -1 replacing
+1 in the above infinite list. Such a number is an odd positive
integer, k, so that no positive integer in this infinite list is
prime:

  k 2^1 - 1, k 2^2 - 1, k 2^3 - 1, ..., k 2^n - 1, ... .

A cover, for such a k, is a finite list of positive integers such that
each integer, j, in the appropriate infinite list, has a factor, d, in
the cover, with 1 < d < j.

Given a k and its cover, ACL2 is used to systematically verify that
each integer, in the appropriate infinite list, has a smaller factor
in the cover.

For each individual k and cover, ACL2 events are generated that would
prove k is a Sierpinski or Riesel number, if all the events
succeed. If some of the events fail, then, as usual when using ACL2,
further study of the failure is required, in the hope of taking
corrective action.

The generation of these events is controlled by the macros
verify-sierpinski and verify-riesel.  These macros take three
arguments: the name of a witness function that will find a factor for
a given k 2^n +or- 1, the number k that is a Sierpinski or Riesel
number, and the cover for k.  The macros then generate an ACL2 proof.

There are a few odd positive integers, shown to be Sierpinski (or
Riesel) numbers, that have no known covers. Hand-crafted ACL2 proofs
have been constructed for these numbers.")
 (:PERMISSION
"Verifying Sierpinski and Riesel Numbers in ACL2
Copyright (C) 2011  University of Wyoming, Laramie, Wyoming

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
