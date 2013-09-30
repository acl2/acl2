((:FILES "
.:
Makefile
Readme.lsp
top.lisp
leftist-tree-defuns.lisp
leftist-tree-defthms.lisp
leftist-tree-sort.lisp
leftist-tree-sort-equivalent.lisp
leftist-tree-sort-equivalent2.lisp
leftist-tree-sort-equivalent3.lisp
") ; a single string with files listed as with Unix command "-ls -1R"
 (:TITLE    "Implementation of Leftist Trees in ACL2")
 (:AUTHOR/S "Ben Selfridge")     ; non-empty list of author strings
 (:KEYWORDS
  "heap" "priority queue" "sort" "heapsort") ; non-empty list of keywords, case-insensitive
 (:ABSTRACT
  "An implementation of leftist trees as described in Purely
Functional Data Structures (Chris Okasaki, Cambridge University Press
1998). Leftist trees are an efficient implementation of binary heaps
well-suited to a functional language. In this book we provide an
implementation of the leftist heap data structure and its basic
operations, along with some basic theorems regarding invariance of
those operations, the rank vs. the size of the tree, and the
correctness of the associated heapsort algorithm. We prove that
heapsort is correct and equivalent to the isort algorithm provided in
the \"sorting\" book."
)
  (:PERMISSION ; author/s permission for distribution and copying:
"Leftist Trees Library for ACL2
Copyright (C) 2012 Ben Selfridge

This program is free software; you can redistribute it and/or modify
it under the terms of Version 2 of the GNU General Public License as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301, USA."))