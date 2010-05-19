((:FILES ".:
COPYING
Makefile
PERFORMANCE
Readme.lsp
cert.acl2
log2.lisp
memory-impl.lisp
memory.lisp
memtree.lisp
package.lsp
private.lisp
timetest.lisp
")
(:TITLE "Memories: Array-like Records for ACL2")
(:AUTHOR/S "Jared Davis")
(:KEYWORDS "arrays, memories, records, linear address spaces")
(:ABSTRACT "We provide a library for modelling fixed-size arrays and
linear memories.  Our implementation provides fixnum-optimized O(log_2 n)
reads and writes from addresses 0, 1, \dots, n - 1.  Space is not allocated
until locations are used, so large address spaces can be represented.  We do
not use single-threaded objects or ACL2 arrays, which frees the user from
syntactic restrictions and slow-array warnings.  Finally, prove the same
hypothesis-free rewrite rules found in misc/records for efficient rewriting 
during theorem proving.")
(:PERMISSION 
  "Memories: Array-like Records for ACL2
Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>

This program is free software; you can redistribute it and/or 
modify it under the terms of the GNU General Public License as 
published by the Free Software Foundation; either version 2 of 
the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, 
but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
GNU General Public License for more details.

You should have received a copy of the GNU General Public 
License along with this program; if not, write to the Free 
Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
Boston, MA 02110-1301, USA.")
(:VERSION "0.31")
)


INCLUDING THE LIBRARY

  (include-book "data-structures/memories/memory" :dir :system)


DOCUMENTATION

  Documentation is available after loading the memory book.  In 
  particular, see :doc MEM::memory for a starting point.


PERFORMANCE

  The file PERFORMANCE includes a few performance results from my
  machine.  See also the file timetest.lisp to benchmark the library
  on your own system.


