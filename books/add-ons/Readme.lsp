((:files
"
.:
Makefile
Readme.lsp
hash-stobjs.acl2
hash-stobjs.cert
hash-stobjs.lisp")
 (:abstract "This directory contains books which add system-level functionality
to ACL2.  These books should be considered experimental, potentially buggy and
unsound.

hash-stobjs.lisp allows stobjs to be defined with hash table members.  Three
types of hash table are supported: EQ, EQL, and HONS-EQUAL.  Such a stobj
member is declared within the DEFSTOBJ form as follows:

 (<name> :type (hash-table <hash-table-type>))

EQ hash tables require keys to be symbols.  EQL hash tables require keys to be
EQLABLEP (number, symbol, or character.)  HONS-EQUAL hash tables are only
available if ACL2 is built with the HONS feature.  They place no requirement on
the keys, but each key is HONS-COPYed before use, so in order for lookups  to
be fast the keys should always be HONSes or atoms.

Questions about hash-stobjs.lisp to Sol Swords <sswords@cs.utexas.edu>.")
(:PERMISSION
  "This program is free software; you can redistribute it and/or 
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
