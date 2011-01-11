; Book directory of GeNoC
; Supporting Material of paper 
; "Towards A Formal Theory of On Chip Communications in the ACL2 Logic
; Copyright (C) 2006  Julien Schmaltz,


; Structure of the books for GeNoC
; --------------------------------

;GeNoC-types 
;-----------
	
;This book defines the data types used in GeNoC: transactions, 
;missives, travels, etc. It contains basic functions used to manipulate
;these datatypes. 
;It does not import any book.

;GeNoC-misc
;----------
;This book imports GeNoC-types.
;This book contains miscellaneous definitions. For instance, it 
;defines predicates like CorrectRoutep, the filtering operator extrac-sublst,
;some lemmas about subsetp, etc.

;GeNoC-nodeset
;-------------
;This book contains functions about the definition and the validation 
;of the set of the existing nodes of a particular network. 
; It does not import any book.

;GeNoC-routing
;-------------
;This book imports GeNoC-nodeset and GeNoC-misc.
;It contains functions about the definition and the validation 
;of the routing algorithm. 

;GeNoC-scheduling
;----------------
;This book imports GeNoC-misc and GeNoC-nodeset.
;It contains functions about the scheduling policy of GeNoC. It
;also adds some lemmas used in the final proof. These lemmas link 
;functions like extract-sublst, missivesp, etc. They are about NodeSet
;and this is why we need the corresponding book.

;GeNoC-interfaces
;---------------
;This book contains functions about the definition and the validation
;of the interfaces. 
;It does not import any book.

;GeNoC
;-----
;This book imports the previous books. It contains the definition 
;of GeNoC and its proof of correctness. 

;Global Structure
;----------------

;	The global "book tree" is the following:
;
;                                 GeNoC
;			/         | 	          \ 
;       GeNoC-scheduling    GeNoC-routing       GeNoC-interfaces
;         |          |      |          | 	
; GeNoC-nodeset     GeNoC-misc     GeNoC-nodeset
;                       |
;                   GeNoC-types


((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
GeNoC-interfaces.lisp
GeNoC.lisp
GeNoC-misc.lisp
GeNoC-nodeset.lisp
GeNoC-routing.lisp
GeNoC-scheduling.lisp
GeNoC-types.lisp
Makefile
Readme.lsp
")
 (:TITLE    "Towards A Formal Theory of On Chip Communications in the ACL2 Logic")
 (:AUTHOR/S "Julien Schmaltz and Dominique Borrione") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "networks on chip" "formal theory")
 (:ABSTRACT "

GeNoC is a first step towards a formal theory of communication networks.
It is expressed in a general mathematical notation with many quantifiers, in
particular quantification over functions. We present here its expression
in the first order quantifier free logic of the ACL2 theorem prover.
We describe our systematic approach to cast it into ACL2, especially
how we use the encapsulation principle to obtain a systematic methodology
to specify and validate on chip communications architectures.
We summarize the different instances of GeNoC
developed so far in ACL2, some come from
industrial designs.We illustrate our approach on an XY routing algorithm.
")
  (:PERMISSION ; author/s permission for distribution and copying:
"GeNoC ACL2 Scripts
Copyright (C) 2006 Julien Schmaltz

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
