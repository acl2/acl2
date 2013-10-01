((:FILES "
.:
Makefile
Readme.lsp
generic-modules
instantiations

./generic-modules:
GeNoC-interfaces.lisp
GeNoC-misc.lisp
GeNoC-nodeset.lisp
GeNoC-routing.lisp
GeNoC-scheduling.lisp
GeNoC-types.lisp
GeNoC.lisp
Makefile
readme

./instantiations:
Makefile
interfaces
nodeset
routing
scheduling

./instantiations/interfaces:
Makefile
bi-phi-m.lisp

./instantiations/nodeset:
2D-mesh-nodeset.lisp
Makefile
octagon-nodeset.lisp

./instantiations/routing:
Makefile
doubleY-routing
octagon-routing
xy-routing

./instantiations/routing/doubleY-routing:
Makefile
doubleY-routing.lisp

./instantiations/routing/octagon-routing:
Makefile
getting_rid_of_mod.lisp
mod_lemmas.lisp
routing_defuns.lisp
routing_local_lemmas.lisp
routing_main.lisp

./instantiations/routing/xy-routing:
Makefile
xy-routing.lisp

./instantiations/scheduling:
Makefile
circuit-scheduling.lisp
intersect.lisp
packet-scheduling.lisp

"
)
 (:TITLE    "GeNoC: A Generic Network On Chip")
 (:AUTHOR/S "J. Schmaltz") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "networks on chip" "formal methods" "system design"
   )
 (:ABSTRACT
"GeNoC is a generic network model intended to serve as a reference for
the validation of high-level descriptions of networks on chip (NoCs). It formalizes
the interaction between three key components: interfaces, routing algorithms,
and scheduling policies. It also defines a global correctness property: messages reach their expected destination
without modification of their content. To abstract from particular implementations, 
GeNoC's components are not explicitly defined. They are constrained to satisfy a 
set of properties. Using encapsulation and functional-instantiation, the constrained
for particular components of a given NoC are automatically generated. Their proof is sufficient 
to guarantee the overall correctness of this given NoC.
")
 (:PERMISSION ; author/s permission for distribution and copying:
"GeNoC v1.0
Copyright (C) 2007 J. Schmaltz

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
