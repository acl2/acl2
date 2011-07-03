; Rev.: March 2009

((:FILES "
.:
Makefile
Readme.lsp
generic-modules/
instantiations/

./generic-modules:
interfaces-computes.lisp
GeNoC-departure.lisp
GeNoC-interfaces.lisp
GeNoC-misc.lisp
GeNoC-nodeset.lisp
GeNoC-ntkstate.lisp
GeNoC-priority.lisp
GeNoC-routing.lisp
GeNoC-scheduling.lisp
GeNoC-simulation.lisp
GeNoC-synchronization.lisp
GeNoC-types.lisp
GeNoC.lisp
Makefile
own-perm.lisp

./instantiations:
Makefile
departure/
genoc/
interfaces/
nodeset/
ntkstate/
routing/
scheduling/
simulation/
synchronization/

./instantiations/departure:
Makefile
simple/

./instantiations/departure/simple:
Makefile
simple-R4D.lisp

./instantiations/genoc:
Makefile
simple-ct-global/

./instantiations/genoc/simple-ct-global:
Makefile
sets.lisp
simple.lisp
trlst-equal.lisp

./instantiations/interfaces:
Makefile
dummy-interfaces/

./instantiations/interfaces/dummy-interfaces:
Makefile
interfaces-computes.lisp

./instantiations/nodeset:
2DMesh-no-ports/
Makefile

./instantiations/nodeset/2DMesh-no-ports:
2DMesh.lisp
Makefile

./instantiations/ntkstate:
Makefile
simple/

./instantiations/ntkstate/simple:
Makefile
simple.lisp

./instantiations/routing:
Makefile
XY/

./instantiations/routing/XY:
Makefile
XYRouting.lisp

./instantiations/scheduling:
Makefile
circuit-switching-global/

./instantiations/scheduling/circuit-switching-global:
Makefile
circuit.lisp
intersect.lisp

./instantiations/simulation:
Makefile
simple/

./instantiations/simulation/simple:
Makefile
simple.lisp

./instantiations/synchronization:
Makefile
circuit-global/

./instantiations/synchronization/circuit-global:
Makefile
circuit.lisp
"
)
 (:TITLE    "Formal Validation of Deadlock Prevention in Networks-on-Chips")
 (:AUTHOR/S "Freek Verbeek" "Julien Schmaltz") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "liveness" "networks-on-chips" "formal methods"
   )
 (:ABSTRACT
"Complex systems-on-chips (SoCs) are built as the assembly of pre-designed 
  parameterized components.
  The specification and validation of the communication infrastructure 
  becomes a crucial step in the early phase of any SoC design.
  The Generic Network-on-Chip model (GeNoC) has been recently 
  proposed as a generic specification environment, 
  restricted to safety properties.
  We report on an initial extension of the GeNoC
  model with 
  a generic termination condition and a generic property 
  showing the prevention of livelock and deadlock.
  The latter shows that all messages injected in the 
  network eventually reach their 
  destination for all possible values of network
  parameters like topology, size of the network, 
  message length or injection time.
  We illustrate our initial results with the validation 
  of a circuit switching technique.
")
 (:PERMISSION ; author/s permission for distribution and copying:
"Deadlock Prevention in Networks-on-Chips
Copyright (C) 2009 F. Verbeek and J. Schmaltz

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

