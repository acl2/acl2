; Poseidon Library
;
;    Copyright 2024 Provable Inc.
;
;    Licensed under the Apache License, Version 2.0 (the "License");
;    you may not use this file except in compliance with the License.
;    You may obtain a copy of the License at
;
;      http://www.apache.org/licenses/LICENSE-2.0
;
;    Unless required by applicable law or agreed to in writing, software
;    distributed under the License is distributed on an "AS IS" BASIS,
;    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;    See the License for the specific language governing permissions and
;    limitations under the License.

; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "POSEIDON")

(include-book "poseidon")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ poseidon
  :parents (acl2::projects)
  :short "The Poseidon hash function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Poseidon is described on "
    (xdoc::ahref "https://www.poseidon-hash.info" "this web site")
    ", which links to the research paper that defines the hash function;
     that paper refers to "
    (xdoc::ahref "https://eprint.iacr.org/2019/1107" "the HADES paper")
    ".")
   (xdoc::p
    "Poseidon is parameterized over a number of aspects,
     such as the round constants, the MDS matrix, etc.
     We capture all these parameters in the @(tsee param) data structure,
     which also includes parameters for aspects that
     are not explicitly described in the Poseidon paper
     but that nevertheless need to be made precise in the definition.
     Perhaps these latter aspects are disambiguated
     by the reference implementation of Poseidon
     (which is also linked from the aforementioned web site),
     but it stil makes mathematical sense to parameterize the definition
     over those aspects.
     These are all described in detail in @(tsee param).
     The top-level functions of our specification of Poseidon
     take a @(tsee param) as an input.")
   (xdoc::p
    "Poseidon uses a sponge construction, which is a more general concept.
     In a sponge construction,
     one can absorb any number of elements,
     squeeze any number of elements,
     and again absorb more elements and then squeeze them,
     and so on.
     We formalize this by explicating the state of the sponge in @(tsee sponge),
     which consists of not only the current vector of elements,
     but also an index within the vector
     where elements are absorbed or squeezed next,
     and an indication of whether we are absorbing or squeezing;
     this is described in more detail in @(tsee sponge).
     We define functions @(tsee absorb) and @(tsee squeeze)
     to absorb and squeeze elements,
     which take as input and return as output a sponge state,
     besides the other natural inputs and outputs.
     This is similar to some existing implementations of Poseidon.")
   (xdoc::p
    "The aforementioned @(tsee absorb) and @(tsee squeeze) functions
     take or return multiple input or output elements.
     If these functions were defined ``directly'',
     they would be somewhat complicated because of the need to handle
     a number of inputs or outputs that will start from the current index
     and that may require one or more permutations and index wrap-arounds.
     This is especially the case because, as described in @(tsee param),
     we support several different ways to absorb and squeeze elements.
     To keep things simpler,
     we define functions @(tsee absorb1) and @(tsee squeeze1)
     that absorb or squeeze a single input or output element:
     these are much simpler to define and understand,
     even with the several different ways to absorb and squeeze elements.
     Then we define @(tsee absorb) and @(tsee squeeze)
     by simply iterating @(tsee absorb1) and @(tsee squeeze1).")
   (xdoc::p
    "At the very top level, we define a function @(tsee hash)
     that maps any number of inputs to any number of outputs.
     This is defined by internally creating and using a sponge state.
     Note that there is no need to include any explicit notion of padding,
     which can be performed externally to Poseidon proper as defined here."))
  :order-subtopics t
  :default-parent t)
