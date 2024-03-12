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

(include-book "main-definition")
(include-book "instantiations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ poseidon
  :parents (acl2::projects)
  :short "The Poseidon hash function."
  :long
  (xdoc::topstring
   (xdoc::p
    "Poseidon is a framework for defining cryptographic hash functions
     that are designed to operate on elements of a large prime field in a
     way that is efficient in a zero-knowledge circuit.")
   (xdoc::p
    "Poseidon is described on "
    (xdoc::ahref "https://www.poseidon-hash.info" "this web site")
    ", which links to the research paper that defines the hash function;
     that paper refers to "
    (xdoc::ahref "https://eprint.iacr.org/2019/1107" "the HADES paper")
    ".")
   (xdoc::p
    "In this library we formalize the main parameterized Poseidon algorithm
     and formalize the parameters that instantiate the algorithm
     into a specific hash function.")
   (xdoc::p
    "Then we model a number of specific instantiations of Poseidon that
     are in use in the wild.")
   (xdoc::p
    "At this time we do not model the security checks that should be done
     on any new instantiation before using it in production.")))

; Explictly order the subtopics.
(xdoc::order-subtopics poseidon
  (poseidon-main-definition
   poseidon-instantiations))
