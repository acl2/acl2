; Poseidon Library
;
; Copyright (C) 2024 Eric McCarthy (bendyarm on GitHub)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "POSEIDON")

(include-book "rate-2-alpha-17")
(include-book "rate-4-alpha-17")
(include-book "rate-8-alpha-17")
(acl2::merge-io-pairs
 dm::primep
 (include-book "ingonyama-hash"))

(defxdoc+ poseidon-instantiations
  :parents (poseidon)
  :short "Instantiations of Poseidon hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "To use Poseidon hash, "
    (xdoc::seetopic "param" "the parameters")
    " must be given explicit values.
     Here we describe some specific instantiations
     that are in use in other projects."))
  :order-subtopics t) ; orders by the include-book forms above
