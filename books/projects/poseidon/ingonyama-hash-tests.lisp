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

(include-book "ingonyama-hash")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests
; Checked against the Ingonyama Python implementation.
; See ingonyama-zk/poseidon-hash/tests/test_hash.py

(assert-equal
 (ingonyama-bn-254-hash '(0 1 2))
 #x0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29)

(assert-equal
 (ingonyama-bls-255-hash '(0 1 2 3 4))
 #x65ebf8671739eeb11fb217f2d5c5bf4a0c3f210e3f3cd3b08b5db75675d797f7)

(assert-equal
 (let* ((domain-tag (* 3 (expt 2 64)))
        (input (cons domain-tag '(0 1 2))))
   (ingonyama-bls-255-neptune-hash input))
 ;; The output of this test is not explicitly mentioned in
 ;; ingonyama-zk/poseidon-hash/tests/test_hash.py
 ;; but a print statement added to the python code reveals it as
 1044691594892685450723242434923330054196099624959797426495238441401678067797)
