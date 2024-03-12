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

(include-book "rate-2-alpha-17")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests

; For `hash` with parameters.

(assert-equal
 (hash (list (rate-2-domain-fe) 0) (rate-2-alpha-17-parameters) 1)
 '(890528275010128413086262374581080260861073041656622537351850370623612770892))

(assert-equal
 (hash (list (rate-2-domain-fe) 1 0) (rate-2-alpha-17-parameters) 1)
 '(5628341397010129094749668483581880102727432924493934736184943293239516955115))

(assert-equal
 (hash (list (rate-2-domain-fe) 1 1) (rate-2-alpha-17-parameters) 1)
 '(8157139884333238590486942177518291201805404831318752263970723012511043776504))

(assert-equal
 (hash (list (rate-2-domain-fe) 2 0 1) (rate-2-alpha-17-parameters) 1)
 '(1264503312579512465189393860390753485466098990459556420139454725533509612591))

(assert-equal
 (hash (list (rate-2-domain-fe) 2 7 6) (rate-2-alpha-17-parameters) 1)
 '(610307558855046745962283397484544098131504333994299967172265018394298942553))

; For hash2.
; These have been checked against the snarkVM console Rust implementation.

(assert-equal
 (hash2 '())
 890528275010128413086262374581080260861073041656622537351850370623612770892)

(assert-equal
 (hash2 '(0))
 5628341397010129094749668483581880102727432924493934736184943293239516955115)

(assert-equal
 (hash2 '(1))
 8157139884333238590486942177518291201805404831318752263970723012511043776504)

(assert-equal
 (hash2 '(0 1))
 1264503312579512465189393860390753485466098990459556420139454725533509612591)

(assert-equal
 (hash2 '(7 6))
 610307558855046745962283397484544098131504333994299967172265018394298942553)
