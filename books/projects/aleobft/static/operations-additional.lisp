; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-fault-tolerance")
(include-book "operations-certificates-for-validators")
(include-book "operations-unequivocal-certificates")
(include-book "operations-anchors")
(include-book "operations-dags-additional")
(include-book "operations-blockchain-additional")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-additional
  :parents (correctness)
  :short "Additional operations on system states and their components."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operations are used
     to formulate and prove the correctness of the system,
     along with the ones defined in @(see operations).
     Unlike the latter, these operations are not used
     to define the state transitions of the system;
     this is why they are grouped separately."))
  :order-subtopics (operations-fault-tolerance
                    operations-certificates-for-validators
                    operations-unequivocal-certificates
                    operations-anchors
                    operations-dags-additional))
