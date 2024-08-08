; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "addresses")
(include-book "transactions")
(include-book "blocks")
(include-book "certificates")
(include-book "validator-states")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states
  :parents (definition)
  :short "States of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce fixtypes for the states, and their components,
     that the AleoBFT system may be in at any given time."))
  :order-subtopics (addresses
                    transactions
                    blocks
                    certificates
                    validator-states))
