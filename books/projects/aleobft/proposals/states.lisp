; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "addresses")
(include-book "transactions")
(include-book "blocks")
(include-book "proposals")
(include-book "certificates")
(include-book "validator-states")
(include-book "messages")
(include-book "system-states")
(include-book "committees")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ states
  :parents (definition)
  :short "States of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce fixtypes for the states, and their components,
     that the AleoBFT system may be in at any given time.
     Along with the fixtypes, we also introduce some operations on them.")
   (xdoc::p
    "Although committees are not an explicit component of states,
     it is, in a way, an implicit component,
     since it is calculated from blockchains.
     So we include committees under states as well."))
  :order-subtopics (addresses
                    transactions
                    blocks
                    proposals
                    certificates
                    validator-states
                    messages
                    system-states
                    committees))
