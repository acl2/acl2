; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "definition")
(include-book "correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft-stake2
  :parents (aleobft::aleobft)
  :short "Formal specification and correctness proofs of
          AleoBFT with dynamic committees with stake."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a formal model of an abstraction of the AleoBFT protocol
     that mainly captures the Bullshark aspects of the protocol,
     but with dynamic committees and with stake,
     which are significant extensions to Bullshark.
     The Narwhal aspects of AleoBFT
     are modeled only at an abstract level,
     similarly to the way the Bullshark papers model
     the underlying DAG consensus layer.
     The level of abstraction of this model
     is about the same as the Bullshark papers.
     This model does not capture garbage collection or syncing.")
   (xdoc::p
    "This is a slightly simplified version of
     the version in @(see aleobft-stake::aleobft-stake):
     see @(see aleobft::aleobft) for more details."))
  :order-subtopics (definition
                    correctness))
