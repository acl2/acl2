; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "definition")
(include-book "correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft-dynamic
  :parents (aleobft::aleobft)
  :short "Formal specification and correctness proofs of
          AleoBFT with dynamic committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a formal model of an abstraction of the AleoBFT protocol
     that mainly captures the Bullshark aspects of the protocol,
     but with dynamic committees,
     which is a significant extension to Bullshark.
     The Narwhal aspects of AleoBFT
     are modeled only at an abstract level,
     similarly to the way the Bullshark papers model
     the underlying DAG consensus layer.
     The level of abstraction of this model
     is about the same as the Bullshark papers.
     This model does not capture garbage collection or syncing.
     It also does not capture stake,
     but it does model an arbitrarily changing number
     of validators where every validator has the same stake."))
  :order-subtopics (definition
                    correctness))
