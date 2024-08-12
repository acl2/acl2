; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "definition")
(include-book "correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft-static
  :parents (aleo::aleobft)
  :short "Formal specification and correctness proofs of
          AleoBFT with static committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a formal model of an abstraction of the AleoBFT protocol
     that mainly captures the Bullshark aspects of the protocol,
     without dynamic committees (i.e. with static committees).
     The Narwhal aspects of AleoBFT
     are modeled only at an abstract level,
     similarly to the way the Bullshark papers model
     the underlying DAG consensus layer.
     The level of abstraction of this model
     is about the same as the Bullshark papers.
     This model does not capture garbage collection or syncing.
     It also does not capture stake, but only numbers of validators
     (i.e. every validator has the same stake).")
   (xdoc::p
    "Although this is more of a model of Bullshark than AleoBFT,
     due to the lack of dynamic committees,
     this model is useful as a baseline,
     because a fixed committee is a special case of dynamic committees
     (a flaw with fixed committees
     would be also a flaw with dynamic committees).
     Furthermore, this model is useful as a starting point
     for developing the more complex model with dynamic committees.
     Note also that, although the substance of AleoBFT is similar to Bullshark,
     there are certain differences between the two protocols,
     particularly in the details of leader election.")
   (xdoc::p
    "Besides defining the formal model.
     we formally prove correctness properties of it,
     most prominently the non-forking of blockchains."))
  :order-subtopics (definition
                    correctness))
