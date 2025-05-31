; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "definition")
(include-book "correctness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleobft-definition-and-correctness
  :parents (aleobft)
  :short "Formal specification and correctness proofs of
          AleoBFT with dynamic committees with stake and proposals."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a formal model of an abstraction of the AleoBFT protocol
     that captures both the Narwhal and the Bullshark aspects of the protocol,
     but with dynamic committees and with stake,
     which are a significant extensions.
     This model does not capture garbage collection or syncing.")
   (xdoc::p
    "This is work in progress:
     the definition of the system is complete,
     but the correctness proofs are not here yet."))
  :order-subtopics (definition
                    correctness))
