; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-faults-and-quora")
(include-book "operations-leaders")
(include-book "operations-author-round-pairs")
(include-book "operations-previous-certificates")
(include-book "operations-message-creation")
(include-book "operations-voting")
(include-book "operations-dags")
(include-book "operations-blockchain")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (definition)
  :short "Operations on system states and their components."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operations are used to define the state transitions of the system,
     as well as to formulate and prove the correctness of the system.
     A few of these operations may not actually be used
     to define the state transiitons of the system,
     but they are similar to ones that are used for that,
     and thus it makes sense to group them together.")
   (xdoc::p
    "Additional operations that are only used
     to formulate and prove correctness
     are in @(see operations-additional)."))
  :order-subtopics (operations-faults-and-quora
                    operations-leaders
                    operations-author-round-pairs
                    operations-previous-certificates
                    operations-message-creation
                    operations-voting
                    operations-dags
                    operations-blockchain))
