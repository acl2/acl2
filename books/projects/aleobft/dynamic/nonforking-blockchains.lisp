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

(include-book "initialization")

(include-book "../library-extensions/lists-noforkp")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nonforking-blockchains
  :parents (correctness)
  :short "Invariant that blockchains do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each (correct) validator has its own view (i.e. copy) of the blockchain,
     but the protocol guarantees that these views are consistent:
     that is, the blockchains never fork.
     One may be a prefix of another at times,
     but they never evolve in different directions.
     This is perhaps the most important property of the protocol,
     namely that it does reach consensus on the blockchains.")
   (xdoc::p
    "Blockchains clearly do not fork in the initial state,
     because all blockchains are empty in the iniital state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk nonforking-blockchains-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two correct validators in the system,
          their blockchains do not fork."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (lists-noforkp
                    (validator-state->blockchain
                     (get-validator-state val1 systate))
                    (validator-state->blockchain
                     (get-validator-state val2 systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nonforking-blockchains-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  (implies (system-initp systate)
           (nonforking-blockchains-p systate))
  :enable (nonforking-blockchains-p
           system-initp
           system-validators-initp-necc))
