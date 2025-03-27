; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "initialization")

(include-book "../library-extensions/lists-noforkp")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nonforking-blockchains-def-and-init
  :parents (correctness)
  :short "Invariant that blockchains do not fork:
          definition and establishment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each (correct) validator has its own view (i.e. copy) of the blockchain,
     but the protocol guarantees that these views are consistent:
     that is, the blockchains never fork.
     One may be a prefix of another at times,
     but they never evolve in different directions.
     This is the most important property of the protocol,
     namely that, being a consensus protocol for a blockchain,
     it does indeed reach consensus on the blockchains.")
   (xdoc::p
    "Blockchains clearly do not fork in the initial state,
     because all blockchains are empty in the iniital state.")
   (xdoc::p
    "The preservation of this invariant relies on another invariant,
     namely that DAGs are unequivocal across validators.
     This is defined in @(see unequivocal-dags-def-and-init),
     where it is also explained how that and this invariant
     are inter-dependent and must be proved together in the induction.")
   (xdoc::p
    "Similarly to @(see unequivocal-dags-def-and-init),
     here we define the invariant,
     and we also prove that it holds in the initial states."))
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
                     (get-validator-state val2 systate)))))
  ///
  (fty::deffixequiv-sk nonforking-blockchains-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nonforking-blockchains-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the blockchains are the same (both empty),
     so they clearly do not fork.
     The proof does not even depend on their emptiness,
     just their equality, since both validators' states
     is @(tsee validator-init)."))
  (implies (system-initp systate)
           (nonforking-blockchains-p systate))
  :enable (nonforking-blockchains-p
           system-initp
           system-validators-initp-necc))
