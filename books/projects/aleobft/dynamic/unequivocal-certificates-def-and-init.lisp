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

(include-book "owned-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-certificates-def-and-init
  :parents (correctness)
  :short "Invariant that certificates are unequivocal:
          definition and establishment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each certificate in the system is uniquely identified
     by its author and round.
     In other words, no two distinct certificates
     have the same author and round.")
   (xdoc::p
    "This is clearly the case in the initial state,
     because there are no certificates at all.")
   (xdoc::p
    "The preservation of this invariant relies on another invariant,
     namely that blockchains do not fork.
     The reason is that, in order to prove certificate non-equivocation,
     we need the fact that different validators agree on
     the active committee at certain rounds;
     since the active committee is calculated from the blockchain,
     we need the fact that blockchains do not fork,
     so that they calculate the same committee
     (for their common blockchain prefixes).
     In turn, the non-forking of blockchains
     relies on the non-equivocation of certificates.
     So the preservation of the two invariants
     must be proved at the same time by induction,
     because we need a sufficiently strong induction hypothesis,
     with both invariants in the old state available,
     from which we can prove that both invariants
     also hold on the new state.")
   (xdoc::p
    "Here we define the invariant about unequivocal certificates,
     and we also prove that it holds in the initial state.
     Elsewhere we do the same for
     the invariant about non-forking blockchains,
     i.e. we define it and prove it holds in the initial state.
     Then we prove that each holds in the new state
     if both hold in the old state,
     and finally we put everything together
     in an induction proof for both invariants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of certificates owned by each correct validator
          is unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick an arbitrary correct validator
     for getting the set of certificates in the system.
     The choice does not matter, because of the already proved invariant that
     all correct validators have the same certificates:
     see @(see same-owned-certificates)."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (certificate-set-unequivocalp
                    (certificates-owned-by val systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-certificates-p-when-init
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  (implies (system-initp systate)
           (unequivocal-certificates-p systate))
  :enable (unequivocal-certificates-p
           certificates-owned-by-when-init
           certificate-set-unequivocalp-when-emptyp))
