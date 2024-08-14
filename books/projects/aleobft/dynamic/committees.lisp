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

(include-book "addresses")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committees
  :parents (states)
  :short "Committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "Dynamic committees are one of the most distinctive features of AleoBFT.
     Starting with a genesis (i.e. initial) committee,
     validators join and leave the committe, by bonding and unbonding,
     which happens via transactions in the blockchain.
     Since every validator has its own view of the blockchain,
     it also has its own view of how the committees evolves.
     The agreement on the blockchains of the validators
     should also provide an agreement on how the committee evolves;
     this is what we are in the progress of formally proving.")
   (xdoc::p
    "The genesis committee is arbitrary,
     but fixed for each execution of the protocol.
     Thus, we model the genesis committee via a constrained nullary function
     that returns the set of addresses of the genesis committee.
     The genesis committee is globally known to all validators.")
   (xdoc::p
    "Each validator's view of the evolution of the committee
     is formalized via functions that operate on the blockchain,
     and that, starting with the genesis committee,
     calculate the committee at every block,
     by taking into considerations bonding and unbonding transactions.
     Blocks are produced at, and are associated with,
     (a subset of the) even rounds of the DAG.
     The notion of interest is that of the committee at a round,
     but this actually specializes into two notions,
     because of the committee lookback approach of AleoBFT.")
   (xdoc::p
    "One notion is that of the committee bonded at each round,
     i.e. the committee resulting from applying
     all the bonding and unbonding transactions up to that round
     to the genesis committee in order.
     That is, this is the committeed bonded at each round.
     There are actually two possible choices for defining this notion precisely,
     based on whether the committee bonded at an even round that has a block
     includes or excludes the transactions in that block.
     That is, do we consider the committee resulting at the end of that block
     to be the committee at that even round, or at the odd round that follows?
     The exact choice might affect the correctness properties,
     so we will need to be careful about the choice.")
   (xdoc::p
    "The other notion is that of the committee active at each round,
     i.e. the committee that is in charge of that round.
     This is the lookback committee: it is the bonded committee
     at a fixed number of previous rounds (``lookback'').
     The choice of when a bonded committee starts vs. ends discussed above
     affects the choice of when an active committee starts vs. ends,
     and that is what most directly may affect the correctness properties.")
   (xdoc::p
    "Here we define both notions, of bonded and active committee.
     We might need to revise them slightly
     as we investigate the correctness properties."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection genesis-committee
  :short "Genesis committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see committees),
     there is an arbitrary but fixed genesis committee,
     which we capture via a constrained nullary function.
     We require the function to return a non-empty set of addresses."))

  (encapsulate
      (((genesis-committee) => *))

    (local
     (defun genesis-committee ()
       (set::insert (address nil) nil)))

    (defrule address-setp-of-genesis-committee
      (address-setp (genesis-committee)))

    (defrule not-emptyp-of-genesis-committee
      (not (set::emptyp (genesis-committee))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
