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

(include-book "committees")
(include-book "certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ elections
  :parents (transitions)
  :short "Leader elections."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each even round has a deterministically chosen leader
     among the validators that form the active committee at that round.
     If all validators agree on the committee at that round,
     which we prove elsewhere,
     then they choose the same leader.
     Given this common leader, each validator uses
     the certificates at the immediately following odd round
     to carry out an election of that chosen leader:
     each certificate that references the leader certificate
     adds its stake to the `yes' vote,
     while each certificate that references a different certificate
     adds its stake to the `no' vote.
     Thus these `yes' and `no' votes are amounts of stake.
     If the validator has enough `yes' vote stake,
     which implies that it must have the leader certificate itself,
     which is called an `anchor',
     then the validator commits that anchor,
     and potentially other precededing anchors,
     generating blocks from them;
     this is formalized elsewhere.")
   (xdoc::p
    "Here we formalize the choice of the leader,
     via a constrained function on committees and round numbers.
     We also formalize the counting of the voting stake."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection leader-at-round
  :short "Leader at a round, given a committee active at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained function that,
     given a round number and a non-empty committee,
     returns an address in the committee.
     This is the chosen leader at that round.")
   (xdoc::p
    "In AleoBFT, this calculation is deterministic,
     given the round number and committee,
     but the details are unimportant to our model.
     Thus, the use of a constrained function is appropriate."))

  (encapsulate
    (((leader-at-round * *) => *
      :formals (round commtt)
      :guard (and (posp round)
                  (committeep commtt)
                  (committee-nonemptyp commtt))))

    (local
     (defun leader-at-round (round commtt)
       (declare (ignore round))
       (address-fix (set::head (committee-members commtt)))))

    (defrule addressp-of-leader-at-round
      (addressp (leader-at-round round commtt)))

    (defrule leader-in-committee
      (implies (committee-nonemptyp commtt)
               (set::in (leader-at-round round commtt)
                        (committee-members commtt)))
      :enable committee-nonemptyp)

    (defrule leader-at-round-of-pos-fix
      (equal (leader-at-round (pos-fix round) commtt)
             (leader-at-round round commtt)))

    (defrule leader-at-round-of-committee-fix
      (equal (leader-at-round round (committee-fix commtt))
             (leader-at-round round commtt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leader-stake-votes ((leader addressp)
                            (voters certificate-setp)
                            (commtt committeep))
  :returns (yes-stake natp)
  :short "Count the stake votes for a leader."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('leader') input to this function
     is the address of the leader at some even round,
     as returned by @(tsee leader-at-round).
     The @('voters') input to this function
     is the set of all the certificates in the DAG
     whose authors should be members of the committee active
     at the immediately following odd round:
     these are all the possible voters for the leader.
     The @('commtt') input to this function
     is the active committee at the odd round
     just after the even round of the leader.")
   (xdoc::p
    "We do not require, in the guard,
     that the voter certificates are all at the same round
     and that they are authored by members of the committee.
     This is for simplicity, and also because,
     when this function is used,
     we do not have, readily available, the condition that
     the voter certificate authors are members of the committee;
     that is an invariant that is proved elsewhere.")
   (xdoc::p
    "Note that the active committee may have changed
     between the even and odd round,
     if it changed between the two rounds
     exactly at the @(tsee lookback) distance.
     This possible change of committee is unproblematic
     for the purpose of the correctness of the protocol,
     as we ensure by way of formal proofs.
     This is why we use @(tsee committee-validator-stake)
     instead of @(tsee committee-member-stake).")
   (xdoc::p
    "We go through the voters, and check whether the leader address
     is among the referenced previous certificates or not,
     counting its stake as part of the resulting vote stake."))
  (b* (((when (set::emptyp (certificate-set-fix voters))) 0)
       (voter (set::head voters))
       (voter-stake
        (committee-validator-stake (certificate->author voter) commtt))
       (yes-stake (leader-stake-votes leader (set::tail voters) commtt)))
    (if (set::in (address-fix leader)
                 (certificate->previous voter))
        (+ voter-stake yes-stake)
      yes-stake))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :hooks (:fix))
