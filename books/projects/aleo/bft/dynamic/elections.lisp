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
     which we prove they will do in @(see same-committees),
     then they will choose the same leader.
     Given this common leader, each validator uses
     the certificates they receive in the immediately following odd round
     to carry out an election of that chosen leader:
     each following odd-round certificate that references the leader certificate
     counts as a `yes' vote,
     while each following odd-round certificate 
     that does not reference the leader certificate counts as a `no' vote.
     If a validator has the leader certificate and has enough `yes' votes,
     that certificate becomes an anchor (see @(see anchors)).
     The validator commits that anchor,
     and potentially other preceding anchors,
     by generating blocks from them;
     but this is formalized elsewhere.")
   (xdoc::p
    "Here we formalize the choice of the leader,
     via a constrained function on committees and round numbers.
     We also formalize the counting of the `yes' and `no' votes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection leader-at-round
  :short "Leader at a round, given a committee active at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a constrained function that,
     given a round number and a committee,
     returns an address in the committee.
     This is the chosen leader at that round.")
   (xdoc::p
    "An AleoBFT implementation may, for example,
     hash the round number, reduce it modulo the number of validators,
     and pick the validator corresponding to that index
     according to some ordering of the validators in the committee.
     But in our model we can just use a constrained function,
     as the details do not matter,
     at least for the kind of properties that
     we are proving in the near future."))

  (encapsulate
    (((leader-at-round * *) => *
      :formals (round commtt)
      :guard (and (posp round)
                  (committeep commtt))))

    (local
     (defun leader-at-round (round commtt)
       (declare (ignore round))
       (address-fix (set::head (committee-members commtt)))))

    (defrule addressp-of-leader-at-round
      (addressp (leader-at-round round commtt)))

    (defrule leader-in-committee
      (set::in (leader-at-round round commtt) (committee-members commtt))
      :enable not-emptyp-of-committee-members)

    (defrule leader-at-round-of-pos-fix
      (equal (leader-at-round (pos-fix round) commtt)
             (leader-at-round round commtt)))

    (defrule leader-at-round-of-committee-fix
      (equal (leader-at-round round (committee-fix commtt))
             (leader-at-round round commtt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tally-leader-votes ((leader addressp) (voters certificate-setp))
  :returns (mv (yes-count natp) (no-count natp))
  :short "Count the `yes' and `no' votes for a leader."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('leader') input to this function
     is the address of the leader at some even round,
     as returned by @(tsee leader-at-round).
     The @('voters') input to this function
     is the set of all the certificates in the DAG
     who are members of the committee active
     at the immediately following odd round:
     these are all the voters for the leader.
     Note that the active committee may have changed
     between the even and odd round,
     if it changed between the two rounds
     exactly at the @(tsee lookback) distance.
     This possible change of committee is unproblematic
     for the purpose of the correctness of the protocol,
     as we ensure by way of formal proofs.")
   (xdoc::p
    "We go through the voters, and for each voter check whether the given leader
     authored one of the certificates referenced in the voter certificate,
     counting `yes' or `no' votes, respectively.
     We return both counts."))
  (b* (((when (set::emptyp voters)) (mv 0 0))
       (voter (set::head voters))
       ((mv yes-count no-count)
        (tally-leader-votes leader (set::tail voters))))
    (if (set::in leader (certificate->previous voter))
        (mv (1+ yes-count) no-count)
      (mv yes-count (1+ no-count))))
  :verify-guards :after-returns)
