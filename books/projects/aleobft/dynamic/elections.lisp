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
     If all validators agree on the committee at that round
     (as we plan to prove as one of the key properties of the protocol),
     then they choose the same leader.
     Given this common leader, each validator uses
     the certificates at the immediately following odd round
     to carry out an election of that chosen leader:
     each certificate that references the leader certificate
     counts as a `yes' vote,
     while each certificate that references a different certificate
     counts as a `no' vote.
     If the validator has enough `yes' votes,
     which implies that it must have the leader certificate itself,
     which is called an `anchor', the validator commits that anchor,
     and potentially other precededing anchors,
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
     given a round number and a non-empty committee,
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
     we plan to prove in the near future."))

  (encapsulate
    (((leader-at-round * *) => *
      :formals (round commtt)
      :guard (and (posp round)
                  (committeep commtt)
                  (committee-nonemptyp commtt))))

    (local
     (defun leader-at-round (round commtt)
       (declare (ignore round))
       (set::head (committee->addresses commtt))))

    (defrule leader-in-committee
      (implies (committee-nonemptyp commtt)
               (committee-memberp (leader-at-round round commtt) commtt))
      :enable (committee-nonemptyp
               committee-memberp))

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
     This possible change of committee should be unproblematic
     for the purpose of the correctness of the protocol,
     but we ensure that by way of formal proofs.")
   (xdoc::p
    "We go through the voters, and check whether the leader address
     is among the refernced previous certificates or not,
     counting those as `yes' or `no' votes.
     We return both counts."))
  (b* (((when (set::emptyp voters)) (mv 0 0))
       (voter (set::head voters))
       ((mv yes-count no-count)
        (tally-leader-votes leader (set::tail voters))))
    (if (set::in leader (certificate->previous voter))
        (mv (1+ yes-count) no-count)
      (mv yes-count (1+ no-count))))
  :verify-guards :after-returns)
