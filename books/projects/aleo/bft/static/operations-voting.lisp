; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-voting
  :parents (operations)
  :short "Operations about voting."
  :long
  (xdoc::topstring
   (xdoc::p
    "A crucial aspect of AleoBFT is the voting or non-voting
     of certificate leaders (anchors).
     Here we define operations to tally the votes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tally-leader-votes ((leader addressp) (voters certificate-setp))
  :returns (mv (yes-count natp) (no-count natp))
  :short "Count the votes and non-votes for the leader."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('leader') input to this function
     is the address of the leader at some even round.
     The @('voters') input to this function
     is the set of all certificates in the DAG
     in the immediately following odd round:
     these are all the voters for the leader.
     Each edge to the leader's certificate (in the preceding even round)
     counts as a `yes' vote, while its absence counts as a `no' vote.
     We return both counts."))
  (b* (((when (set::emptyp voters)) (mv 0 0))
       (voter (set::head voters))
       ((mv yes-count no-count)
        (tally-leader-votes leader (set::tail voters))))
    (if (set::in leader (certificate->previous voter))
        (mv (1+ yes-count) no-count)
      (mv yes-count (1+ no-count))))
  :verify-guards :after-returns

  ///

  (defret tally-leader-votes-sum
    (equal (+ yes-count no-count)
           (set::cardinality voters))
    :hints (("Goal"
             :induct t
             :in-theory (enable set::cardinality))))
  (in-theory (disable tally-leader-votes-sum))

  (defruled tally-leader-votes-of-insert
    (equal (tally-leader-votes leader (set::insert voter voters))
           (if (set::in voter voters)
               (tally-leader-votes leader voters)
             (mv (if (set::in leader (certificate->previous voter))
                     (1+ (mv-nth 0 (tally-leader-votes leader voters)))
                   (mv-nth 0 (tally-leader-votes leader voters)))
                 (if (not (set::in leader (certificate->previous voter)))
                     (1+ (mv-nth 1 (tally-leader-votes leader voters)))
                   (mv-nth 1 (tally-leader-votes leader voters))))))
    :induct (set::weak-insert-induction voter voters)))
