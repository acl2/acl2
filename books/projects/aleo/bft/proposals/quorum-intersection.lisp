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

(include-book "fault-tolerance")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ quorum-intersection
  :parents (correctness)
  :short "Quorum intersection."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a fairly ubiquitous concept in BFT systems.
     This concept can be generally described like this:
     certain decisions are made (by correct validators)
     only if they are supported by a quorum of validators;
     contradictory decisions cannot be made because,
     because each decision would be supported by a quorum,
     but the intersection of the two quora would contain enough validators
     that there is at least a correct one in the intersection,
     which would not have supported both decisions.
     This is the case if the system is fault-tolerant,
     i.e. @($f < n/3$) (see @(tsee max-faulty-for-total)).")
   (xdoc::p
    "The quorum intersection argument is normally based on number of validators:
     both @($n$) and @($f$) measure numbers of validators.
     In AleoBFT, stake is used instead of numbers of validators:
     both @($n$) and @($f$) measure stake;
     see @(see fault-tolerance), as well as the functions
     @(tsee committee-max-faulty-stake) and @(tsee committee-quorum-stake).
     The quorum argument works not only for numbers of validators,
     but also for stake of validators,
     as we prove here.")
   (xdoc::p
    "In AleoBFT, quorum intersection applies to certificate non-equivocation.
     By requiring a quorum of signatures,
     where each signature supports the certificate
     (in the sense of `supporting' mentioned above),
     we ensure that two incompatible certificates,
     i.e. two certificates with different proposals but equal author and round,
     cannot exist because they would have to be both signed by
     at least one correct validator in the intersection of the quora;
     the intersection consists of stake (not numbers of validators),
     but it still implies the existence of
     at least one correct validator in both quora.
     Note that non-equivocation is limited to the proposals,
     not to the whole certificates,
     because it is possible that two correct validator obtain certificates
     certificates with identical proposals but slightly different signatures.")
   (xdoc::p
    "Here we introduce a function that picks a correct validator (if any)
     from the intersection of two sets of (addresses of) validators
     from a common committee.
     We prove that, if the committee is fault-tolerant,
     and each set of addresses has at least the quorum stake,
     the function indeed picks a correct validator.
     This is then used (elsewhere) to prove certificate non-equivocation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pick-common-correct-validator ((vals1 address-setp)
                                       (vals2 address-setp)
                                       (systate system-statep))
  :returns (val? address-optionp)
  :short "Pick a common correct validator address from two sets of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just @(tsee pick-correct-validator)
     applied to the intersection of the two sets.
     The significance of this is that,
     as explained in @(see quorum-intersection),
     we want to intersect two quora
     (represented by @('vals1') and @('vals2') here),
     and pick a correct validator common to the two sets."))
  (pick-correct-validator (set::intersect (address-set-fix vals1)
                                          (address-set-fix vals2))
                          systate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled stake-of-quorum-intersection
  :short "Stake of a quorum intersection."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the intersection of two quora
     that are both subsets of a non-empty committee of total stake @($n$)
     have more than @($f$) stake.
     Refer to @(tsee max-faulty-for-total) for
     a description of @($f$) and @($n$).")
   (xdoc::p
    "The non-emptiness of the committee is a critical assumption.
     If the committee is empty, we have @($n = f = 0$),
     and the intersection has zero stake.")
   (xdoc::p
    "Let @($A$) and @($B$) be the two sets of (addresses of) validators
     whose total stakes are @($S(A)$) and @($S(B)$).
     Since they each form a quorum, their stakes are at least @($n - f$):")
   (xdoc::@[]
    "S(A) \\geq n - f")
   (xdoc::@[]
    "S(B) \\geq n - f")
   (xdoc::p
    "Furthermore, since both @($A$) and @($B$) are subsets of the committee,
     their union is also a subset of the committe,
     and thus the stake of the union is bounded by
     the committee's total stake,
     i.e.")
   (xdoc::@[]
    "S(A \\cup B) \\leq n")
   (xdoc::p
    "This fact is proved as a local lemma,
     which fires as a rewrite rule in the proof of the main theorem.")
   (xdoc::p
    "We start from the previously proved (in @(tsee committee-members-stake))
     fact that")
   (xdoc::@[]
    "S(A \\cup B) = S(A) + S(B) - S(A \\cap B)")
   (xdoc::p
    "from which we get")
   (xdoc::@[]
    "S(A \\cap B) = S(A) + S(B) - S(A \\cup B)")
   (xdoc::p
    "If we use the quorum inequalities of @($A$) and @($B$) (see above),
     we obtain")
   (xdoc::@[]
    "S(A \\cap B) \\geq 2n - 2f - S(A \\cup B)")
   (xdoc::p
    "But as mentioned earlier we have")
   (xdoc::@[]
    "S(A \\cup B) \\leq n")
   (xdoc::p
    "that is")
   (xdoc::@[]
    "- S(A \\cup B) \\geq -n")
   (xdoc::p
    "and if we use that in the inequality above we get")
   (xdoc::@[]
    "S(A \\cap B) \\geq 2n - 2f - n")
   (xdoc::p
    "Since @($f < n/3$), we have @($n > 3f$),
     which we substitute above obtaining")
   (xdoc::@[]
    "S(A \\cap B) \\geq 2n - 2f - n = n - 2f > 3f - 2f = f")
   (xdoc::p
    "So we get")
   (xdoc::@[]
    "S(A \\cap B) > f")
   (xdoc::p
    "Note that committees are defined to be non-empty,
     so we have @($n > 0$), which is necessary here,
     otherwise @($f = n = 0$) and @($f = n/3$) (not @($f < n/3$)).")
   (xdoc::p
    "ACL2's built-in arithmetic,
     plus perhaps some other arithmetic rules that happen to be available,
     takes care of the reasoning detailed above,
     but we need to help things with a few hints.
     We expand various definition so to expose @(tsee max-faulty-for-total),
     for which the linear rule @('total-lower-bound-wrt-max-faulty')
     fires in the proof, corresponding to @($n > 3f$) above;
     that rule says @($n \\geq 3f + 1$), which is equivalent.
     We also need to expand the cardinality of the intersection,
     and disable the rule that expands the cardinality of the union.
     We also need a lemma, as mentioned earlier."))
  (implies (and (address-setp vals1)
                (address-setp vals2)
                (committee-nonemptyp commtt)
                (set::subset vals1 (committee-members commtt))
                (set::subset vals2 (committee-members commtt))
                (>= (committee-members-stake vals1 commtt)
                    (committee-quorum-stake commtt))
                (>= (committee-members-stake vals2 commtt)
                    (committee-quorum-stake commtt)))
           (> (committee-members-stake (set::intersect vals1 vals2) commtt)
              (committee-max-faulty-stake commtt)))
  :rule-classes :linear
  :enable (committee-members-stake-of-intersect
           committee-quorum-stake
           committee-max-faulty-stake
           total-lower-bound-wrt-max-faulty)
  :prep-lemmas
  ((defrule lemma
     (implies (and (address-setp vals1)
                   (address-setp vals2)
                   (set::subset vals1 (committee-members commtt))
                   (set::subset vals2 (committee-members commtt)))
              (<= (committee-members-stake (set::union vals1 vals2) commtt)
                  (committee-total-stake commtt)))
     :rule-classes :linear
     :enable (committee-total-stake
              committee-members-stake-monotone))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled quorum-intersection-has-correct-validator
  :short "A quorum intersection has at least one correct validator
          if the committee is non-empty and fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the main property of quorum intersection.
     Given a non-empty fault-tolerant committee,
     and two quora of validators in the committee,
     the function @(tsee pick-common-correct-validator)
     returns a validator that is in both quora and is correct.")
   (xdoc::p
    "First we prove that the function returns
     a correct validator in the intersection,
     from which it easily follows that it returns
     a correct validator in both quora."))
  (implies (and (address-setp vals1)
                (address-setp vals2)
                (committee-nonemptyp commtt)
                (committee-fault-tolerant-p commtt systate)
                (set::subset vals1 (committee-members commtt))
                (set::subset vals2 (committee-members commtt))
                (>= (committee-members-stake vals1 commtt)
                    (committee-quorum-stake commtt))
                (>= (committee-members-stake vals2 commtt)
                    (committee-quorum-stake commtt)))
           (b* ((val (pick-common-correct-validator vals1 vals2 systate)))
             (and (set::in val vals1)
                  (set::in val vals2)
                  (set::in val (correct-addresses systate)))))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (and (address-setp vals1)
                   (address-setp vals2)
                   (committee-nonemptyp commtt)
                   (committee-fault-tolerant-p commtt systate)
                   (set::subset vals1 (committee-members commtt))
                   (set::subset vals2 (committee-members commtt))
                   (>= (committee-members-stake vals1 commtt)
                       (committee-quorum-stake commtt))
                   (>= (committee-members-stake vals2 commtt)
                       (committee-quorum-stake commtt)))
              (b* ((val (pick-common-correct-validator vals1 vals2 systate)))
                (and (set::in val (set::intersect vals1 vals2))
                     (set::in val (correct-addresses systate)))))
     :enable (pick-common-correct-validator
              stake-of-quorum-intersection
              pick-correct-validator-in-set
              pick-correct-validator-is-correct
              set::expensive-rules)
     :use (:instance
           pick-correct-validator-when-fault-tolerant-and-gt-max-faulty
           (vals (set::intersect vals1 vals2))))))
