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
     because each would be supported by a quorum,
     but the intersection of the two quora would contain enough validators
     that there is at least a correct one in the intersection,
     which would not have supported both decisions.
     This is the case if the system is fault-tolerant,
     i.e. @($f < n/3$) (see @(tsee max-faulty-for-total)).")
   (xdoc::p
    "In AleoBFT this concept applies to certificate non-equivocation.
     By requiring a quorum of signatures,
     where each signature supports the certificate
     (in the sense of `supporting' mentioned above),
     we ensure that two incompatible certificates,
     i.e. two different certificates with the same author and round,
     cannot exist because they would have to be both signed by
     at least one correct validator in the intersection of the quora.")
   (xdoc::p
    "Here we introduce a function that picks a correct validator (if any)
     from the intersection of two sets of (addresses of) validators
     from a common committee.
     We prove that, if the committee is fault-tolerant,
     and each set of addresses forms a quorum,
     the function indeed picks a correct validator.
     This is then used (elsewhere) to prove certificate non-equivocation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pick-correct-validator ((vals address-setp) (systate system-statep))
  :returns (val? address-optionp)
  :short "Pick a correct validator address from a set of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Correct validators are identified via a system state,
     so we pass a system state to this function.")
   (xdoc::p
    "We go through all the addresses in the set,
     returning the first one we find that is of a correct validator.
     We return @('nil') if there is no correct validator address in the set.")
   (xdoc::p
    "We show that if this function returns an address,
     the address is in the input set,
     and it is the address of a correct validator.
     We show that if this function returns @('nil')
     and if all the addresses are in the system,
     then all the addresses are of faulty validators,
     because otherwise we would have found a correct one.")
   (xdoc::p
    "From the latter fact,
     we prove that this function will return an address
     if the following conditions are satisfied:
     the input set is a subset of a fault-tolerant committee,
     the committee consists of validators in the system,
     and the number of validators is more than @($f$),
     i.e. the maximum tolerated number of faulty validators
     (see @(tsee max-faulty-for-total)).
     The reason is that if @('pick-correct-validator') returned @('nil'),
     as proved then all the validators in @('vals') are faulty.
     But since we hypothesize that there are more than @($f$),
     and since the fault tolerance hypothesis means that
     there are no more than @($f$) faulty validators,
     we have an impossibility.
     Thus @('pick-correct-validator') must return an address,
     which as previously proved is in @('vals') and is a correct validator."))
  (b* (((when (set::emptyp vals)) nil)
       (val (set::head vals))
       ((when (set::in val (correct-addresses systate))) (address-fix val)))
    (pick-correct-validator (set::tail vals) systate))

  ///

  (fty::deffixequiv pick-correct-validator
    :args ((systate system-statep)))

  (defruled pick-correct-validator-in-set
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate)
                      vals))
    :induct t)

  (defruled pick-correct-validator-is-correct
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate)
                      (correct-addresses systate)))
    :induct t)

  (defruled all-faulty-when-not-pick-correct-validator
    (implies (and (set::subset vals (all-addresses systate))
                  (not (pick-correct-validator vals systate)))
             (set::subset vals (faulty-addresses systate)))
    :induct t
    :enable (faulty-addresses
             set::expensive-rules
             not-in-address-set-when-not-address))

  (defruled pick-correct-validator-when-fault-tolerant-p
    (implies (and (set::subset vals
                               (committee-members commtt))
                  (set::subset (committee-members commtt)
                               (all-addresses systate))
                  (committee-fault-tolerant-p commtt systate)
                  (> (set::cardinality vals)
                     (committee-max-faulty commtt)))
             (pick-correct-validator vals systate))
    :enable (committee-fault-tolerant-p
             committee-faulty-members
             set::expensive-rules)
    :disable pick-correct-validator
    :use (all-faulty-when-not-pick-correct-validator
          (:instance set::subset-of-intersect-if-subset-of-both
                     (a vals)
                     (b (faulty-addresses systate))
                     (c (committee-members commtt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (pick-correct-validator (set::intersect vals1 vals2) systate)
  ///
  (fty::deffixequiv pick-common-correct-validator
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-quorum-intersection
  :short "Cardinality of a quorum intersection."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the intersection of two quora
     that are both subsets of a committee of size @($n$)
     contains more than @($f$) elements.
     Refer to @(tsee max-faulty-for-total) for
     a description of @($f$) and @($n$).")
   (xdoc::p
    "Let @($A$) and @($B$) be the two sets of (addresses of) validators.
     Since they each form a quorum,
     their cardinality is")
   (xdoc::@[]
    "|A| = |B| = n - f")
   (xdoc::p
    "Furthermore, since both @($A$) and @($B$) are subsets of the committee,
     their union is also a subset of the committe,
     and thus the cardinality of the union is bounded by the committee size,
     i.e.")
   (xdoc::@[]
    "|A \\cup B| \\leq n")
   (xdoc::p
    "This fact is proved as a local lemma,
     which fires as a rewrite rule in the proof of the main theorem.")
   (xdoc::p
    "We start from the known fact that")
   (xdoc::@[]
    "|A \\cup B| = |A| + |B| - |A \\cap B|")
   (xdoc::p
    "from which we get")
   (xdoc::@[]
    "|A \\cap B| = |A| + |B| - |A \\cup B|")
   (xdoc::p
    "If we substitute the quorum cardinality of @($A$) and @($B$) (see above),
     we obtain")
   (xdoc::@[]
    "|A \\cap B| = 2n - 2f - |A \\cup B|")
   (xdoc::p
    "But as mentioned earlier we have")
   (xdoc::@[]
    "|A \\cup B| \\leq n")
   (xdoc::p
    "that is")
   (xdoc::@[]
    "- |A \\cup B| \\geq -n")
   (xdoc::p
    "and if we use that in the equation above we get")
   (xdoc::@[]
    "|A \\cap B| \\geq 2n - 2f - n")
   (xdoc::p
    "Since @($f < n/3$), we have @($n > 3f$),
     which we substitute above obtaining")
   (xdoc::@[]
    "|A \\cap B| \\geq 2n - 2f - n = n - 2f > 3f - 2f = f")
   (xdoc::p
    "So we get")
   (xdoc::@[]
    "|A \\cap B| > f")
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
  (implies (and (set::subset vals1 (committee-members commtt))
                (set::subset vals2 (committee-members commtt))
                (equal (set::cardinality vals1)
                       (committee-quorum commtt))
                (equal (set::cardinality vals2)
                       (committee-quorum commtt)))
           (> (set::cardinality (set::intersect vals1 vals2))
              (committee-max-faulty commtt)))
  :rule-classes :linear
  :enable (set::expand-cardinality-of-intersect
           committee-quorum
           committee-max-faulty
           total-lower-bound-wrt-max-faulty)
  :disable set::expand-cardinality-of-union
  :prep-lemmas
  ((defrule lemma
     (implies (and (set::subset vals1 (committee-members commtt))
                   (set::subset vals2 (committee-members commtt)))
              (<= (set::cardinality (set::union vals1 vals2))
                  (committee-total commtt)))
     :rule-classes :linear
     :enable committee-total
     :disable set::expand-cardinality-of-union)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled quorum-intersection-has-correct-validator
  :short "A quorum intersection has at least one correct validator
          if the committee is fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the main property of quorum intersection.
     Given a fault-tolerant committee whose members are in the system,
     and two quora of validators in the committee,
     the function @(tsee pick-common-correct-validator)
     returns a validator that is in both quora and is correct.")
   (xdoc::p
    "First we prove that the function returns
     a correct validator in the intersection,
     from which it easily follows that it returns
     a correct validator in both quora.
     Some attempts to prove this in one shot failed,
     but perhaps there is a way to avoid the intermediate local lemma."))
  (implies (and (set::subset (committee-members commtt)
                             (all-addresses systate))
                (committee-fault-tolerant-p commtt systate)
                (set::subset vals1 (committee-members commtt))
                (set::subset vals2 (committee-members commtt))
                (equal (set::cardinality vals1)
                       (committee-quorum commtt))
                (equal (set::cardinality vals2)
                       (committee-quorum commtt)))
           (b* ((val (pick-common-correct-validator vals1 vals2 systate)))
             (and (set::in val vals1)
                  (set::in val vals2)
                  (set::in val (correct-addresses systate)))))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (and (set::subset (committee-members commtt)
                                (all-addresses systate))
                   (committee-fault-tolerant-p commtt systate)
                   (set::subset vals1 (committee-members commtt))
                   (set::subset vals2 (committee-members commtt))
                   (equal (set::cardinality vals1)
                          (committee-quorum commtt))
                   (equal (set::cardinality vals2)
                          (committee-quorum commtt)))
              (b* ((val (pick-common-correct-validator vals1 vals2 systate)))
                (and (set::in val (set::intersect vals1 vals2))
                     (set::in val (correct-addresses systate)))))
     :enable (pick-common-correct-validator
              cardinality-of-quorum-intersection
              pick-correct-validator-in-set
              pick-correct-validator-is-correct
              set::expensive-rules)
     :use (:instance pick-correct-validator-when-fault-tolerant-p
                     (vals (set::intersect vals1 vals2))))))
