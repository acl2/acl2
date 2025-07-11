; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "addresses")
(include-book "transactions")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "library-extensions/oset-theorems"))

(local (include-book "std/osets/nonemptyp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposals
  :parents (states)
  :short "Proposals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators generate and exchange proposals,
     which contain proposed transactions along with other information.
     Once they have enough endorsements, in the form of signatures,
     proposals are turned into certificates,
     which are the vertices of the DAG.")
   (xdoc::p
    "Proposals have a rich structure,
     but we model only the information needed for our purposes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod proposal
  :short "Fixtype of proposals."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a proposal as consisting of:")
   (xdoc::ol
    (xdoc::li
     "The address of the validator who authored the proposal.")
    (xdoc::li
     "The round number of the proposal.")
    (xdoc::li
     "The transactions that the validator is proposing
      for inclusion in the blockchain.")
    (xdoc::li
     "The addresses that, together with the previous round number,
      identify the certificates from the previous round
      that this proposal references.
      When the proposal is turned into a certificate,
      these define the edges of the DAG.
      It is a system invariant, proved elsewhere,
      that certificates in DAGs are uniquely identified by
      their author and round."))
   (xdoc::p
    "We do not model cryptographic signatures explicitly.
     The presence of the author address in a proposal
     models the fact that the author signed the proposal."))
  ((author address)
   (round pos)
   (transactions transaction-list)
   (previous address-set))
  :pred proposalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption proposal-option
  proposal
  :short "Fixtype of optional proposals."
  :pred proposal-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset proposal-set
  :short "Fixtype of sets of proposals."
  :elt-type proposal
  :elementp-of-nil nil
  :pred proposal-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk prop-set-all-author-p ((author addressp) (props proposal-setp))
  :returns (yes/no booleanp)
  :short "Check if all the proposals in a set have a given author."
  (forall (prop)
          (implies (set::in prop (proposal-set-fix props))
                   (equal (proposal->author prop)
                          (address-fix author))))

  ///

  (fty::deffixequiv-sk prop-set-all-author-p
    :args ((author addressp) (props proposal-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk prop-set-none-author-p ((author addressp) (props proposal-setp))
  :returns (yes/no booleanp)
  :short "Check if none of the proposals in a set have a given author."
  (forall (prop)
          (implies (set::in prop (proposal-set-fix props))
                   (not (equal (proposal->author prop)
                               (address-fix author)))))

  ///

  (fty::deffixequiv-sk prop-set-none-author-p
    :args ((author addressp) (props proposal-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define props-with-author+round ((author addressp)
                                 (round posp)
                                 (props proposal-setp))
  :returns (props-with-author+round proposal-setp)
  :short "Retrieve, from a set of proposals,
          the subset of proposals with a given author and round."
  (b* (((when (set::emptyp (proposal-set-fix props))) nil)
       ((proposal prop) (set::head props)))
    (if (and (equal (address-fix author) prop.author)
             (equal (pos-fix round) prop.round))
        (set::insert (proposal-fix prop)
                     (props-with-author+round author round (set::tail props)))
      (props-with-author+round author round (set::tail props))))
  :prepwork ((local (in-theory (enable emptyp-of-proposal-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret props-with-author+round-subset
    (set::subset props-with-author+round props)
    :hyp (proposal-setp props)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defrule props-with-author+round-of-empty
    (equal (props-with-author+round author round nil)
           nil))

  (defruled in-of-props-with-author+round
    (equal (set::in prop (props-with-author+round author round props))
           (and (set::in prop (proposal-set-fix props))
                (equal (proposal->author prop)
                       (address-fix author))
                (equal (proposal->round prop)
                       (pos-fix round))))
    :induct t
    :enable emptyp-of-proposal-set-fix)

  (defruled not-emptyp-of-props-with-author+round
    (implies (and (set::in prop props)
                  (proposal-setp props)
                  (equal (proposal->author prop) author)
                  (equal (proposal->round prop) round))
             (not (set::emptyp (props-with-author+round author round props))))
    :induct t)

  (defruled props-with-author+round-when-none-author
    (implies (prop-set-none-author-p author props)
             (equal (props-with-author+round author round props) nil))
    :use lemma
    :enable set::emptyp
    :disable props-with-author+round
    :prep-lemmas
    ((defruled lemma
       (implies (prop-set-none-author-p author props)
                (set::emptyp (props-with-author+round author round props)))
       :enable (set::emptyp-to-not-nonemptyp
                set::nonemptyp
                in-of-props-with-author+round
                prop-set-none-author-p-necc)
       :disable props-with-author+round))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define props-with-round ((round posp) (props proposal-setp))
  :returns (props-with-round proposal-setp)
  :short "Retrieve, from a set of proposals,
          the subset of proposals with a given round."
  (b* (((when (set::emptyp (proposal-set-fix props))) nil)
       ((proposal prop) (set::head props)))
    (if (equal (pos-fix round) prop.round)
        (set::insert (proposal-fix prop)
                     (props-with-round round (set::tail props)))
      (props-with-round round (set::tail props))))
  :prepwork ((local (in-theory (enable emptyp-of-proposal-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret props-with-round-subset
    (set::subset props-with-round props)
    :hyp (proposal-setp props)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled in-of-props-with-round
    (equal (set::in prop (props-with-round round props))
           (and (set::in prop (proposal-set-fix props))
                (equal (proposal->round prop)
                       (pos-fix round))))
    :induct t)

  (defruled not-in-prop-set-when-none-with-round
    (implies (and (set::emptyp (props-with-round (proposal->round prop) props))
                  (proposal-setp props))
             (not (set::in prop props)))
    :induct t)

  (defruled not-in-prop-subset-when-none-with-round
    (implies (and (set::emptyp (props-with-round (proposal->round prop) props))
                  (set::subset props0 props)
                  (proposal-setp props0)
                  (proposal-setp props))
             (not (set::in prop props0)))
    :enable (not-in-prop-set-when-none-with-round
             set::expensive-rules))

  (defruled props-with-author+round-to-props-with-round
    (implies (prop-set-all-author-p author props)
             (equal (props-with-author+round author round props)
                    (props-with-round round props)))
    :disable props-with-round
    :enable (set::double-containment-no-backchain-limit
             set::subset-pick-a-point
             in-of-props-with-author+round
             in-of-props-with-round
             prop-set-all-author-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk prop-set-unequivp ((props proposal-setp))
  :returns (yes/no booleanp)
  :short "Check if a set of proposals is unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the proposals in the set
     have unique combinations of author and round.
     We check that any two proposals in the set
     with the same author and round
     are in fact the same proposal.
     This means that the proposals in the set
     are uniquely identified by their author and round.")
   (xdoc::p
    "The rule @('prop-set-unequivp-of-insert')
     is useful to prove the preservation of non-equivocation
     when a set of proposals is extended.
     Either the added proposal is already in the initial set,
     or the initial set has no proposal with
     the added proposal's author and round."))
  (forall (prop1 prop2)
          (implies (and (set::in prop1 (proposal-set-fix props))
                        (set::in prop2 (proposal-set-fix props))
                        (equal (proposal->author prop1)
                               (proposal->author prop2))
                        (equal (proposal->round prop1)
                               (proposal->round prop2)))
                   (equal prop1 prop2)))

  ///

  (fty::deffixequiv-sk prop-set-unequivp
    :args ((props proposal-setp)))

  (defruled prop-set-unequivp-when-subset
    (implies (and (prop-set-unequivp props)
                  (set::subset (proposal-set-fix props0)
                               (proposal-set-fix props)))
             (prop-set-unequivp props0))
    :disable prop-set-unequivp-necc
    :use (:instance prop-set-unequivp-necc
                    (prop1 (mv-nth 0 (prop-set-unequivp-witness props0)))
                    (prop2 (mv-nth 1 (prop-set-unequivp-witness props0))))
    :enable set::expensive-rules)

  (defrule proop-set-unequivp-of-empty
    (prop-set-unequivp nil))

  (defruled prop-set-unequivp-of-insert
    (implies (and (proposal-setp props)
                  (proposalp prop))
             (equal (prop-set-unequivp (set::insert prop props))
                    (and (prop-set-unequivp props)
                         (or (set::in prop props)
                             (set::emptyp (props-with-author+round
                                           (proposal->author prop)
                                           (proposal->round prop)
                                           props))))))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defruled if-part
       (implies (and (proposal-setp props)
                     (proposalp prop)
                     (prop-set-unequivp props)
                     (or (set::in prop props)
                         (set::emptyp (props-with-author+round
                                       (proposal->author prop)
                                       (proposal->round prop)
                                       props))))
                (prop-set-unequivp (set::insert prop props)))
       :use (:instance prop-set-unequivp-necc
                       (prop1 (mv-nth 0 (prop-set-unequivp-witness
                                         (set::insert prop props))))
                       (prop2 (mv-nth 1 (prop-set-unequivp-witness
                                         (set::insert prop props))))
                       (props props))
       :enable not-emptyp-of-props-with-author+round
       :disable prop-set-unequivp-necc)
     (defruled only-if-part
       (implies (and (proposal-setp props)
                     (proposalp prop)
                     (prop-set-unequivp (set::insert prop props)))
                (and (prop-set-unequivp props)
                     (or (set::in prop props)
                         (set::emptyp (props-with-author+round
                                       (proposal->author prop)
                                       (proposal->round prop)
                                       props)))))
       :enable (prop-set-unequivp-when-subset
                set::emptyp-to-not-nonemptyp
                set::nonemptyp
                in-of-props-with-author+round)
       :disable (prop-set-unequivp
                 prop-set-unequivp-necc)
       :use (:instance prop-set-unequivp-necc
                       (prop1 prop)
                       (prop2 (set::nonemptyp-witness
                               (props-with-author+round (proposal->author prop)
                                                        (proposal->round prop)
                                                        props)))
                       (props (set::insert prop props))))))

  (defruled prop-set-unequivp-of-delete
    (implies (and (proposal-setp props)
                  (prop-set-unequivp props))
             (prop-set-unequivp (set::delete prop props)))
    :disable prop-set-unequivp
    :enable prop-set-unequivp-when-subset))
