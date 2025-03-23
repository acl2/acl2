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

(include-book "addresses")
(include-book "transactions")

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
      that this proposal is based on.
      (More on this below.)"))
   (xdoc::p
    "A validator generates at most one proposal per round.
     Thus, the combination of author and round number identifies
     (at most) a unique proposal, and a unique certificate in a DAG.
     This uniqueness is a critical and non-trivial property,
     which we prove as an invariant elsewhere.")
   (xdoc::p
    "A certificate is a vertex of the DAG.
     The @('previous') component of this fixtype models
     the edges of the DAG (once the proposal becomes a certificate),
     from this proposal/certificate to
     the certificates in the previous round
     with the authors specified by the set of addresses.
     Because of the invariant mentioned above,
     those certificates are uniquely determined.")
   (xdoc::p
    "We do not model cryptographic signatures explicitly.
     The presence of the author address in a proposal
     models the fact that
     the validator with that address has signed the proposal."))
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
  :hooks (:fix))

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
             set::expensive-rules)))
