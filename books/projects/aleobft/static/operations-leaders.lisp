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

(include-book "validator-states")
(include-book "operations-certificate-retrieval")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-leaders
  :parents (operations)
  :short "Operations for leaders."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each even round has a globally known leader validator.
     If a validator (the leader or another) has a certificate
     at that round that is authored by the leader,
     that certificate is an anchor,
     which may be committed (under suitable conditions)
     to form a block that extends the blockchain.
     Here we introduce some operations related to leaders."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection leader-index
  :short "Under-specified indices for choosing round leaders."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every even round has a leader validator.
     We model that via an underspecified function
     that returns a natural number at each round.
     We only use the function on non-zero even rounds,
     since round 0 and odd rounds have no leaders.
     The natural number is reduced modulo the number of validators,
     and the resulting number is used as an index in
     the totally ordered set of validator addresses.")
   (xdoc::p
    "We only constrain this under-specified function
     to return a natural number.
     We also guard it to require a natural number as input
     (which we could tighten it to non-zero even natural number).")
   (xdoc::p
    "This approach to modeling leader choice amount to
     this under-specified being universally quantified:
     everything proved about the model
     holds for every concrete choice of the function.
     This is adequate for proving properties
     over single runs of the system
     (for every possible run, but just one round at a time).
     For properties involving multiple runs of the system,
     using a single under-constrained function would constrain
     the multiple runs to always choose the same leader at every round,
     which may not be adequate.
     But in this case, we can extend this under-constrained function
     to take an additional ``seed'' input,
     which makes it possible to return different natural numbers
     for the same round but for different seeds.
     Then the seed can be added to the internal state of the system;
     the seed never needs to change with events,
     but different initial states may have different seeds,
     and thus the multiple runs involved in a property of interest
     may be given different seeds,
     thus allowing them to choose different leaders at the same round.")
   (xdoc::p
    "In some literature, the distinction between
     properties over single runs vs. properties over multiple runs
     is describes as `properties' for the former
     and `hyperproperties' for the latter.
     We generally prefer to use the term `property'
     in the more general mathematical sense,
     and talk about (properties of) single or multiple runs
     when the distinction is relevant."))

  (encapsulate
      (((leader-index *) => * :formals (round) :guard (natp round)))

    (local (defun leader-index (round) (nfix round)))

    (defrule natp-of-leader-index
      (natp (leader-index round))
      :rule-classes (:rewrite :type-prescription))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nth-address ((index natp) (addrs address-setp))
  :guard (< index (set::cardinality addrs))
  :returns (addr addressp)
  :short "The address at a given index in a set of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 osets are ordered sets, according to ACL2's total order on values,
     and so they can be treated as lists (without repetitions);
     in fact, that is exactly how they are represented.
     In particular, it makes sense to retrieve the element of a set
     that occupies a given position in the sequential order.
     As in lists, we index the positions starting from 0.")
   (xdoc::p
    "This could be a more general operation on sets.
     Another option could be simply to use @(tsee nth),
     since osets are lists."))
  (cond ((set::emptyp addrs) (prog2$ (impossible) (address :irrelevant)))
        ((zp index) (address-fix (set::head addrs)))
        (t (nth-address (1- index) (set::tail addrs))))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leader-at-round ((round posp) (vals address-setp))
  :guard (and (evenp round)
              (not (set::emptyp vals)))
  :returns (leader addressp)
  :short "Address of the leader validator at a given non-zero even round."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the set of electable validators to this function.
     We retrieve the natural number for the round
     from the under-specified function for the leader index.
     We reduce the natural number modulo the number of validators,
     and use the index to pick the leader address.")
   (xdoc::p
    "The set of validators must be non-empty,
     otherwise there is no validator to pick."))
  (b* ((index (leader-index round))
       (index (mod index (set::cardinality vals))))
    (nth-address index vals))
  :prepwork
  ((local (include-book "kestrel/arithmetic-light/mod" :dir :system))))
