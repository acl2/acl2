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

(defxdoc+ genesis-committees
  :parents (initialization)
  :short "Genesis committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "An execution of AleoBFT starts with an initial committeed
     called the `genesis committee',
     which changes as validators bond and unbond.
     The genesis committee is arbitrary,
     but fixed for each execution of the protocol.
     Thus, we model the genesis committee via a constrained nullary function
     that returns the set of addresses of the genesis committee.")
   (xdoc::p
    "This model of the genesis committee is part of the definition of
     the possible initial states of the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection genesis-committee
  :short "Genesis committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see initialization),
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
