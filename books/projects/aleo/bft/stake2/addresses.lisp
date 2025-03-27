; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ addresses
  :parents (states)
  :short "Addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator has a unique address,
     which is an Aleo blockchain address of the form @('aleo1...').
     An address is essentially a public key;
     the validator uses the associated private key to sign data.")
   (xdoc::p
    "In our model, the details of these addresses are irrelevant,
     so we treat addresses as abstract entities.
     Our model only needs to compare addresses for equality."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod address
  :short "Fixtype of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "To treat addresses abstractly,
     we define this fixtype as a wrapper of the fixtype of all ACL2 values.
     In other words, we can use any ACL2 value as an address,
     e.g. to construct examples and simulations."))
  ((unwrap any))
  :pred addressp
  :prepwork ((local (in-theory (enable identity)))))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption address-option
  address
  :short "Fixtype of optional addresses."
  :pred address-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::defset address-set
  :short "Fixtype of sets of addresses."
  :elt-type address
  :elementp-of-nil nil
  :pred address-setp)
