; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "std/lists/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transactions
  :parents (states)
  :short "Transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators propose transactions for inclusion in the blockchain.
     Transactions have a rich structure.
     In fact, AleoBFT handles not only transactions,
     but also `solutions' and (possibly in the future) `ratifications',
     which together with transactions form `transmissions'.")
   (xdoc::p
    "However, these details are unimportant for our model.
     Our model sticks to the more common term `transaction',
     which can be thought as modeling also the other kinds of transmissions.
     We treat transactions as abstract entities."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transaction
  :short "Fixtype of transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "To treat transactions abstractly,
     we define this fixtype as a wrapper of the fixtype of all ACL2 values.
     In other words, we can use any ACL2 value as a transaction,
     e.g. to construct examples and simulations."))
  ((unwrap any))
  :pred transactionp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist transaction-list
  :short "Fixtype of lists of transactions."
  :elt-type transaction
  :true-listp t
  :elementp-of-nil nil
  :pred transaction-listp
  :prepwork ((local (in-theory (enable nfix)))))
