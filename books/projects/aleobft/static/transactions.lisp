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

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/pos-set" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
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
     but also `solutions' and `ratifications',
     which together with transactions form `transmissions'.
     However, these details are unimportant for our model.
     We can treat transactions as abstract entities,
     since our model is only concerned with
     properly putting them into blocks."))
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
  :pred transactionp
  :prepwork ((local (in-theory (enable identity)))))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist transaction-list
  :short "Fixtype of lists of transactions."
  :elt-type transaction
  :true-listp t
  :elementp-of-nil nil
  :pred transaction-listp
  :prepwork ((local (in-theory (enable nfix)))))
