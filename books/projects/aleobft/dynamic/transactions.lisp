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
     which together with transactions form `transmissions'.")
   (xdoc::p
    "However, most of these details are unimportant for our model.
     Our model is only concerned with two kinds of transactions:
     one to bond a validator (i.e. add the validator to the committee), and
     one to unbond a validator (i.e. remove the validator from the committee).
     So we consider these two kinds of transactions,
     plus an opaque one for all other kinds of transactions,
     and more in general the other kinds of transmissions mentioned above.
     We stick to the more common term `transaction' in our model,
     but one can imagine that the non-bonding and non-unbonding transactions
     (i.e. the third kind of transactions in our model)
     also captures solutions and ratifications."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum transaction
  :short "Fixtype of transactions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our model treats transactions as mostly opaque.
     Certain transactions bond and unbond validators,
     which is what makes the validator committee dynamic.
     So we model three kinds of transactions:
     bond a validator,
     unbond a validator,
     and something else that does not bond or unbond validators;
     we leave the details of third third kind open.")
   (xdoc::p
    "We do not model stake,
     so the bonding and unbonding transactions
     only contain an address (of the validator bonded or unbonded).")
   (xdoc::p
    "We do not model solutions and ratifications explicitly.
     The third kind of transactions in our model
     can be thought of as including those as well."))
  (:bond ((validator address)))
  (:unbond ((validator address)))
  (:other ((unwrap any)))
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
