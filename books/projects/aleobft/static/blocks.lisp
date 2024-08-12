; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "transactions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ blocks
  :parents (states)
  :short "Blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "Blocks in the Aleo blockchain have a rich structure.
     However, for the purpose of our model,
     blocks are simply containers of transactions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod block
  :short "Fixtype of blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a block as consisting of a list of transactions.")
   (xdoc::p
    "There is a natural association of blocks to round numbers.
     But since in our current model committees are static,
     we do not need that information in a block.
     We just need blocks to be containers of transactions.
     Furthermore, as proved in @(see invariant-blockchain-redundant),
     the blocks in a validator state are actually redundant,
     i.e. calculable from other state components
     (specifically, the committed anchors),
     so one can always obtain the round numbers associated to blocks
     by calculating them from the committed anchors."))
  ((transactions transaction-list))
  :pred blockp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist block-list
  :short "Fixtype of lists of blocks."
  :elt-type block
  :true-listp t
  :elementp-of-nil nil
  :pred block-listp
  :prepwork ((local (in-theory (enable nfix)))))
