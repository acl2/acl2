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
     blocks are simply containers of transactions.
     We also explicate the round number at which each block is generated:
     there is a natural association of round numbers to blocks,
     which is also needed to calculate dynamic committees from the blocks.."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod block
  :short "Fixtype of blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a block as consisting of
     a list of transactions and a round number.
     The round number is always even,
     since blocks are only produced at even rounds,
     but we do not capture that constraint here."))
  ((transactions transaction-list)
   (round pos))
  :pred blockp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist block-list
  :short "Fixtype of lists of blocks."
  :elt-type block
  :true-listp t
  :elementp-of-nil nil
  :pred block-listp
  :prepwork ((local (in-theory (enable nfix)))))
