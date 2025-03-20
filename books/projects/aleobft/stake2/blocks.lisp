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

(include-book "transactions")

(local (include-book "../library-extensions/arithmetic-theorems"))

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
     blocks are mainly containers of transactions.
     We also explicate the round number at which each block is generated:
     there is a natural association of round numbers to blocks,
     which is used to calculate dynamic committees from the blocks."))
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
     but we do not capture that constraint in this fixtype."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define blocks-ordered-even-p ((blocks block-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of blocks has
          strictly increasing (right to left) even round numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each (correct) validator includes
     a list of blocks that models the blockchain as seen by the validator.
     Blocks go from right to left, i.e. the @(tsee car) is the newest block.")
   (xdoc::p
    "Blocks are committed at even rounds,
     using increasingly higher round numbers,
     at most one block per (even) round.
     So the blocks have even round numbers in stricly increasing order.
     This predicate fomalizes these constraints on round numbers."))
  (b* (((when (endp blocks)) t)
       (block (car blocks))
       (round (block->round block))
       ((unless (evenp round)) nil)
       ((when (endp (cdr blocks))) t)
       ((unless (> round (block->round (cadr blocks)))) nil))
    (blocks-ordered-even-p (cdr blocks)))
  :hooks (:fix)

  ///

  (defrule blocks-ordered-even-p-of-cdr
    (implies (blocks-ordered-even-p blocks)
             (blocks-ordered-even-p (cdr blocks))))

  (defruled newest-geq-oldest-when-blocks-ordered-even-p
    (implies (and (blocks-ordered-even-p blocks)
                  (consp blocks))
             (>= (block->round (car blocks))
                 (block->round (car (last blocks)))))
    :rule-classes ((:linear
                    :trigger-terms ((block->round (car blocks))
                                    (block->round (car (last blocks))))))
    :induct t
    :enable last)

  (defruled evenp-of-car-when-blocks-ordered-even-p
    (implies (and (blocks-ordered-even-p blocks)
                  (consp blocks))
             (evenp (block->round (car blocks)))))

  (defruled evenp-of-car-of-last-when-blocks-ordered-even-p
    (implies (and (blocks-ordered-even-p blocks)
                  (consp blocks))
             (evenp (block->round (car (last blocks)))))
    :induct t
    :enable last)

  (defruled evenp-of-nth-when-blocks-ordered-even-p
    (implies (and (blocks-ordered-even-p blocks)
                  (< (nfix i) (len blocks)))
             (evenp (block->round (nth i blocks))))
    :induct t
    :enable (nth nfix len))

  (defruled blocks-ordered-even-p-of-append
    (equal (blocks-ordered-even-p (append blocks1 blocks2))
           (and (blocks-ordered-even-p blocks1)
                (blocks-ordered-even-p blocks2)
                (or (endp blocks1)
                    (endp blocks2)
                    (>= (block->round (car (last blocks1)))
                        (+ 2 (block->round (car blocks2)))))))
    :induct t
    :enable (append
             last
             aleobft::lt-to-2+le-when-both-evenp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define blocks-last-round ((blocks block-listp))
  :returns (last natp)
  :short "Last round in a list of blocks, or 0 if there are no blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee blocks-ordered-even-p) holds,
     block rounds are in strictly increading order from right to left.
     This function returns the latest, i.e. highest, round.
     If there are no blocks, this function returns 0.")
   (xdoc::p
    "Although it may seem natural
     to add @(tsee blocks-ordered-even-p) to this function's guard,
     we deliberately avoid that, for the following reason.
     Adding that guard here requires adding it to other operations,
     particularly @(tsee active-committee-at-round).
     The latter is used to define system transistions,
     and is applied to blockchains of validators,
     which are just lists of blocks,
     not necessarily satisfying @(tsee blocks-ordered-even-p).
     It is an invariant that they satisfy that predicate,
     but that invariant is proved after defining the transitions,
     and so it is not available when defining the transitions."))
  (if (consp blocks)
      (block->round (car blocks))
    0)
  :hooks (:fix)

  ///

  (defruled evenp-of-blocks-last-round
    (implies (blocks-ordered-even-p blocks)
             (evenp (blocks-last-round blocks)))
    :enable evenp-of-car-when-blocks-ordered-even-p)

  (defruled oldest-of-prefix-gt-newest-of-suffix-when-blocks-ordered-even-p
    (implies (and (blocks-ordered-even-p (append blocks1 blocks2))
                  (consp blocks1))
             (> (block->round (car (last blocks1)))
                (blocks-last-round blocks2)))
    :rule-classes ((:linear
                    :trigger-terms ((block->round (car (last blocks1)))
                                    (blocks-last-round blocks2))))
    :enable blocks-ordered-even-p-of-append))
