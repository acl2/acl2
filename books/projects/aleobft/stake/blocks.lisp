; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

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
     which is also used to calculate dynamic committees from the blocks."))
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
          strictly increasing (right to left), even round numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each (correct) validator includes
     a list of blocks that models the blockchain (as seen by the validator).
     As explained there, blocks go from right to left,
     i.e. the @(tsee car) is the latest block.")
   (xdoc::p
    "Blocks are committed at even rounds,
     using increasingly higher round numbers,
     at most one block per (even) round.
     So the blocks will have round numbers in stricly increasing order,
     and they will all be even.
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
    :enable (append last)
    :hints ('(:use ((:instance lemma
                               (x (block->round (car blocks2)))
                               (y (block->round (car (last blocks1))))))))
    :prep-lemmas
    ((defruled lemma
       (implies (and (natp x)
                     (natp y)
                     (evenp x)
                     (evenp y)
                     (< x y))
                (<= (+ 2 x) y))
       :enable evenp))))

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
     If there are no blocks, we totalize this function to return 0.
     However, we do not require @(tsee blocks-ordered-even-p) in the guard."))
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
