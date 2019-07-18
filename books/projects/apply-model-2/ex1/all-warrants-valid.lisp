; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;        Verification that All the Warrants in User-Book.lisp Are Valid
;                     in the Evaluation Theory Produced by
;   the Defattaches of their Doppelgangers to BADGE-USERFN and APPLY$-USERFN

(in-package "MODAPP")

(include-book "evaluation-lemmas")

(defthm apply$-warrant-SQUARE-valid
  (apply$-warrant-SQUARE)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SQUARE-definition))))

(defthm apply$-warrant-NATS-valid
  (apply$-warrant-NATS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-NATS-definition))))

(defthm apply$-warrant-COUNT-ATOMS-valid
  (apply$-warrant-COUNT-ATOMS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COUNT-ATOMS-definition))))

(defthm apply$-warrant-SUMLIST-valid
  (apply$-warrant-SUMLIST)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST-definition))))

(defthm apply$-warrant-FOLDR-valid
  (apply$-warrant-FOLDR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FOLDR-definition))))

(defthm apply$-warrant-PROW-valid
  (apply$-warrant-PROW)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW-definition))))

(defthm apply$-warrant-PROW*-valid
  (apply$-warrant-PROW*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW*-definition))))

(defthm apply$-warrant-COLLECT-A-valid
  (apply$-warrant-COLLECT-A)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-A-definition))))

(defthm apply$-warrant-SUM-OF-PRODUCTS-valid
  (apply$-warrant-SUM-OF-PRODUCTS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUM-OF-PRODUCTS-definition))))

(defthm apply$-warrant-ACK$-valid
  (apply$-warrant-ACK$)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-ACK$-definition))))

(defthm apply$-warrant-SILLY$-valid
  (apply$-warrant-SILLY$)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SILLY$-definition))))

