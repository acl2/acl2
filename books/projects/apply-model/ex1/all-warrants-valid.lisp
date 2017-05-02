; Copyright (C) 2016, ForrestHunt, Inc.
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
  (("Goal" :in-theory (enable apply$-warrant-SQUARE))))

(defthm apply$-warrant-NATS-valid
  (apply$-warrant-NATS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-NATS))))

(defthm apply$-warrant-SUMLIST-valid
  (apply$-warrant-SUMLIST)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST))))

(defthm apply$-warrant-FOLDR-valid
  (apply$-warrant-FOLDR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FOLDR))))

(defthm apply$-warrant-PROW-valid
  (apply$-warrant-PROW)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW))))

(defthm apply$-warrant-PROW*-valid
  (apply$-warrant-PROW*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW*))))

(defthm apply$-warrant-COLLECT-A-valid
  (apply$-warrant-COLLECT-A)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-A))))

(defthm apply$-warrant-SUM-OF-PRODUCTS-valid
  (apply$-warrant-SUM-OF-PRODUCTS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUM-OF-PRODUCTS))))
