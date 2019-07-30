; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "evaluation-lemmas")

; Verification that All the Warrants in User-Book.lisp Are Valid in
;               the Evaluation Theory Produced by the
;  Defattaches of their Doppelgangers to BADGE-USERFN and APPLY$-USERFN

(in-package "MODAPP")

(include-book "evaluation-lemmas")

(defthm apply$-warrant-SQUARE-valid
  (apply$-warrant-SQUARE)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SQUARE-definition))))

(defthm apply$-warrant-CUBE-valid
  (apply$-warrant-CUBE)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-CUBE-definition))))

(defthm apply$-warrant-MY-APPEND1-valid
  (apply$-warrant-MY-APPEND1)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MY-APPEND1-definition))))

(defthm apply$-warrant-MY-REV-valid
  (apply$-warrant-MY-REV)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MY-REV-definition))))

(defthm apply$-warrant-NATS-valid
  (apply$-warrant-NATS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-NATS-definition))))

(defthm apply$-warrant-EXPT-5-valid
  (apply$-warrant-EXPT-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-EXPT-5-definition))))

(defthm apply$-warrant-OK-FNP-valid
  (apply$-warrant-OK-FNP)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-OK-FNP-definition))))

(defthm apply$-warrant-COUNT-ATOMS-valid
  (apply$-warrant-COUNT-ATOMS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COUNT-ATOMS-definition))))

(defthm apply$-warrant-COLLECT-valid
  (apply$-warrant-COLLECT)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-definition))))

(defthm apply$-warrant-SUMLIST-valid
  (apply$-warrant-SUMLIST)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST-definition))))

(defthm apply$-warrant-SUMLIST-WITH-PARAMS-valid
  (apply$-warrant-SUMLIST-WITH-PARAMS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST-WITH-PARAMS-definition))))

(defthm apply$-warrant-FILTER-valid
  (apply$-warrant-FILTER)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FILTER-definition))))

(defthm apply$-warrant-ALL-valid
  (apply$-warrant-ALL)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-ALL-definition))))

(defthm apply$-warrant-XISTS-valid
  (apply$-warrant-XISTS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-XISTS-definition))))

(defthm apply$-warrant-MAXLIST-valid
  (apply$-warrant-MAXLIST)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MAXLIST-definition))))

(defthm apply$-warrant-COLLECT-ON-valid
  (apply$-warrant-COLLECT-ON)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-ON-definition))))

(defthm apply$-warrant-COLLECT-TIPS-valid
  (apply$-warrant-COLLECT-TIPS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-TIPS-definition))))

(defthm apply$-warrant-APPLY$2-valid
  (apply$-warrant-APPLY$2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-APPLY$2-definition))))

(defthm apply$-warrant-APPLY$2x-valid
  (apply$-warrant-APPLY$2x)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-APPLY$2X-definition))))

(defthm apply$-warrant-APPLY$2xx-valid
  (apply$-warrant-APPLY$2x)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-APPLY$2XX-definition))))

(defthm apply$-warrant-RUSSELL-valid
  (apply$-warrant-RUSSELL)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-RUSSELL-definition))))

(defthm apply$-warrant-FOLDR-valid
  (apply$-warrant-FOLDR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FOLDR-definition))))

(defthm apply$-warrant-FOLDL-valid
  (apply$-warrant-FOLDL)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FOLDL-definition))))

(defthm apply$-warrant-COLLECT-FROM-TO-valid
  (apply$-warrant-COLLECT-FROM-TO)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-FROM-TO-definition))))

(defthm apply$-warrant-COLLECT*-valid
  (apply$-warrant-COLLECT*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT*-definition))))

(defthm apply$-warrant-COLLECT2-valid
  (apply$-warrant-COLLECT2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT2-definition))))

(defthm apply$-warrant-RECUR-BY-COLLECT-valid
  (apply$-warrant-RECUR-BY-COLLECT)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-RECUR-BY-COLLECT-definition))))

(defthm apply$-warrant-PROW-valid
  (apply$-warrant-PROW)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW-definition))))

(defthm apply$-warrant-PROW*-valid
  (apply$-warrant-PROW*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW*-definition))))

(defthm apply$-warrant-FN-5-valid
  (apply$-warrant-FN-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FN-5-definition))))

(defthm apply$-warrant-MAP-FN-5-valid
  (apply$-warrant-MAP-FN-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MAP-FN-5-definition))))

(defthm apply$-warrant-SUMLIST-EXPR-valid
  (apply$-warrant-SUMLIST-EXPR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST-EXPR-definition))))

(defthm apply$-warrant-TWOFER-valid
  (apply$-warrant-TWOFER)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-TWOFER-definition))))

(defthm apply$-warrant-COLLECT-A-valid
  (apply$-warrant-COLLECT-A)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-A-definition))))

(defthm apply$-warrant-COLLECT-B-valid
  (apply$-warrant-COLLECT-B)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-B-definition))))

(defthm apply$-warrant-COLLECT-C-valid
  (apply$-warrant-COLLECT-C)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-C-definition))))

(defthm apply$-warrant-COLLECT-D-valid
  (apply$-warrant-COLLECT-D)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-D-definition))))

(defthm apply$-warrant-COLLECT-E-valid
  (apply$-warrant-COLLECT-E)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-E-definition))))

(defthm apply$-warrant-MY-APPLY-2-valid
  (apply$-warrant-MY-APPLY-2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MY-APPLY-2-definition))))

(defthm apply$-warrant-MY-APPLY-2-1-valid
  (apply$-warrant-MY-APPLY-2-1)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MY-APPLY-2-1-definition))))

(defthm apply$-warrant-COLLECT-MY-REV-valid
  (apply$-warrant-COLLECT-MY-REV)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-MY-REV-definition))))

(defthm apply$-warrant-MY-APPEND2-valid
  (apply$-warrant-MY-APPEND2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MY-APPEND2-definition))))

(defthm apply$-warrant-SQNATS-valid
  (apply$-warrant-SQNATS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SQNATS-definition))))

(defthm apply$-warrant-SUM-OF-PRODUCTS-valid
  (apply$-warrant-SUM-OF-PRODUCTS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUM-OF-PRODUCTS-definition))))

(defthm apply$-warrant-COLLECT-COMPOSITION-valid
  (apply$-warrant-COLLECT-COMPOSITION)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-COMPOSITION-definition))))

(defthm apply$-warrant-COLLECT-X1000-valid
  (apply$-warrant-COLLECT-X1000)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-X1000-definition))))

(defthm apply$-warrant-COLLECT-X1000-CALLER-valid
  (apply$-warrant-COLLECT-X1000-CALLER)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-X1000-CALLER-definition))))

(defthm apply$-warrant-GUARDED-COLLECT-valid
  (apply$-warrant-GUARDED-COLLECT)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-GUARDED-COLLECT-definition))))

(defthm apply$-warrant-ACK$-valid
  (apply$-warrant-ACK$)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-ACK$-definition))))

(defthm apply$-warrant-SILLY$-valid
  (apply$-warrant-SILLY$)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SILLY$-definition))))
