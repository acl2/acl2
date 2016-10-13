; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "evaluation-lemmas")

; Verification that All the Warrants in User-Book.lisp Are Valid in
;               the Evaluation Theory Produced by the
;  Defattaches of their Doppelgangers to BADGE-USERFN and APPLY$-USERFN

(in-package "ACL2")

(defthm apply$-warrant-AP-valid
  (apply$-warrant-AP)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-ap))))

(defthm apply$-warrant-REV-valid
  (apply$-warrant-REV)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-rev))))

(defthm apply$-warrant-PALINDROMIFY-LIST-valid
  (apply$-warrant-PALINDROMIFY-LIST)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-palindromify-list))))

(defthm apply$-warrant-LIST-OF-TRUE-LISTSP-valid
  (apply$-warrant-LIST-OF-TRUE-LISTSP)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-list-of-true-listsp))))

(defthm apply$-warrant-LIST-OF-LIST-OF-TRUE-LISTSP-valid
  (apply$-warrant-LIST-OF-LIST-OF-TRUE-LISTSP)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-list-of-list-of-true-listsp))))

(defthm apply$-warrant-EXPT-5-valid
  (apply$-warrant-EXPT-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-EXPT-5))))

(defthm apply$-warrant-OK-FNP-valid
  (apply$-warrant-OK-FNP)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-ok-fnp))))

(defthm apply$-warrant-COLLECT-valid
  (apply$-warrant-COLLECT)
  :hints
  (("Goal" :in-theory (e/d (apply$-warrant-collect)
                           (collect-is-a-foldr)))))

(defthm apply$-warrant-SUMLIST-valid
  (apply$-warrant-SUMLIST)
  :hints
  (("Goal" :in-theory (e/d (apply$-warrant-sumlist)
                           (sumlist-is-a-foldr)))))

(defthm apply$-warrant-SUMLIST-WITH-PARAMS-valid
  (apply$-warrant-SUMLIST-WITH-PARAMS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-sumlist-with-params))))

(defthm apply$-warrant-FILTER-valid
  (apply$-warrant-FILTER)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-filter))))

(defthm apply$-warrant-ALL-valid
  (apply$-warrant-ALL)
  :hints
  (("Goal" :in-theory (e/d (apply$-warrant-all)
                           (all-is-a-foldr)))))

(defthm apply$-warrant-COLLECT-ON-valid
  (apply$-warrant-COLLECT-ON)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-collect-on))))

(defthm apply$-warrant-COLLECT-TIPS-valid
  (apply$-warrant-COLLECT-TIPS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-collect-tips))))

(defthm apply$-warrant-APPLY$2-valid
  (apply$-warrant-APPLY$2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-apply$2))))

(defthm apply$-warrant-APPLY$2x-valid
  (apply$-warrant-APPLY$2x)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-apply$2x))))

(defthm apply$-warrant-APPLY$2xx-valid
  (apply$-warrant-APPLY$2x)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-apply$2xx))))

(defthm apply$-warrant-RUSSELL-valid
  (apply$-warrant-RUSSELL)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-russell))))

(defthm apply$-warrant-FOLDR-valid
  (apply$-warrant-FOLDR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-foldr))))

(defthm apply$-warrant-FOLDL-valid
  (apply$-warrant-FOLDL)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-foldl))))

(defthm apply$-warrant-COLLECT-FROM-TO-valid
  (apply$-warrant-COLLECT-FROM-TO)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-collect-from-to))))

(defthm apply$-warrant-COLLECT*-valid
  (apply$-warrant-COLLECT*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT*))))

(defthm apply$-warrant-COLLECT2-valid
  (apply$-warrant-COLLECT2)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT2))))

(defthm apply$-warrant-RECUR-BY-COLLECT-valid
  (apply$-warrant-RECUR-BY-COLLECT)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-RECUR-BY-COLLECT))))

(defthm apply$-warrant-PROW-valid
  (apply$-warrant-PROW)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW))))

(defthm apply$-warrant-PROW*-valid
  (apply$-warrant-PROW*)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-PROW*))))

(defthm apply$-warrant-FN-5-valid
  (apply$-warrant-FN-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-FN-5))))

(defthm apply$-warrant-MAP-FN-5-valid
  (apply$-warrant-MAP-FN-5)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-MAP-FN-5))))

(defthm apply$-warrant-SUMLIST-EXPR-valid
  (apply$-warrant-SUMLIST-EXPR)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUMLIST-EXPR))))

(defthm apply$-warrant-COLLECT-REV-valid
  (apply$-warrant-COLLECT-REV)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-COLLECT-REV))))

(defthm apply$-warrant-SUM-OF-PRODUCTS-valid
  (apply$-warrant-SUM-OF-PRODUCTS)
  :hints
  (("Goal" :in-theory (enable apply$-warrant-SUM-OF-PRODUCTS))))

