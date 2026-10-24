; Putting eliminate-irrelevance-clause and its subroutines into :logic mode
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book puts ELIMINATE-IRRELEVANCE-CLAUSE and all of its (formerly
;; :program mode) subroutines into :logic mode, by proving their termination.
;; Guards are not verified here.  Most of these functions are the
;; induction-candidate merging code that M&M-APPLY dispatches to, since
;; eliminate-irrelevance-clause partitions the literals of a clause using M&M.

;; Several measures below have the form (if x (+ 1 (len x)) 0), the number of
;; steps to reach NIL by taking CDRs, which handles recursions that stop when x
;; is NIL (rather than when x is an atom).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tag-trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination add-to-tag-tree! (declare (xargs :verify-guards nil)))
(verify-termination remove1-assoc-eq-assoc-eq-1 (declare (xargs :verify-guards nil)))
(verify-termination remove1-assoc-eq-assoc-eq (declare (xargs :verify-guards nil)))
(verify-termination cons-tag-trees1 (declare (xargs :verify-guards nil)))
(verify-termination cons-tag-trees (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Flushing induction candidates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The level of the fit function FN.  Pigeon-holep-apply calls pigeon-holep
;; only with a fit function of a lower level.
(defund pigeon-holep-fn-level (fn)
  (declare (xargs :guard t))
  (cond ((eq fn 'tests-and-alists-fitp) 2)
        ((eq fn 'alist-fitp) 1)
        (t 0)))

;; The measures are triples ordered lexicographically: the level of FN, then
;; (twice) the number of pigeons left, then the number of holes left to try.
(verify-termination
  (pigeon-holep-apply
   (declare (xargs :measure (make-ord 2
                                      (+ 1 (pigeon-holep-fn-level fn))
                                      (make-ord 1 1 0))
                   :hints (("Goal" :in-theory (enable pigeon-holep-fn-level)))
                   :verify-guards nil)))
  (pigeon-holep
   (declare (xargs :measure (make-ord 2
                                      (+ 1 (pigeon-holep-fn-level fn))
                                      (make-ord 1
                                                (+ 2 (* 2 (if pigeons (+ 1 (len pigeons)) 0)))
                                                0))
                   :verify-guards nil)))
  (pigeon-holep1
   (declare (xargs :measure (make-ord 2
                                      (+ 1 (pigeon-holep-fn-level fn))
                                      (make-ord 1
                                                (+ 3 (* 2 (if pigeons (+ 1 (len pigeons)) 0)))
                                                (if lst (+ 1 (len lst)) 0)))
                   :verify-guards nil))))

(verify-termination flush-cand1-down-cand2 (declare (xargs :verify-guards nil)))
(verify-termination flush-candidates (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Merging induction candidates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination alists-agreep
  (declare (xargs :measure (if vars (+ 1 (len vars)) 0) :verify-guards nil)))
(verify-termination irreconcilable-alistsp
  (declare (xargs :measure (if alist1 (+ 1 (len alist1)) 0) :verify-guards nil)))
(verify-termination affinity (declare (xargs :verify-guards nil)))
(verify-termination member-affinity
  (declare (xargs :measure (if alist-lst (+ 1 (len alist-lst)) 0) :verify-guards nil)))
(verify-termination occur-affinity
  (declare (xargs :measure (if lst (+ 1 (len lst)) 0) :verify-guards nil)))
(verify-termination some-occur-affinity
  (declare (xargs :measure (if alists (+ 1 (len alists)) 0) :verify-guards nil)))
(verify-termination all-occur-affinity
  (declare (xargs :measure (if alists (+ 1 (len alists)) 0) :verify-guards nil)))
(verify-termination contains-affinity
  (declare (xargs :measure (if lst (+ 1 (len lst)) 0) :verify-guards nil)))
(verify-termination antagonistic-tests-and-alists-lstp
  (declare (xargs :measure (if lst (+ 1 (len lst)) 0) :verify-guards nil)))
(verify-termination antagonistic-tests-and-alists-lstsp
  (declare (xargs :measure (if lst1 (+ 1 (len lst1)) 0) :verify-guards nil)))
(verify-termination every-alist1-matedp
  (declare (xargs :measure (if lst1 (+ 1 (len lst1)) 0) :verify-guards nil)))
(verify-termination merge-alist1-into-alist2 (declare (xargs :verify-guards nil)))
(verify-termination merge-alist1-lst-into-alist2
  (declare (xargs :measure (if alist1-lst (+ 1 (len alist1-lst)) 0) :verify-guards nil)))
(verify-termination merge-lst1-into-alist2
  (declare (xargs :measure (if lst1 (+ 1 (len lst1)) 0) :verify-guards nil)))
(verify-termination merge-lst1-into-alist2-lst
  (declare (xargs :measure (if alist2-lst (+ 1 (len alist2-lst)) 0) :verify-guards nil)))
(verify-termination merge-lst1-into-lst2
  (declare (xargs :measure (if lst2 (+ 1 (len lst2)) 0) :verify-guards nil)))
(verify-termination merge-tests-and-alists-lsts (declare (xargs :verify-guards nil)))
(verify-termination merge-cand1-into-cand2 (declare (xargs :verify-guards nil)))
(verify-termination merge-candidates (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Mate and merge (m&m)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination intersectp-eq/union-equal (declare (xargs :verify-guards nil)))
(verify-termination equal/union-equal (declare (xargs :verify-guards nil)))
(verify-termination subsetp-equal/smaller (declare (xargs :verify-guards nil)))
(verify-termination m&m-apply (declare (xargs :verify-guards nil)))

(verify-termination count-off
  (declare (xargs :measure (if lst (+ 1 (len lst)) 0) :verify-guards nil)))

(verify-termination m&m-search
  (declare (xargs :measure (if y-lst (+ 1 (len y-lst)) 0) :verify-guards nil)))

;; The number of elements of PAIRS whose ids are not in DEL, that is, the
;; size of the "unprocessed bag" of m&m1.
(defund m&m-live-count (pairs del)
  (declare (xargs :measure (if pairs (+ 1 (len pairs)) 0)))
  (if (null pairs)
      0
    (+ (if (member (caar pairs) del) 0 1)
       (m&m-live-count (cdr pairs) del))))

(local
 (defthm m&m-live-count-of-cons-del-linear
   (<= (m&m-live-count pairs (cons id del))
       (m&m-live-count pairs del))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable m&m-live-count)))))

;; The id returned by m&m-search belongs to a live element of y-lst, so
;; deleting it decreases the live count.
(local
 (defthm m&m-live-count-of-cons-del-of-m&m-search
   (implies (mv-nth 0 (m&m-search x y-lst del fn))
            (< (m&m-live-count y-lst (cons (mv-nth 1 (m&m-search x y-lst del fn)) del))
               (m&m-live-count y-lst del)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (m&m-live-count m&m-search) (m&m-apply))))))

;; Each step of m&m1 either deletes a live element (perhaps replacing the
;; first element by a merge) or removes an element from PAIRS without
;; changing the live count.
(verify-termination m&m1
  (declare (xargs :measure (make-ord 1
                                     (+ 1 (m&m-live-count pairs del))
                                     (if pairs (+ 1 (len pairs)) 0))
                  :hints (("Goal" :in-theory (e/d (m&m-live-count)
                                                  (m&m-search m&m-apply))))
                  :verify-guards nil)))

(verify-termination m&m (declare (xargs :verify-guards nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Irrelevance elimination
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination pair-vars-with-lits
  (declare (xargs :measure (if cl (+ 1 (len cl)) 0) :verify-guards nil)))

(verify-termination all-variablep
  (declare (xargs :measure (if lst (+ 1 (len lst)) 0) :verify-guards nil)))

(verify-termination
  (ffnnames-subsetp (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))
                                    :verify-guards nil)))
  (ffnnames-subsetp-listp (declare (xargs :measure (+ (* 2 (acl2-count terms)) (if terms 2 0))
                                          :verify-guards nil))))

(verify-termination probably-not-validp (declare (xargs :verify-guards nil)))

(verify-termination irrelevant-lits
  (declare (xargs :measure (if alist (+ 1 (len alist)) 0) :verify-guards nil)))

(verify-termination eliminate-irrelevance-clause (declare (xargs :verify-guards nil)))
