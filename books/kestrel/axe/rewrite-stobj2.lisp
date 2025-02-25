; A stobj to gather parameters used in rewriting
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Unlike rewrite-stobj, this includes values that change during rewriting
;; (such as the DAG).  So rewrite-stobj2 has to be returned by the functions in
;; the main rewriter clique.

;; TODO: Consider adding more things to this, like the memoization, hit-counts,
;; tries, and limits.

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "wf-dagp")

(defstobj+ rewrite-stobj2
  ;; Functions that are known to be boolean in the current world:
  (dag-array :type t :initially nil) ; todo: strenghthen preds?
  (dag-len :type (satisfies natp) ; using (integer 0 *) led to guards and theorems that didn't mention natp
           :initially 0)
  (the-dag-parent-array :type t :initially nil)
  ;; we add "the-" to the names to avoid name clashes:
  (the-dag-constant-alist :type (satisfies dag-constant-alistp) :initially nil)
  (the-dag-variable-alist :type (satisfies dag-variable-alistp) :initially nil)
  :inline t
  :renaming ((dag-array get-dag-array)
             (update-dag-array put-dag-array)

             (dag-len get-dag-len)
             (update-dag-len put-dag-len)

             (the-dag-parent-array get-dag-parent-array)
             (update-the-dag-parent-array put-dag-parent-array)

             (the-dag-constant-alist get-dag-constant-alist)
             (update-the-dag-constant-alist put-dag-constant-alist)

             (the-dag-variable-alist get-dag-variable-alist)
             (update-the-dag-variable-alist put-dag-variable-alist)))

;; todo: use this more?
(defund wf-rewrite-stobj2 (rewrite-stobj2)
  (declare (xargs :stobjs rewrite-stobj2))
  (wf-dagp 'dag-array (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) 'dag-parent-array (get-dag-parent-array rewrite-stobj2) (get-dag-constant-alist rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2)))

(defthm wf-rewrite-stobj2-conjuncts
  (implies (and (wf-rewrite-stobj2 rewrite-stobj2)
                ;(rewrite-stobj2p rewrite-stobj2)
                )
           (and (pseudo-dag-arrayp 'dag-array (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2))
                (natp (get-dag-len rewrite-stobj2))
                (integerp (get-dag-len rewrite-stobj2))
                (dag-parent-arrayp 'dag-parent-array (get-dag-parent-array rewrite-stobj2))
                (bounded-dag-parent-arrayp 'dag-parent-array (get-dag-parent-array rewrite-stobj2)  (get-dag-len rewrite-stobj2))
                (equal (alen1 'dag-array (get-dag-array rewrite-stobj2))
                       (alen1 'dag-parent-array (get-dag-parent-array rewrite-stobj2)))
                (dag-variable-alistp (get-dag-variable-alist rewrite-stobj2))
                (bounded-dag-variable-alistp (get-dag-variable-alist rewrite-stobj2)
                                             (get-dag-len rewrite-stobj2))
                (dag-constant-alistp (get-dag-constant-alist rewrite-stobj2))
                (bounded-dag-constant-alistp (get-dag-constant-alist rewrite-stobj2)
                                             (get-dag-len rewrite-stobj2))))
  :hints (("Goal" :in-theory (enable wf-rewrite-stobj2))))

(theory-invariant (incompatible (:rewrite wf-rewrite-stobj2-conjuncts) (:definition wf-rewrite-stobj2)))

(defthm wf-rewrite-stobj2-conjuncts2
  (implies (and (wf-rewrite-stobj2 rewrite-stobj2)
                ;(rewrite-stobj2p rewrite-stobj2)
                )
           (and (<= (get-dag-len rewrite-stobj2) 1152921504606846974)
                (<= 0 (get-dag-len rewrite-stobj2))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (wf-rewrite-stobj2) (wf-rewrite-stobj2-conjuncts)))))

(defthm pseudo-dag-arrayp-of-get-dag-array-when-wf-rewrite-stobj2-gen
  (implies (and (wf-rewrite-stobj2 rewrite-stobj2)
                ;(rewrite-stobj2p rewrite-stobj2)
                (<= n (get-dag-len rewrite-stobj2))
                (natp n)
                )
           (pseudo-dag-arrayp 'dag-array (get-dag-array rewrite-stobj2) n))
  :hints (("Goal" :use (wf-rewrite-stobj2-conjuncts)
           :in-theory (disable wf-rewrite-stobj2-conjuncts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "dag-array-builders")

;; returns (mv erp nodenum rewrite-stobj2)
(defund add-variable-to-dag-array-in-stobj (var rewrite-stobj2)
  (declare (xargs :guard (and (symbolp var)
                              (wf-rewrite-stobj2 rewrite-stobj2))
                  :stobjs rewrite-stobj2))
  (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
    (add-variable-to-dag-array var (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) (get-dag-parent-array rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2))
    (if erp
        (mv erp 0 rewrite-stobj2)
      (let* ((rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2))
             (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
             (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
           ;; (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2))
             (rewrite-stobj2 (put-dag-variable-alist dag-variable-alist rewrite-stobj2)))
        (mv nil nodenum rewrite-stobj2)))))

(defthm add-variable-to-dag-array-in-stobj-return-type
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))) ; no error
                (symbolp var)
                (wf-rewrite-stobj2 rewrite-stobj2))
           (and (natp (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (wf-rewrite-stobj2 (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (< (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))
                   (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))
                (<= (get-dag-len rewrite-stobj2)
                    (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2) (natp wf-rewrite-stobj2-conjuncts)))))

(defthm add-variable-to-dag-array-in-stobj-return-type-2
  (implies (and; (not (mv-nth 0 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))) ; no error
                (symbolp var)
                ; (wf-rewrite-stobj2 rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2))
           (rewrite-stobj2p (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2) (natp wf-rewrite-stobj2-conjuncts)))))

;; a bit gross, as it makes a claim about a single component of the stobj.
;; but this helps to support some rewriter rules with very few hyps.
(defthm add-variable-to-dag-array-in-stobj-return-type-3
  (implies (natp (get-dag-len rewrite-stobj2))
           (natp (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2) (natp wf-rewrite-stobj2-conjuncts)))))


;; rule for (WF-DAGP 'DAG-ARRAY (GET-DAG-ARRAY REWRITE-STOBJ2) (GET-DAG-LEN REWRITE-STOBJ2) 'DAG-PARENT-ARRAY (GET-DAG-PARENT-ARRAY REWRITE-STOBJ2) (GET-DAG-CONSTANT-ALIST REWRITE-STOBJ2) (GET-DAG-VARIABLE-ALIST REWRITE-STOBJ2))
