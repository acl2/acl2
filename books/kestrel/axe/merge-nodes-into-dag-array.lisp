; Tools to merge DAG nodes into a DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "renaming-array")
(include-book "dag-array-builders")
(include-book "consecutivep")
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(defthmd natp-of-car-of-car-of-last-when-weak-dagp-aux
  (implies (and (weak-dagp-aux dag)
                (consp dag))
           (natp (car (car (last dag)))))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (disable strip-cdrs)))

;returns (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;variable names are shared between rev-dag-lst and dag-array
;fixme add args dag-array-name and dag-parent-array-name
;doesn't need to handle lambdas (they should never be in a dag and so shouldn't be in rev-dag-lst)
;what about ground terms?  calls to the evaluator?
;todo: compare to merge-embedded-dag-into-dag-array
(defund merge-nodes-into-dag-array (rev-dag-lst ;nodenums in ascending order
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                    renaming-array ;maps nodes already seen in rev-dag-lst to nodes in dag-array
                                    )
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (weak-dagp-aux rev-dag-lst)
                              (array1p 'renaming-array renaming-array)
                              (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop?
                              ;; have to know that the rev-dag-lst nodenums increase:
                              (if (consp rev-dag-lst)
                                  (and (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                                       (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len))
                                t)
                              (consecutivep (strip-cars rev-dag-lst)))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :expand (weak-dagp-aux rev-dag-lst)
                                 :in-theory (e/d (car-of-cadr-when-consecutivep-of-strip-cars strip-cars dag-exprp0)
                                                 ())))))
  (if (endp rev-dag-lst)
      (mv (erp-nil) renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let* ((entry (first rev-dag-lst))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (variablep expr)
          (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (add-variable-to-dag-array expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (if erp
                (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (merge-nodes-into-dag-array (rest rev-dag-lst)
                                          dag-array dag-len
                                          dag-parent-array dag-constant-alist dag-variable-alist
                                          (aset1 'renaming-array renaming-array nodenum new-nodenum))))
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn) ; note that the constant will be inlined when we handle the parents (no duplicate nodes should arise, be we call a proper dag-builder function on the parents)x
              (merge-nodes-into-dag-array (rest rev-dag-lst)
                                          dag-array dag-len
                                          dag-parent-array dag-constant-alist dag-variable-alist
                                          (aset1 'renaming-array renaming-array nodenum expr))
            ;;else, it's a regular function call:
            (let* ((args (dargs expr))
                   (renamed-args (rename-args args 'renaming-array renaming-array)))
              (mv-let (erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                (add-function-call-expr-to-dag-array2 fn renamed-args dag-array dag-len dag-parent-array dag-constant-alist)
                (if erp
                    (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                  (merge-nodes-into-dag-array (rest rev-dag-lst)
                                              dag-array dag-len
                                              dag-parent-array dag-constant-alist dag-variable-alist
                                              (aset1 'renaming-array renaming-array nodenum new-nodenum)))))))))))

(defthm wf-dagp-after-merge-nodes-into-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop or simplify?
                ;; have to know that the rev-dag-lst nodenums increase:
                (if (consp rev-dag-lst)
                    (and (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                         (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len))
                  t)
                (consecutivep (strip-cars rev-dag-lst)))
           (mv-let (erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
             (declare (ignore renaming-array erp))
             (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :induct (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
           ;; :do-not '(generalize eliminate-destructors)
           ;; :expand ((PSEUDO-DAGP-AUX REV-DAG-LST (+ -1 (LEN REV-DAG-LST))))
           :in-theory (e/d (MERGE-NODES-INTO-DAG-ARRAY ;caar-of-cdr-when-PSEUDO-DAGP-AUX
                            ;wf-dagp
                            caar-of-cdr-when-consecutivep-of-strip-cars
                            strip-cars
                            dag-exprp0)
                           (LEN-WHEN-PSEUDO-DAGP-AUX ;looped
                            pseudo-dag-arrayp)))))

(defthm alen1-of-mv-nth-1-of-merge-nodes-into-dag-array
  (implies (weak-dagp rev-dag-lst)
           (equal (alen1 'renaming-array (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
                  (alen1 'renaming-array renaming-array)))
  :hints (("Goal" :in-theory (enable merge-nodes-into-dag-array))))

(defthm natp-of-mv-nth-3-of-merge-nodes-into-dag-array
  (implies (natp dag-len)
           (natp (mv-nth 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable merge-nodes-into-dag-array))))

(defthm <=-of-mv-nth-3-of-merge-nodes-into-dag-array-linear
  (implies (natp dag-len)
           (<= dag-len (mv-nth 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable merge-nodes-into-dag-array))))

(defthm array1p-of-mv-nth-1-of-merge-nodes-into-dag-array
  (implies (and (weak-dagp rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (implies (consp rev-dag-lst)
                         (< (maxelem (strip-cars rev-dag-lst)) (alen1 'RENAMING-ARRAY RENAMING-ARRAY))))
           (array1p 'renaming-array (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :in-theory (enable merge-nodes-into-dag-array strip-cars))))

(defthm renaming-arrayp-aux-of-mv-nth-1-of-merge-nodes-into-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop?
                ;; have to know that the rev-dag-lst nodenums increase:
                (consp rev-dag-lst)
                (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
           (renaming-arrayp-aux 'renaming-array
                                (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                                (car (car (last rev-dag-lst)))))
  :hints (("Goal" :expand (RENAMING-ARRAYP-AUX 'RENAMING-ARRAY
                                               RENAMING-ARRAY (CAR (CAR REV-DAG-LST)))
           :in-theory (e/d (merge-nodes-into-dag-array strip-cars) (MYQUOTEP)))))


(defthm renaming-arrayp-aux-of-mv-nth-1-of-merge-nodes-into-dag-array-gen
  (implies (and (<= n (car (car (last rev-dag-lst))))
                (natp n)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop?
                ;; have to know that the rev-dag-lst nodenums increase:
                (consp rev-dag-lst) ;or else the call to last is meaningles
                (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
           (renaming-arrayp-aux 'renaming-array
                                (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                                n))
  :hints (("Goal" :use renaming-arrayp-aux-of-mv-nth-1-of-merge-nodes-into-dag-array
           :do-not-induct t
;           :expand (WEAK-DAGP-AUX REV-DAG-LST)
           :in-theory (e/d (natp-of-car-of-car-of-last-when-WEAK-DAGP-AUX) (renaming-arrayp-aux-of-mv-nth-1-of-merge-nodes-into-dag-array)) ;'(RENAMING-ARRAYP-AUX-MONOTONE)
           )))

(defthm bounded-renaming-entriesp-of-mv-nth-1-of-merge-nodes-into-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop?
                ;; have to know that the rev-dag-lst nodenums increase:
                (consp rev-dag-lst)
                (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
           (bounded-renaming-entriesp (car (car (last rev-dag-lst)))
                                      'renaming-array
                                      (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                                      (mv-nth 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :expand (RENAMING-ARRAYP-AUX 'RENAMING-ARRAY
                                               RENAMING-ARRAY (CAR (CAR REV-DAG-LST)))
           :in-theory (e/d (merge-nodes-into-dag-array strip-cars) (MYQUOTEP)))))

(defthm bounded-renaming-entriesp-of-mv-nth-1-of-merge-nodes-into-dag-array-gen
  (implies (and (<= n (car (car (last rev-dag-lst))))
                (natp n)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp-aux rev-dag-lst)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array)) ;drop?
                ;; have to know that the rev-dag-lst nodenums increase:
                (consp rev-dag-lst)
                (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
           (bounded-renaming-entriesp n
                                      'renaming-array
                                      (mv-nth 1 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                                      (mv-nth 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :use bounded-renaming-entriesp-of-mv-nth-1-of-merge-nodes-into-dag-array
           :in-theory (e/d (natp-of-car-of-car-of-last-when-WEAK-DAGP-AUX) (bounded-renaming-entriesp-of-mv-nth-1-of-merge-nodes-into-dag-array)))))

(defthm array1p-of-mv-nth-2-of-merge-nodes-into-dag-array
  (implies (and (weak-dagp rev-dag-lst)
                (array1p 'dag-array dag-array)
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
                (<= dag-len 2147483646)
                (natp dag-len))
           (array1p 'dag-array (mv-nth 2 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :in-theory (enable merge-nodes-into-dag-array))))

(defthm pseudo-dag-arrayp-of-mv-nth-2-of-merge-nodes-into-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (weak-dagp rev-dag-lst)
                (ARRAY1P 'RENAMING-ARRAY RENAMING-ARRAY)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array))
                (if (consp rev-dag-lst)
                    (and (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                         (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len)
                         )
                  t)
                (consecutivep (strip-cars rev-dag-lst))
                ;; no error:
                (not (mv-nth 0 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
           (pseudo-dag-arrayp 'dag-array
                              (mv-nth 2 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                              (mv-nth 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :induct t
           :in-theory (e/d (merge-nodes-into-dag-array BOUNDED-RENAMING-ENTRIESP-OF-ASET1-SPECIAL-GEN CAAR-OF-CDR-WHEN-CONSECUTIVEP-OF-STRIP-CARS
                                                       weak-dagp ;why?
                                                       )
                           (myquotep)))))

;drop?
(defthm merge-nodes-into-dag-array-bound-lemma
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (<= dag-len 2147483646)
                (bounded-dag-constant-alistp dag-constant-alist dag-len)
                (bounded-dag-variable-alistp dag-variable-alist dag-len)
                (consecutivep (strip-cars rev-dag-lst))
                (weak-dagp-aux rev-dag-lst)
                (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (array1p 'renaming-array renaming-array)
                (all-< (strip-cars rev-dag-lst) (alen1 'renaming-array renaming-array))
                (if (consp rev-dag-lst)
                    (and (renaming-arrayp-aux 'renaming-array renaming-array (+ -1 (car (car rev-dag-lst))))
                         (bounded-renaming-entriesp (+ -1 (car (car rev-dag-lst))) 'renaming-array renaming-array dag-len))
                  t)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array)))
           (<=
            (MV-NTH 3 (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
            (alen1
              'DAG-ARRAY
              (MV-NTH
               2
               (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))))
  :hints (("Goal" :induct (merge-nodes-into-dag-array rev-dag-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
           :do-not '(generalize eliminate-destructors)
           :expand ((PSEUDO-DAGP-AUX REV-DAG-LST (+ -1 (LEN REV-DAG-LST))))
           :in-theory (e/d (MERGE-NODES-INTO-DAG-ARRAY ;caar-of-cdr-when-PSEUDO-DAGP-AUX
                            caar-of-cdr-when-consecutivep-of-strip-cars
                            strip-cars
                            dag-exprp0)
                           (LEN-WHEN-PSEUDO-DAGP-AUX ;looped
                            pseudo-dag-arrayp)))))
