; Converting DAGs to terms
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

;; A utility for converting DAGs (not dag-arrays) to terms.
;; See also dag-to-term-with-lets.lisp and dag-to-term-with-lets-simple.lisp.

(include-book "dags")
(include-book "dag-arrays") ;for greatest-nodenum-in-list (factor out?)

(defun dag-walker-measure-for-item (nodenum-or-quotep)
  (make-ord 1
            (if (consp nodenum-or-quotep)   ;check for quotep
                1                           ;ordinal coeff must be positive
              (+ 2 (nfix nodenum-or-quotep))) ;add 2 to make this greater than in the other branch (necesary?)
            0))

(defun dag-walker-measure-for-items (nodenum-or-quoteps)
  (make-ord 1
            (+ 2 (greatest-nodenum-in-list nodenum-or-quoteps)) ;add 2 because it might be -1 and ordinal coeffs must be positive
            (len nodenum-or-quoteps)))

;we could of course make a faster version using arrays or memoization, but if this
;blow up, whatever we do with the resulting term will likely blow up too.
;; This could be a model for proving termination of functions over DAGS.
;; Either the nodenum being manipulated (or the max nodenum in the list) goes
;; down, or the list gets shorter.
;; TODO: When doing the lookups, consider discarding any nodes passed by.
(mutual-recursion
 ;;doesn't use arrays or anything
 (defun dag-to-term-aux (nodenum-or-quotep dag)
   (declare (xargs :guard (and (weak-dagp dag)
                               (or (myquotep nodenum-or-quotep)
                                   (and (natp nodenum-or-quotep)
                                        (<= nodenum-or-quotep (top-nodenum dag)))))
                   :guard-hints (("Goal" ;:expand ((ALL-DARGP-LESS-THAN NODENUM-OR-QUOTEPS (CAR (CAR DAG))))
                                  :in-theory (enable DARGP-LESS-THAN)))
                   :measure (dag-walker-measure-for-item nodenum-or-quotep)))
   (if (consp nodenum-or-quotep) ;check for quotep
       nodenum-or-quotep
     (and (mbt (natp nodenum-or-quotep)) ;for termination ;drop somehow?
          (let ((expr (lookup nodenum-or-quotep dag)))
            (if (or (variablep expr)
                    (quotep expr))
                expr
              ;;function call
              (let ((args (dargs expr)))
                (if (not (mbt (all-dargp-less-than args nodenum-or-quotep)))
                    (er hard 'dag-to-term-aux "Child not less than parent: ~x0" expr)
                  (cons (ffn-symb expr)
                        (dag-to-term-aux-lst args dag)))))))))

 (defun dag-to-term-aux-lst (nodenum-or-quoteps dag)
   (declare (xargs :guard (and (weak-dagp dag)
                               (true-listp nodenum-or-quoteps)
                               ;;(all-dargp nodenum-or-quoteps)
                               (all-dargp-less-than nodenum-or-quoteps (top-nodenum dag))
                               )
                   :measure (dag-walker-measure-for-items nodenum-or-quoteps)))

   (if (endp nodenum-or-quoteps)
       nil
     (cons (dag-to-term-aux (car nodenum-or-quoteps) dag)
           (dag-to-term-aux-lst (cdr nodenum-or-quoteps) dag)))))

(make-flag dag-to-term-aux)

(defthm-flag-dag-to-term-aux
  (defthm pseudo-termp-of-dag-to-term-aux
    (implies (and (pseudo-dagp dag)
                  (or (myquotep nodenum-or-quotep)
                      (and (natp nodenum-or-quotep)
                           (<= nodenum-or-quotep (top-nodenum dag)))))
             (pseudo-termp (dag-to-term-aux nodenum-or-quotep dag)))
    :flag dag-to-term-aux)
  (defthm pseudo-term-listp-of-dag-to-term-aux-lst
    (implies (and (pseudo-dagp dag)
                  (true-listp nodenum-or-quoteps)
                  (all-dargp-less-than nodenum-or-quoteps (top-nodenum dag)))
             (pseudo-term-listp (dag-to-term-aux-lst nodenum-or-quoteps dag)))
    :flag dag-to-term-aux-lst)
  :hints (("subgoal *1/2" :use (:instance dag-exprp0-of-lookup-equal-when-pseudo-dagp
                                          (n nodenum-or-quotep)
                                          )
           :in-theory (disable dag-exprp0-of-lookup-equal-when-pseudo-dagp
                               dag-exprp0-of-lookup-equal-when-weak-dagp-aux
                               dag-exprp0-of-lookup-equal-when-weak-dagp
                               dag-exprp-of-lookup-equal-when-pseudo-dagp))
          ("Goal" :in-theory (e/d (symbolp-when-dag-exprp0) (weak-dagp-aux
                                                             bounded-dag-exprp
                                                             ;;myquotep
                                                             ;;quotep
                                                             )))))

;; Convert DAG to an equivalent term. Of course, this can blow up exponentially
;; if there is a lot of sharing in DAG. Another option to convert a dag to a
;; term would be to quote the dag and pass it to the Axe evaluator.
(defund dag-to-term (dag)
  (declare (xargs :guard (or (weak-dagp dag)
                             (quotep dag))
                  :guard-hints (("Goal" :in-theory (e/d (WEAK-DAGP-AUX) ())))))
  (if (quotep dag)
      dag
    (dag-to-term-aux (top-nodenum dag) dag)))

;; This version avoids imposing invariant-risk on callers, because it has a guard of t.
(defund dag-to-term-unguarded (dag)
  (declare (xargs :guard t))
  (if (or (weak-dagp dag)
          (quotep dag))
      (dag-to-term dag)
    (er hard? 'dag-to-term-unguarded "Bad input: ~x0" dag)))

(defthm pseudo-termp-of-dag-to-term
  (implies (pseudo-dagp dag)
           (pseudo-termp (dag-to-term dag)))
  :hints (("Goal" :in-theory (enable dag-to-term))))

;; (defun dags-to-terms (dags)
;;   (if (endp dags)
;;       nil
;;     (cons (dag-to-term (first dags))
;;           (dags-to-terms (rest dags)))))
