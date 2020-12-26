; Utilities for dealing with clauses represented as DAGs
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

(include-book "dag-arrays")
(include-book "contexts")
(include-book "kestrel/utilities/forms" :dir :system)

;nodenums are the disjuncts, and we are trying to prove at least one of them true
;it can help to think about the case where they are all false, to see what is contradictory
;fixme add the ability to read the output of this back in and apply the prover to it
;fixme make tail rec (could just print each one instead of consing up the list..)
(defund expressions-for-this-case (items dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (possibly-negated-nodenumsp items)
                              (all-< (strip-nots-from-possibly-negated-nodenums items)
                                     dag-len))
                  :guard-hints (("Goal" :expand ((possibly-negated-nodenumsp items))
                                 :in-theory (enable strip-not-from-possibly-negated-nodenum
                                                    strip-nots-from-possibly-negated-nodenums
                                                    DAG-FUNCTION-CALL-EXPRP-REDEF)))))
  (if (endp items)
      nil
    (let* ((item (first items)))
      (if (consp item)       ;;it's negated (TODO: Handle double negation?)
          (cons (farg1 item) ;strip the not
                (expressions-for-this-case (cdr items) dag-array dag-len))
        (let ((expr (aref1 'dag-array dag-array item)))
          (if (and (consp expr)
                   (eq 'not (ffn-symb expr))
                   (consp (dargs expr)) ;for guards
                   )
              (cons (first (dargs expr))
                    (expressions-for-this-case (cdr items) dag-array dag-len))
            (cons `(not ,item)
                  (expressions-for-this-case (cdr items) dag-array dag-len))))))))

;; in this version, the items are all nodenums.  todo: drop the version just above?
(defund expressions-for-this-case-simple (items dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp items)
                              (all-< items dag-len))
                  :guard-hints (("Goal" :expand ((possibly-negated-nodenumsp items))
                                 :in-theory (enable strip-not-from-possibly-negated-nodenum
                                                    strip-nots-from-possibly-negated-nodenums
                                                    DAG-FUNCTION-CALL-EXPRP-REDEF)))))
  (if (endp items)
      nil
    (let* ((item (first items)))
      (let ((expr (aref1 'dag-array dag-array item)))
        (if (and (consp expr)
                 (eq 'not (ffn-symb expr))
                 (consp (dargs expr)) ;for guards
                 )
            ;; if the item is a NOT, negate it by stripping the NOT:
            (cons (first (dargs expr))
                  (expressions-for-this-case (cdr items) dag-array dag-len))
          ;; if the item isn't a NOT, negate it by adding a NOT:
          (cons `(not ,item)
                (expressions-for-this-case (cdr items) dag-array dag-len)))))))

;any non-nil constant proves the clause (we are proving a disjunction), any nil is dropped (because (or nil x) = x)
;;returns (mv provedp remaining-disjunct-nodenums)
;is there another version of this?  See get-axe-disjunction-from-dag-items.
;todo: give this a better name
;; TODO: Should we remove duplicate disjuncts too?
;; TODO: Deprecate! (Why?)
;; Also used in prover.lisp
(defund handle-constant-disjuncts (disjuncts acc)
  (declare (xargs :guard (and (true-listp disjuncts)
                              (all-dargp disjuncts)
                              (true-listp acc))))
  (if (endp disjuncts)
      (mv nil (reverse acc)) ;todo: maybe drop the reverse
    (let ((disjunct (first disjuncts)))
      (if (consp disjunct)
          ;; it's a quotep:
          (if (unquote disjunct)
              ;; A disjunct that is a non-nil constant proves the disjunction:
              (mv t nil) ;second RV is irrelevant
            ;; Drop the nil disjunct:
            (handle-constant-disjuncts (rest disjuncts) acc))
        ;; it's a nodenum:
        (handle-constant-disjuncts (rest disjuncts) (cons disjunct acc))))))

(defthm all-<-of-mv-nth-1-of-handle-constant-disjuncts
  (implies (and (all-dargp-less-than disjuncts bound)
                (all-< acc bound))
           (all-< (mv-nth 1 (handle-constant-disjuncts disjuncts acc)) bound))
  :hints (("Goal" :in-theory (enable handle-constant-disjuncts))))

(defthm nat-listp-of-mv-nth-1-of-handle-constant-disjuncts
  (implies (and (all-dargp-less-than disjuncts bound)
                (nat-listp acc))
           (nat-listp (mv-nth 1 (handle-constant-disjuncts disjuncts acc))))
  :hints (("Goal" :in-theory (enable handle-constant-disjuncts))))

(defthm true-listp-of-mv-nth-1-of-handle-constant-disjuncts
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (handle-constant-disjuncts disjuncts acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable handle-constant-disjuncts))))
