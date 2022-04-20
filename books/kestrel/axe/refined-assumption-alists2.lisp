; Extending a refined-assumption-alist
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "refined-assumption-alists")
(include-book "conjunctions-and-disjunctions")
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable natp REFINED-ASSUMPTION-ALISTP)))

(defthm all-dargp-of-dargs-when-possibly-negated-nodenump
  (implies (and (possibly-negated-nodenump possibly-negated-nodenum)
                ;;(consp possibly-negated-nodenum)
                )
           (all-dargp (dargs possibly-negated-nodenum)))
  :hints (("Goal" :expand ((all-dargp (cdr possibly-negated-nodenum))
                           (all-dargp (cddr possibly-negated-nodenum)))
           :in-theory (enable possibly-negated-nodenump
                              dargs
                              all-dargp))))

(defthm dag-exprp-when-possibly-negated-nodenumsp
  (implies (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                (consp possibly-negated-nodenums)
                (consp (first possibly-negated-nodenums))
                )
           (dag-exprp (first possibly-negated-nodenums)))
  :hints (("Goal" :expand ((all-dargp (cdr possibly-negated-nodenum))
                           (all-dargp (cddr possibly-negated-nodenum)))
           :in-theory (enable possibly-negated-nodenump
                              dargs
                              all-dargp
                              DAG-EXPRP))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extract suitable function call exprs from the possibly-negated-nodenums
(defund dag-function-call-exprs-from-possibly-negated-nodenums (possibly-negated-nodenums dag-array dag-len)
  (declare (xargs :guard (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                                     dag-len))
                  :guard-hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                                           possibly-negated-nodenump)
                                 :expand ((possibly-negated-nodenumsp possibly-negated-nodenums))))))
  (if (endp possibly-negated-nodenums)
      nil
    (let ((pnn (first possibly-negated-nodenums)))
      (if (consp pnn) ; tests for a call of not
          (cons pnn   ; the pnn itself is a suitable expr
                (dag-function-call-exprs-from-possibly-negated-nodenums (rest possibly-negated-nodenums) dag-array dag-len))
        ;; pnn is a nodenum:
        (let ((expr (aref1 'dag-array dag-array pnn)))
          (if (atom expr)
              (prog2$ (cw "Warning: Variable assumption, ~x0, encountered.~%" expr) ;skip it
                      (dag-function-call-exprs-from-possibly-negated-nodenums (rest possibly-negated-nodenums) dag-array dag-len))
            (if (quotep expr)
                (prog2$ (cw "Warning: Constant assumption, ~x0, encountered.~%" expr) ;skip it
                        (dag-function-call-exprs-from-possibly-negated-nodenums (rest possibly-negated-nodenums) dag-array dag-len))
              ;; No need to extract conjuncts, because that was done when the possibly-negated-nodenums were created
              (cons expr ; the expr is suitable
                    (dag-function-call-exprs-from-possibly-negated-nodenums (rest possibly-negated-nodenums) dag-array dag-len)))))))))

(defthm all-dag-function-call-exprp-of-dag-function-call-exprs-from-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len))
           (all-dag-function-call-exprp (dag-function-call-exprs-from-possibly-negated-nodenums
                                         possibly-negated-nodenums
                                         dag-array dag-len)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenump
                                     DAG-FUNCTION-CALL-EXPRS-FROM-POSSIBLY-NEGATED-NODENUMS)
           :expand ((possibly-negated-nodenumsp possibly-negated-nodenums)))))

(defthm bounded-dag-expr-listp-of-dag-function-call-exprs-from-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len))
           (bounded-dag-expr-listp dag-len
                                  (dag-function-call-exprs-from-possibly-negated-nodenums
                                   possibly-negated-nodenums
                                   dag-array dag-len)))
  :hints (("Goal" :in-theory (enable strip-nots-from-possibly-negated-nodenums
                                     possibly-negated-nodenump
                                     DAG-FUNCTION-CALL-EXPRS-FROM-POSSIBLY-NEGATED-NODENUMS
                                     STRIP-NOT-FROM-POSSIBLY-NEGATED-NODENUM
                                     BOUNDED-DAG-EXPRP)
           :expand ((possibly-negated-nodenumsp possibly-negated-nodenums)
                    (DARGS (CAR POSSIBLY-NEGATED-NODENUMS))
                    (BOUNDED-DARG-LISTP (CDR (CAR POSSIBLY-NEGATED-NODENUMS))
                                         DAG-LEN)
                    (BOUNDED-DARG-LISTP (CDDR (CAR POSSIBLY-NEGATED-NODENUMS))
                                         DAG-LEN)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing by doing things more directly
(defund extend-refined-assumption-alist-with-possibly-negated-nodenums (possibly-negated-nodenums refined-assumption-alist dag-array dag-len)
  (declare (xargs :guard (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                              (refined-assumption-alistp refined-assumption-alist)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                                     dag-len))))
  (let ((exprs (dag-function-call-exprs-from-possibly-negated-nodenums possibly-negated-nodenums dag-array dag-len)))
    (extend-refined-assumption-alist exprs refined-assumption-alist)))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist-with-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                (refined-assumption-alistp refined-assumption-alist)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len))
           (refined-assumption-alistp (extend-refined-assumption-alist-with-possibly-negated-nodenums possibly-negated-nodenums refined-assumption-alist dag-array dag-len)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-with-possibly-negated-nodenums))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-with-possibly-negated-nodenums
  (implies (and (possibly-negated-nodenumsp possibly-negated-nodenums)
                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist-with-possibly-negated-nodenums possibly-negated-nodenums refined-assumption-alist dag-array dag-len)
                                              dag-len))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-with-possibly-negated-nodenums))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing by doing things more directly
(defund extend-refined-assumption-alist-assuming-node (refined-assumption-alist nodenum dag-array dag-len)
  (declare (xargs :guard (and (refined-assumption-alistp refined-assumption-alist)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len))))
  (let ((conjunction (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len)))
    (if (quotep conjunction)
        (prog2$ (cw "Warning: Constant assumption, ~x0, encountered.~%" conjunction)
                refined-assumption-alist)
      (extend-refined-assumption-alist-with-possibly-negated-nodenums conjunction refined-assumption-alist dag-array dag-len))))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-node
  (implies (and (refined-assumption-alistp refined-assumption-alist)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (refined-assumption-alistp (extend-refined-assumption-alist-assuming-node refined-assumption-alist nodenum dag-array dag-len)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-assuming-node))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-node
  (implies (and (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist-assuming-node refined-assumption-alist nodenum dag-array dag-len)
                                              dag-len))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-assuming-node))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-node-gen
  (implies (and (<= dag-len bound)
                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist-assuming-node refined-assumption-alist nodenum dag-array dag-len)
                                              bound))
  :hints (("Goal" :use bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-node
           :in-theory (disable bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-node))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing by doing things more directly
(defund extend-refined-assumption-alist-assuming-negation-of-node (refined-assumption-alist nodenum dag-array dag-len)
  (declare (xargs :guard (and (refined-assumption-alistp refined-assumption-alist)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable negate-axe-disjunction)))
                  ))
  (let* ((disjunction (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len)) ; assume (not (or a b c)) by assuming (not a), etc.
         (conjunction (negate-axe-disjunction disjunction)))
    (if (quotep conjunction)
        (prog2$ (cw "Warning: Constant assumption, ~x0, encountered.~%" conjunction)
                refined-assumption-alist)
      (extend-refined-assumption-alist-with-possibly-negated-nodenums conjunction refined-assumption-alist dag-array dag-len))))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-negation-of-node
  (implies (and (refined-assumption-alistp refined-assumption-alist)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (refined-assumption-alistp (extend-refined-assumption-alist-assuming-negation-of-node refined-assumption-alist nodenum dag-array dag-len)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-assuming-negation-of-node
                                     all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-conjunctionp))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-negation-of-node
  (implies (and (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist-assuming-negation-of-node refined-assumption-alist nodenum dag-array dag-len)
                                              dag-len))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist-assuming-negation-of-node
                                     all-<-of-strip-nots-from-possibly-negated-nodenums-when-bounded-axe-conjunctionp))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-negation-of-node-gen
  (implies (and (<= dag-len bound)
                (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist-assuming-negation-of-node refined-assumption-alist nodenum dag-array dag-len)
                                              bound))
  :hints (("Goal" :use bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-negation-of-node
           :in-theory (disable bounded-refined-assumption-alistp-of-extend-refined-assumption-alist-assuming-negation-of-node))))
