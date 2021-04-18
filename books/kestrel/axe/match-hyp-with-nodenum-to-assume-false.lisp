; Supporting utilities for the Axe Prover(s)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unify-tree-and-dag")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; Returns :fail (meaning failure to match) or an alist binding the free vars in HYP.
;; hyp is a tree with leaves that are quoteps, nodenums (from vars already bound), and free vars.
;; the alist returned maps variables to nodenums or quoteps
;; TODO: Take an alist to extend, but i suppose that might make lookups in unify-tree-with-dag-node slower?  could pass it 2 alists, once to extend and one to use?
(defund match-hyp-with-nodenum-to-assume-false (hyp nodenum-to-assume-false dag-array dag-len)
  (declare (xargs :guard (and (axe-treep hyp)
                              (consp hyp)
                              (not (equal 'quote (ffn-symb hyp)))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum-to-assume-false)
                              (< nodenum-to-assume-false dag-len))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0))))
           (ignore dag-len) ;todo
           )
  (if (and (eq 'not (ffn-symb hyp)) ;; TODO: Avoid checking this over and over for each nodenum-to-assume-false
           (consp (fargs hyp)) ; for the guard proof, should always be true if arities are right.
           (endp (cdr (fargs hyp))) ; needed for the proof that all free vars get bound, should always be true if arities are right.
           )
      ;; If hyp is of the form (not <x>) then try to match <x> with the nodenum-to-assume-false:
      ;; TODO: what if hyp is of the form (equal .. nil) or (equal nil ..)?
      ;; TODO: Consider a fast matcher that fails fast (without consing) if the skeleton is wrong, like we do for matching terms with dags:
      (unify-tree-with-dag-node (farg1 hyp) nodenum-to-assume-false dag-array nil)
    ;;otherwise we require the expr assumed false to be a call of NOT, and we try to match HYP with the argument of the NOT
    (let ((expr-to-assume-false (aref1 'dag-array dag-array nodenum-to-assume-false))) ;could do this at a shallower level?
      (if (and (call-of 'not expr-to-assume-false)
               (consp (dargs expr-to-assume-false)) ; for the guard proof, should always be true if arities are right (we could, at least, check the arities of NOTs)
               )
          (let ((arg-to-assume (darg1 expr-to-assume-false)))
            (if (consp arg-to-assume) ;whoa, it's a constant! ;TODO: This may be impossible
                :fail
              ;; TODO: Consider a fast matcher that fails fast (without consing) if the skeleton is wrong, like we do for matching terms with dags:
              (unify-tree-with-dag-node hyp arg-to-assume dag-array nil)))
        :fail))))

(defthm symbol-alistp-of-match-hyp-with-nodenum-to-assume-false
  (implies (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
           (symbol-alistp (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
  :hints (("Goal" :in-theory (enable match-hyp-with-nodenum-to-assume-false))))

(local
 (defthm true-listp-when-alistp
   (implies (alistp x)
            (true-listp x))))

(defthm true-listp-of-match-hyp-with-nodenum-to-assume-false
  (implies (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
           (true-listp (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
  :hints (("Goal" :in-theory (enable match-hyp-with-nodenum-to-assume-false))))

(defthm true-listp-of-match-hyp-with-nodenum-to-assume-false-type
  (or (symbolp (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))
      (true-listp (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable match-hyp-with-nodenum-to-assume-false))))

(defthm all-dargp-of-match-hyp-with-nodenum-to-assume-false
  (implies (and (axe-treep hyp)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum-to-assume-false)
                (< nodenum-to-assume-false dag-len)
                (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))))
           (all-dargp (strip-cdrs (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (match-hyp-with-nodenum-to-assume-false car-becomes-nth-of-0 NATP-OF-+-OF-1)
                                  (natp)))))

(defthm all-dargp-less-than-of-match-hyp-with-nodenum-to-assume-false
  (implies (and (axe-treep hyp)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum-to-assume-false)
                (< nodenum-to-assume-false dag-len)
                (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))))
           (all-dargp-less-than (strip-cdrs (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len)) dag-len))
  :hints (("Goal" :in-theory (e/d (match-hyp-with-nodenum-to-assume-false car-becomes-nth-of-0 NATP-OF-+-OF-1)
                                  (natp)))))

;; All the free vars get bound
(defthm match-hyp-with-nodenum-to-assume-false-binds-all-vars
  (implies (and (axe-treep hyp)
                (consp hyp)
                (not (equal 'quote (ffn-symb hyp)))
                (symbol-alistp alist)
                (not (equal :fail (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))))
           (subsetp-equal (axe-tree-vars hyp)
                          (strip-cars (match-hyp-with-nodenum-to-assume-false hyp nodenum-to-assume-false dag-array dag-len))))
  :hints (("Goal" :in-theory (e/d (match-hyp-with-nodenum-to-assume-false) (unify-tree-with-dag-node-binds-all-vars))
           :expand ((axe-tree-vars hyp)
                    (axe-tree-vars-lst (cdr hyp)))
           :use ((:instance unify-tree-with-dag-node-binds-all-vars
                            (alist nil)
                            (tree (cadr hyp))
                            (nodenum-or-quotep nodenum-to-assume-false))
                 (:instance unify-tree-with-dag-node-binds-all-vars
                            (tree hyp)
                            (alist nil)
                            (nodenum-or-quotep (nth 0
                                                    (dargs (aref1 'dag-array
                                                                  dag-array nodenum-to-assume-false)))))))))
