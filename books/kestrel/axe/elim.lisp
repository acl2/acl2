; Support for the Axe Prover tuple elimination
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
(include-book "dag-variable-alist")
(include-book "worklists")
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

;dup in prove-with-stp
(defthm assoc-equal-when-member-equal-of-strip-cars
  (implies (and (member-equal key (strip-cars alist))
                (or key (alistp alist)))
           (assoc-equal key alist))
  :hints
  (("Goal" :in-theory (e/d (member-equal assoc-equal strip-cars alistp) nil))))

(defund get-var-length-alist-for-tuple-elimination (nodenums-to-assume-false dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (true-listp nodenums-to-assume-false)
                              (all-natp nodenums-to-assume-false)
                              (all-< nodenums-to-assume-false dag-len))
                  :guard-hints (("Goal" :in-theory (e/d () (PSEUDO-DAG-ARRAYP))))))
  (if (endp nodenums-to-assume-false)
      acc
    (let* ((nodenum (first nodenums-to-assume-false))
           (not-expr (aref1 'dag-array dag-array nodenum))
           (acc (if (and (consp not-expr)
                         (eq 'not (ffn-symb not-expr))
                         (= 1 (len (dargs not-expr)))
                         (not (consp (darg1 not-expr))))
                    (let ((expr (aref1 'dag-array dag-array (darg1 not-expr))))
                      (if (and (call-of 'equal expr)
                               (= 2 (len (dargs expr)))
                               (quotep (darg1 expr))
                               ;;allow 0?:
                               (posp (unquote (darg1 expr)))
                               (< (unquote (darg1 expr)) 50) ;fffixme had 40, but that was too small for the cbc proof (think more about this..)
                               (not (consp (darg2 expr)))
                               )
                          (let ((possible-len-of-var (aref1 'dag-array dag-array (darg2 expr))))
                            (if (and (consp possible-len-of-var)
                                     (eq 'len (ffn-symb possible-len-of-var))
                                     (= 1 (len (dargs possible-len-of-var)))
                                     (not (consp (darg1 possible-len-of-var))))
                                (let ((possible-var (aref1 'dag-array dag-array (darg1 possible-len-of-var))))
                                  (if (symbolp possible-var)
                                      (acons-fast possible-var (unquote (darg1 expr)) acc)
                                    acc))
                              acc))
                        acc))
                  acc)))
      (get-var-length-alist-for-tuple-elimination (cdr nodenums-to-assume-false) dag-array dag-len acc))))

(defthm symbol-alistp-of-get-var-length-alist-for-tuple-elimination
  (equal (symbol-alistp (get-var-length-alist-for-tuple-elimination nodenums-to-assume-false dag-array dag-len acc))
         (symbol-alistp acc))
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

(defthm symbol-alistp-of-get-var-length-alist-for-tuple-elimination-type
  (implies (symbol-alistp acc)
           (symbol-alistp (get-var-length-alist-for-tuple-elimination nodenums-to-assume-false dag-array dag-len acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

(defthm acl2-number-of-lookup-equal-when-all-natp-of-strip-cdrs
  (implies (all-natp (strip-cdrs acc))
           (iff (acl2-numberp (lookup-equal var acc))
                (member-equal var (strip-cars acc))))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal strip-cars member-equal))))

(defthm acl2-numberp-of-lookup-equal-of-get-var-length-alist-for-tuple-elimination
  (implies (all-natp (strip-cdrs acc))
           (iff (acl2-numberp (lookup-equal var (get-var-length-alist-for-tuple-elimination literal-nodenums dag-array dag-len acc)))
                (member-equal var (strip-cars (get-var-length-alist-for-tuple-elimination literal-nodenums dag-array dag-len acc)))))
  :hints (("Goal" :in-theory (enable get-var-length-alist-for-tuple-elimination))))

;explores worklist and all supporting nodes
;any node that is a parent of NODENUM and whose fn is not among FNS causes this to return nil
;fixme stop once we hit a nodenum smaller than NODENUM?
(defund nodenum-only-appears-in (worklist dag-array dag-len nodenum fns done-array)
  (declare (xargs ;; The measure is, first the number of unhandled nodes, then, if unchanged, check the length of the worklist.
            :measure (make-ord 1
                               (+ 1 ;coeff must be positive
                                  (if (not (natp (alen1 'done-array done-array)))
                                      0
                                    (+ 1 (- (alen1 'done-array done-array)
                                            (num-handled-nodes 'done-array done-array)))))
                               (len worklist))
            :guard (and (nat-listp worklist)
                        (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                        (array1p 'done-array done-array)
                        (all-< worklist (alen1 'done-array done-array))
                        (all-< worklist dag-len)
                        (true-listp fns)
                        (natp nodenum))))
  (if (or (endp worklist)
          (not (mbt (array1p 'done-array done-array)))
          (not (mbt (nat-listp worklist)))
          (not (mbt (all-< worklist (alen1 'done-array done-array)))))
      t
    (let* ((possible-parent-nodenum (first worklist)))
      (if (aref1 'done-array done-array possible-parent-nodenum)
          ;;this node has already been checked:
          (nodenum-only-appears-in (rest worklist) dag-array dag-len nodenum fns done-array)
        (let ((expr (aref1 'dag-array dag-array possible-parent-nodenum)))
          (if (or (variablep expr)
                  (fquotep expr))
              ;;it's a variable or quoted constant, so it's not a parent of nodenum
              (nodenum-only-appears-in (rest worklist) dag-array dag-len nodenum fns
                                       (aset1 'done-array done-array possible-parent-nodenum t))
            ;;function call:
            (if (and (member nodenum (dargs expr)) ;fixme check that the appearance is kosher (e.g., second arg of nth where the first arg is a constant in the right range?  what do we have to have for soundness?)
                     (not (member-eq (ffn-symb expr) fns)))
                nil
;check the children:
              (nodenum-only-appears-in (append-atoms (dargs expr) (rest worklist))
                                       dag-array dag-len nodenum fns
                                       (aset1 'done-array done-array possible-parent-nodenum t)))))))))



(local (in-theory (disable STRIP-CARS)))

(defthm assoc-equal-when-subsetp-equal-of-strip-cars
  (implies (and (subsetp-equal keys (strip-cars alist))
                (member-equal key keys)
                (alistp alist))
           (assoc-equal key alist))
  :hints (("Goal" :in-theory (enable ;ASSOC-EQUAL-IFF
                              strip-cars memberp subsetp-equal))))

;returns a var to elim, or nil to indicate failure to find one
;fixme don't re-search the literals for each var...
;fixme can't use the parent-array because that may include parents that are not used by any literals?
(defund var-okay-to-elim (vars dag-array dag-len dag-variable-alist literal-nodenums)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-variable-alistp dag-variable-alist dag-len)
                              (subsetp-equal vars (strip-cars dag-variable-alist))
                              (nat-listp literal-nodenums)
                              (consp literal-nodenums)
                              (all-< literal-nodenums dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (;integerp-of-maxelem-when-all-integerp
                                                         natp-of-lookup-equal-when-dag-variable-alistp)
                                                        (natp))))))
  (if (endp vars)
      nil
    (let* ((var (first vars))
           (nodenum (lookup-eq-safe var dag-variable-alist))
           (max-literal-nodenum (maxelem literal-nodenums))
           )
      (if (nodenum-only-appears-in literal-nodenums dag-array dag-len nodenum '(nth true-listp len)
                                   (make-empty-array 'done-array (+ 1 max-literal-nodenum))
                                   ) ;fffixme make sure the nths are always of constants..
          var
        (var-okay-to-elim (rest vars) dag-array dag-len dag-variable-alist literal-nodenums)))))

;may be nil, which is a symbol
(defthm symbolp-of-var-okay-to-elim
  (implies (symbol-listp vars)
           (symbolp (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)))
  :hints (("Goal" :in-theory (enable var-okay-to-elim))))

(defthm member-equal-of-var-okay-to-elim
  (implies (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
           (member-equal (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums) vars))
  :hints (("Goal" :in-theory (enable var-okay-to-elim))))

(defthm member-equal-of-var-okay-to-elim-gen
  (implies (and (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
                (subsetp-equal vars vars2))
           (member-equal (var-okay-to-elim vars dag-array dag-len dag-variable-alist literal-nodenums)
                    vars2))
  :hints (("Goal" :use (:instance member-equal-of-var-okay-to-elim)
           :in-theory (disable member-equal-of-var-okay-to-elim))))
