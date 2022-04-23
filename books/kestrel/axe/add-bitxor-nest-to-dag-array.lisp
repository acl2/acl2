; Adding a nest of bitxors to the DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-array-builders")
(include-book "def-dag-builder-theorems")
(include-book "kestrel/bv/bitxor" :dir :system) ; since this tool knows about bitxor
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable natp)))

;dup
(defthm bounded-darg-listp-when-singleton-cheap
  (implies (equal 1 (len dargs))
           (equal (bounded-darg-listp dargs bound)
                  (and (dargp-less-than (first dargs) bound)
                       (null (cdr dargs)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-darg-listp))))

;; KEEP IN SYNC WITH ADD-BVXOR-NEST-TO-DAG-ARRAY-AUX
;; Returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund add-bitxor-nest-to-dag-array-aux (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up)
                                          core-nodenum
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (natp core-nodenum)
                              (< core-nodenum dag-len)
                              (true-listp rev-leaves)
                              (bounded-darg-listp rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (NOT-CDDR-OF-NTH-WHEN-ALL-DARGP)
                                                        (DARGP
                                                         DARGP-LESS-THAN
                                                         natp
                                                         CAR-BECOMES-NTH-OF-0
                                                         PSEUDO-DAG-ARRAYP)))))
           (type (integer 0 2147483646) dag-len))
  (if (endp rev-leaves)
      (mv (erp-nil) core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
      (add-function-call-expr-to-dag-array 'bitxor (list (first rev-leaves) core-nodenum) ; note the order
                                           dag-array dag-len dag-parent-array dag-constant-alist)
      (if erp
          (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-bitxor-nest-to-dag-array-aux (rest rev-leaves)
                                          core-nodenum
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(def-dag-builder-theorems
  (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((true-listp rev-leaves)
         (natp core-nodenum)
         (< core-nodenum dag-len)
         (bounded-darg-listp rev-leaves dag-len)))

;drop some hyps?
(defthm dargp-of-mv-nth-1-of-add-bitxor-nest-to-dag-array-aux
  (implies (and (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;                (true-listp rev-leaves)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp (mv-nth 1 (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-bitxor-nest-to-dag-array-aux))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bitxor-nest-to-dag-array-aux
  (implies (and (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;                (true-listp rev-leaves)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            (mv-nth 3 (add-bitxor-nest-to-dag-array-aux rev-leaves core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (enable add-bitxor-nest-to-dag-array-aux))))

;; KEEP IN SYNC WITH ADD-BVXOR-NEST-TO-DAG-ARRAY
;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund add-bitxor-nest-to-dag-array (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up); may have 0 or just 1 element
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (true-listp rev-leaves)
                              (bounded-darg-listp rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (NOT-CDDR-OF-NTH-WHEN-ALL-DARGP)
                                                        (DARGP
                                                         DARGP-LESS-THAN
                                                         natp
                                                         CAR-BECOMES-NTH-OF-0
                                                         PSEUDO-DAG-ARRAYP)))))
           (type (integer 0 2147483646) dag-len))
  (if (endp rev-leaves)
      ;; no leaves:
      (mv (erp-nil)
          (enquote 0) ;the bitxor of no items is 0
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (if (endp (cdr rev-leaves)) ;the bitxor of one thing is the low bit of that thing
        ;;a single leaf:
        (let ((leaf (first rev-leaves)))
          (if (quotep leaf)
              (mv (erp-nil)
                  (enquote (getbit 0 (ifix (unquote leaf)))) ;consider dropping the ifix
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            ;; a single leaf that is a nodenum:
            (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist)
              (add-function-call-expr-to-dag-array 'getbit (list ''0 leaf)
                                                   dag-array dag-len dag-parent-array dag-constant-alist)
              (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
      ;;at least two leaves (usual case):
      (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
        (add-function-call-expr-to-dag-array 'bitxor (list (second rev-leaves) (first rev-leaves)) ;note the order
                                             dag-array dag-len dag-parent-array dag-constant-alist)
        (if erp
            (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (add-bitxor-nest-to-dag-array-aux (rest (rest rev-leaves))
                                            core-nodenum
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))

(def-dag-builder-theorems
  (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :hyps ((true-listp rev-leaves)
         (bounded-darg-listp rev-leaves dag-len)))

(defthm dargp-of-mv-nth-1-of-add-bitxor-nest-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp (mv-nth 1 (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (add-bitxor-nest-to-dag-array) (dargp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bitxor-nest-to-dag-array
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
           (dargp-less-than (mv-nth 1 (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                            (mv-nth 3 (add-bitxor-nest-to-dag-array rev-leaves dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
  :hints (("Goal" :in-theory (e/d (add-bitxor-nest-to-dag-array) (dargp-less-than)))))
