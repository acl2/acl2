; Adding a nest of bvxors to the DAG
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

(include-book "dag-array-builders2")
(include-book "def-dag-builder-theorems")
(include-book "kestrel/bv/bvxor" :dir :system) ; since this tool knows about bvxor
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;rename to connote adding to the dag
;keep in sync with bitxor version
;returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
(defund add-bvxor-nest-to-dag-array-aux (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up)
                                         quoted-size ;fixme add this to the bitxor version too?
                                         core-nodenum
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (declare (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (myquotep quoted-size)
                              (natp core-nodenum)
                              (< core-nodenum dag-len)
                              (true-listp rev-leaves)
                              (all-dargp-less-than rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (NOT-CDDR-OF-NTH-WHEN-ALL-DARGP
                                                         dargp-when-myquotep
                                                         dargp-less-than-when-myquotep
                                                         )
                                                        (DARGP
                                                         myquotep
                                                         DARGP-LESS-THAN
                                                         natp
                                                         CAR-BECOMES-NTH-OF-0
                                                         PSEUDO-DAG-ARRAYP))))))
  (if (endp rev-leaves)
      (mv (erp-nil) core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (add-function-call-expr-to-dag-array-with-name 'bvxor (list quoted-size (first rev-leaves) core-nodenum) ; `(',size ,(first rev-leaves) ,core-nodenum) ;note the order
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
      (if erp
          (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-bvxor-nest-to-dag-array-aux (rest rev-leaves)
                                         quoted-size
                                         core-nodenum
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))

(local (in-theory (disable myquotep)))

(def-dag-builder-theorems
  (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :dag-array-name dag-array-name
  :dag-parent-array-name dag-parent-array-name
  :hyps ((true-listp rev-leaves)
         (natp core-nodenum)
         (< core-nodenum dag-len)
         (all-dargp-less-than rev-leaves dag-len)
         (myquotep quoted-size)))

;drop some hyps?
(defthm dargp-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-aux
  (implies (and (myquotep quoted-size)
                (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; (true-listp rev-leaves)
                (all-dargp-less-than rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-bvxor-nest-to-dag-array-aux))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-aux
  (implies (and (myquotep quoted-size)
                (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; (true-listp rev-leaves)
                (all-dargp-less-than rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (add-bvxor-nest-to-dag-array-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-bvxor-nest-to-dag-array-aux))))

;keep in sync with bitxor version
;returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
(defund add-bvxor-nest-to-dag-array (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up); may have 0 or just 1 element
                                     size       ;unquoted
                                     quoted-size
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (declare (type (integer 0 2147483646) dag-len)
           (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (myquotep quoted-size)
                              (natp size)
                              (true-listp rev-leaves)
                              (all-dargp-less-than rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (not-cddr-of-nth-when-all-dargp
                                                         DARGP-LESS-THAN-WHEN-MYQUOTEP
                                                         DARGP-WHEN-MYQUOTEP)
                                                        (dargp
                                                         dargp-less-than
                                                         myquotep
                                                         natp
                                                         car-becomes-nth-of-0
                                                         pseudo-dag-arrayp))))))
  (if (endp rev-leaves)
      ;; no leaves:
      (mv (erp-nil)
          (enquote 0) ;the xor of no items is 0
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (if (endp (cdr rev-leaves)) ;the xor of one thing is the low bits of that thing
        ;;a single leaf:
        (let ((leaf (first rev-leaves)))
          (if (quotep leaf)
              (mv (erp-nil)
                  (enquote (bvchop                     ;$inline
                            size (ifix (unquote leaf)) ;todo: maybe drop the ifix?
                            ) ;will this ever do any trimming?
                           ) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            ;; a single leaf that is a nodenum:
            (add-function-call-expr-to-dag-array-with-name 'bvchop ;$inline
                                                                 (list quoted-size leaf) ;`(',size ,leaf)
                                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
      ;;at least two leaves:
      (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-function-call-expr-to-dag-array-with-name 'bvxor (list quoted-size (second rev-leaves) (first rev-leaves)) ;`(',size ,(second rev-leaves) ,(first rev-leaves)) ;note the order
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
        (if erp
            (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (add-bvxor-nest-to-dag-array-aux (rest (rest rev-leaves))
                                           quoted-size
                                           core-nodenum
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))))

(def-dag-builder-theorems
  (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :dag-array-name dag-array-name
  :dag-parent-array-name dag-parent-array-name
  :hyps ((true-listp rev-leaves)
         (all-dargp-less-than rev-leaves dag-len)
         (myquotep quoted-size)))

(defthm dargp-of-mv-nth-1-of-add-bvxor-nest-to-dag-array
  (implies (and (myquotep quoted-size)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (e/d (add-bvxor-nest-to-dag-array) (dargp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bvxor-nest-to-dag-array
  (implies (and (myquotep quoted-size)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (all-dargp-less-than rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (add-bvxor-nest-to-dag-array rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (e/d (add-bvxor-nest-to-dag-array) (dargp-less-than)))))
