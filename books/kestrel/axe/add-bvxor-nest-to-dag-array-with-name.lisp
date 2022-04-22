; Adding a nest of bvxors to the DAG
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

(include-book "dag-array-builders2")
(include-book "def-dag-builder-theorems")
(include-book "kestrel/bv/bvxor" :dir :system) ; since this tool knows about bvxor
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable myquotep)))

;; KEEP IN SYNC WITH ADD-BITXOR-NEST-TO-DAG-ARRAY-WITH-NAME-AUX
;; Returns (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; The "-with-name" suffix indicates that this function takes the dag-array-name and dag-parent-array-name.
(defund add-bvxor-nest-to-dag-array-with-name-aux (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up)
                                                   quoted-size
                                                   core-nodenum
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (myquotep quoted-size)
                              (natp core-nodenum)
                              (< core-nodenum dag-len)
                              (true-listp rev-leaves)
                              (bounded-darg-listp rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (not-cddr-of-nth-when-all-dargp
                                                         dargp-when-myquotep
                                                         dargp-less-than-when-myquotep)
                                                        (dargp myquotep natp)))))
           (type (integer 0 2147483646) dag-len))
  (if (endp rev-leaves)
      (mv (erp-nil) core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (add-function-call-expr-to-dag-array-with-name 'bvxor (list quoted-size (first rev-leaves) core-nodenum) ; note the order
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
      (if erp
          (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-bvxor-nest-to-dag-array-with-name-aux (rest rev-leaves)
                                                   quoted-size
                                                   core-nodenum
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))

(def-dag-builder-theorems
  (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :dag-array-name dag-array-name
  :dag-parent-array-name dag-parent-array-name
  :hyps ((true-listp rev-leaves)
         (natp core-nodenum)
         (< core-nodenum dag-len)
         (bounded-darg-listp rev-leaves dag-len)
         (myquotep quoted-size)))

;drop some hyps?
(defthm dargp-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-with-name-aux
  (implies (and (myquotep quoted-size)
                (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; (true-listp rev-leaves)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-bvxor-nest-to-dag-array-with-name-aux))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-with-name-aux
  (implies (and (myquotep quoted-size)
                (natp core-nodenum)
                (< core-nodenum dag-len)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; (true-listp rev-leaves)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (add-bvxor-nest-to-dag-array-with-name-aux rev-leaves quoted-size core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable add-bvxor-nest-to-dag-array-with-name-aux))))

;; KEEP IN SYNC WITH ADD-BITXOR-NEST-TO-DAG-ARRAY-WITH-NAME
;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; The "-with-name" suffix indicates that this function takes the dag-array-name and dag-parent-array-name.
(defund add-bvxor-nest-to-dag-array-with-name (rev-leaves ;reversed from the order we want them in (since we must build the nest from the bottom up); may have 0 or just 1 element, due to duplicates being removed
                                               size       ;unquoted
                                               quoted-size
                                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (myquotep quoted-size)
                              (natp size)
                              (true-listp rev-leaves)
                              (bounded-darg-listp rev-leaves dag-len))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d (not-cddr-of-nth-when-all-dargp
                                                         dargp-less-than-when-myquotep
                                                         dargp-when-myquotep)
                                                        (dargp
                                                         dargp-less-than
                                                         myquotep
                                                         natp
                                                         car-becomes-nth-of-0
                                                         pseudo-dag-arrayp)))))
           (type (integer 0 2147483646) dag-len))
  (if (endp rev-leaves)
      ;; special case: no leaves:
      (mv (erp-nil)
          (enquote 0) ;the xor of no items is 0
          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (if (endp (cdr rev-leaves)) ;the xor of one thing is the low bits of that thing
        ;; special case: a single leaf:
        ;; Justified by properties like bvxor-of-0-arg2 and bvxor-of-0-arg3:
        (let ((leaf (first rev-leaves)))
          (if (quotep leaf) ; just check consp?
              (mv (erp-nil)
                  ;; Chop/coerce constants:
                  (if (unsigned-byte-p size (unquote leaf))
                      leaf ; usual case
                    (enquote (bvchop size (ifix (unquote leaf)))))
                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            ;; a single leaf that is a nodenum: Add (bvchop '<size> <leaf>) since bvxor chops its argument
            (add-function-call-expr-to-dag-array-with-name 'bvchop
                                                           (list quoted-size leaf)
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
      ;; At least two leaves (usual case).  First, create an xor of the first 2 leaves:
      (mv-let (erp core-nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-function-call-expr-to-dag-array-with-name 'bvxor (list quoted-size (second rev-leaves) (first rev-leaves)) ; note the order (first leaf is deeper in the nest)
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
        (if erp
            (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          ;; Then call recursive helper function to handle the rest, adding in one node at a time:
          (add-bvxor-nest-to-dag-array-with-name-aux (rest (rest rev-leaves))
                                                     quoted-size
                                                     core-nodenum
                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))))

(def-dag-builder-theorems
  (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :recursivep nil
  :dag-array-name dag-array-name
  :dag-parent-array-name dag-parent-array-name
  :hyps ((true-listp rev-leaves)
         (bounded-darg-listp rev-leaves dag-len)
         (myquotep quoted-size)))

(defthm dargp-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-with-name
  (implies (and (myquotep quoted-size)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (e/d (add-bvxor-nest-to-dag-array-with-name) (dargp)))))

(defthm dargp-less-than-of-mv-nth-1-of-add-bvxor-nest-to-dag-array-with-name
  (implies (and (myquotep quoted-size)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (bounded-darg-listp rev-leaves dag-len)
                (not (mv-nth 0 (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                       (mv-nth 3 (add-bvxor-nest-to-dag-array-with-name rev-leaves size quoted-size dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (e/d (add-bvxor-nest-to-dag-array-with-name) (dargp-less-than)))))
