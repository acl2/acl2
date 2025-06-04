; Computing sets of DAG nodes that support DAG nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;; This book contains utilities to compute the set of DAG nodes that supports
;;; a given node or set of nodes, and to transform DAGs accordingly (e.g., by
;;; dropping non-supporting nodes).

;; TODO: Consider using a stobj array instead of the tag-array, perhaps using
;; with-local-stobj.

(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "dag-arrays")
(include-book "numeric-lists")
(include-book "translation-array")
(include-book "kestrel/acl2-arrays/aref1-list" :dir :system)
(include-book "kestrel/acl2-arrays/aset1-list" :dir :system)
(include-book "kestrel/typed-lists-light/all-greater" :dir :system)
(local (include-book "rational-lists"))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(local (in-theory (disable (:i alistp))))

;move
(local
 (defthm all-<-forward-to-posp-when-nat-listp
   (implies (and (all-< items x)
                 (nat-listp items)
                 (consp items)
                 (integerp x))
            (posp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable all-<)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Used to express some theorems
;; Check that each of the NODENUMS is tagged in the array.
;; The "-with-name" suffix indicates that this function takes the tag-array-name as an argument.
(defund all-taggedp-with-name (nodenums tag-array-name array)
  (declare (xargs :guard (and (array1p tag-array-name array)
                              (nat-listp nodenums)
                              (all-< nodenums (alen1 tag-array-name array)))))
  (if (endp nodenums)
      t
    (and (aref1 tag-array-name array (first nodenums))
         (all-taggedp-with-name (rest nodenums) tag-array-name array))))

(defthm all-taggedp-with-name-of-aset1-list
  (implies (and (array1p tag-array-name array)
                (nat-listp nodenums)
                (all-< nodenums (alen1 tag-array-name array)))
           (all-taggedp-with-name nodenums tag-array-name (aset1-list tag-array-name array nodenums 't)))
  :hints (("Goal" :in-theory (enable all-taggedp-with-name aset1-list))))

(defthm all-taggedp-with-name-of-aset1-of-t-when-all-taggedp-with-name
  (implies (and (all-taggedp-with-name nodenums tag-array-name tag-array)
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array))
                (nat-listp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array))
                (array1p tag-array-name tag-array))
           (all-taggedp-with-name nodenums tag-array-name (aset1 tag-array-name tag-array nodenum t)))
  :hints (("Goal" :in-theory (enable all-taggedp-with-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Set the tag bit for each thing in DARGS that is a nodeum.  DARGS are nodenums
;or quoted constants.
;; The "-with-name" suffix indicates that this function takes the tag-array-name as an argument.
(defund tag-nodenums-with-name (dargs tag-array-name array)
  (declare (xargs :guard (and (array1p tag-array-name array)
                              (true-listp dargs)
                              (bounded-darg-listp dargs (alen1 tag-array-name array)))))
  (if (endp dargs)
      array
    (let ((darg (first dargs)))
      (if (consp darg) ;; test for quoted constant
          (tag-nodenums-with-name (cdr dargs) tag-array-name array)
        (tag-nodenums-with-name (cdr dargs) tag-array-name (aset1 tag-array-name array darg t))))))

(defthm alen1-of-tag-nodenums-with-name
  (implies (bounded-darg-listp dargs (alen1 tag-array-name array))
           (equal (alen1 tag-array-name (tag-nodenums-with-name dargs tag-array-name array))
                  (alen1 tag-array-name array)))
  :hints (("Goal" :in-theory (enable tag-nodenums-with-name))))

(defthm array1p-of-tag-nodenums-with-name
  (implies (and (array1p tag-array-name array)
                (bounded-darg-listp dargs (alen1 tag-array-name array)))
           (array1p tag-array-name (tag-nodenums-with-name dargs tag-array-name array)))
  :hints (("Goal" :in-theory (enable tag-nodenums-with-name))))

;; the tag doesn't become unset
(defthm aref1-of-tag-nodenums-with-name-when-aref1
  (implies (and (aref1 tag-array-name tag-array nodenum)
                (array1p tag-array-name tag-array)
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array))
                (bounded-darg-listp dargs (alen1 tag-array-name tag-array)))
           (aref1 tag-array-name (tag-nodenums-with-name dargs tag-array-name tag-array) nodenum))
  :hints (("Goal" :in-theory (enable tag-nodenums-with-name))))

;; tags don't become unset
(defthm all-taggedp-with-name-of-tag-nodenums-with-name-when-all-taggedp-with-name
  (implies (and (all-taggedp-with-name nodenums tag-array-name tag-array)
                (bounded-darg-listp nodenums2 (alen1 tag-array-name tag-array))
                (nat-listp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array))
                (array1p tag-array-name tag-array))
           (all-taggedp-with-name nodenums tag-array-name (tag-nodenums-with-name nodenums2 tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable all-taggedp-with-name tag-nodenums-with-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;processes the nodes top down in order
;before calling this, you should tag the node(s) whose supporters you want to compute (by setting their entries in the tag-array to t)
;if a node is tagged when we reach it, its children get tagged too
;could also use a worklist algorithm (might be better if the number of tagged nodes will be small - saves looping over the whole array)
;; The "-with-name" suffix indicates that this function takes the dag-array-name and tag-array-name as arguments.
(defund tag-supporters-of-nodes-with-name-aux (n dag-array-name dag-array tag-array-name tag-array)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (integerp n)
                              (<= -1 n)
                              (implies (natp n)
                                       (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                                            (array1p tag-array-name tag-array)
                                            (< n (alen1 tag-array-name tag-array)))))
                  :split-types t)
           (type (integer -1 1152921504606846973) n))
  (if (or (not (mbt (and (integerp n)
                         (<= -1 n))))
          (= -1 n))
      tag-array
    (let ((tag (aref1 tag-array-name tag-array n)))
      (if tag
          (let ((expr (aref1 dag-array-name dag-array n)))
            (if (or (variablep expr)
                    (fquotep expr))
                ;;no children to tag
                (tag-supporters-of-nodes-with-name-aux (+ -1 n) dag-array-name dag-array tag-array-name tag-array)
              (let ((args (dargs expr)))
                (tag-supporters-of-nodes-with-name-aux (+ -1 n) dag-array-name dag-array tag-array-name (tag-nodenums-with-name args tag-array-name tag-array)))))
        ;;node isn't tagged
        (tag-supporters-of-nodes-with-name-aux (+ -1 n) dag-array-name dag-array tag-array-name tag-array)))))

(defthm alen1-of-tag-supporters-of-nodes-with-name-aux
  (implies (and (natp top-nodenum)
                (array1p tag-array-name tag-array)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (< top-nodenum (alen1 tag-array-name tag-array)))
           (equal (alen1 tag-array-name (tag-supporters-of-nodes-with-name-aux top-nodenum dag-array-name dag-array tag-array-name tag-array))
                  (alen1 tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name-aux)
           :expand ((tag-supporters-of-nodes-with-name-aux 0 dag-array-name
                                    dag-array tag-array-name tag-array))
           :do-not '(generalize eliminate-destructors))))

(defthm array1p-of-tag-supporters-of-nodes-with-name-aux
  (implies (and (natp top-nodenum)
                (array1p tag-array-name tag-array)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (< top-nodenum (alen1 tag-array-name tag-array)))
           (array1p tag-array-name (tag-supporters-of-nodes-with-name-aux top-nodenum dag-array-name dag-array tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name-aux)
           :expand ((tag-supporters-of-nodes-with-name-aux 0 dag-array-name dag-array tag-array-name tag-array))
           :do-not '(generalize eliminate-destructors))))

;; the tag doesn't become unset
(defthm aref1-of-tag-supporters-of-nodes-with-name-aux-when-aref1
  (implies (and (aref1 tag-array-name tag-array nodenum)
                ;; the guard:
                (and (integerp n)
                     (implies (natp n)
                              (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                                   (array1p tag-array-name tag-array)
                                   (< n (alen1 tag-array-name tag-array)))))
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array)))
           (aref1 tag-array-name (tag-supporters-of-nodes-with-name-aux n dag-array-name dag-array tag-array-name tag-array) nodenum))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name-aux))))

;; tags don't become unset
(defthm all-taggedp-with-name-of-tag-supporters-of-nodes-with-name-aux-when-all-taggedp-with-name
  (implies (and (all-taggedp-with-name nodenums tag-array-name tag-array)
                ;; the guard:
                (integerp n)
                (implies (natp n)
                         (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                              (array1p tag-array-name tag-array)
                              (< n (alen1 tag-array-name tag-array))))
                (nat-listp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array)))
           (all-taggedp-with-name nodenums tag-array-name (tag-supporters-of-nodes-with-name-aux n dag-array-name dag-array tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name-aux NAT-LISTP))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the TAG-ARRAY, named TAG-ARRAY-NAME, which maps each nodenum to a
;; boolean indicating whether it is a supporter of any of the NODENUMS (nodes
;; are considered their own supporters).
;; rename make-supporters-tag-array-for-nodes
;; The "-with-name" suffix indicates that this function takes the dag-array-name and tag-array-name as arguments.
(defund tag-supporters-of-nodes-with-name (nodenums
                                           max-nodenum ; often one less than the tag-array-length, we pass it in since the called usually computes the maxelem
                                           dag-array-name dag-array
                                           tag-array-name ;; the name of the tag array to create
                                           tag-array-length ;; the array length to use  -- if we might look up nodes higher than the nodenums, we can make this larger than (+ 1 (maxelem nodenums)) to prevent errors (todo: do we ever need that?)
                                           )
  (declare (xargs :guard (and (nat-listp nodenums)
                              (consp nodenums) ;so we can call maxelem
                              (equal max-nodenum (maxelem nodenums))
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                              (integerp tag-array-length)
                              (all-< nodenums tag-array-length) ;implies that tag-array-length is positive
                              (<= tag-array-length *max-1d-array-length*)
                              (symbolp tag-array-name))))
  (let* ((tag-array (make-empty-array tag-array-name tag-array-length))
         ;; Tag all the NODENUMS...
         (tag-array (aset1-list tag-array-name tag-array nodenums t))
         ;; ... and their supporters:
         (tag-array (tag-supporters-of-nodes-with-name-aux max-nodenum dag-array-name dag-array tag-array-name tag-array)))
    tag-array))

(defthm array1p-of-tag-supporters-of-nodes-with-name
  (implies (and (nat-listp nodenums)
                (consp nodenums)
                (equal max-nodenum (maxelem nodenums))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums))))
           (array1p tag-array-name (tag-supporters-of-nodes-with-name nodenums max-nodenum dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (e/d (tag-supporters-of-nodes-with-name) (natp)))))

(defthm alen1-of-tag-supporters-of-nodes-with-name
  (implies (and (nat-listp nodenums)
                (consp nodenums)
                (equal max-nodenum (maxelem nodenums))
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (equal (alen1 tag-array-name (tag-supporters-of-nodes-with-name nodenums max-nodenum dag-array-name dag-array tag-array-name tag-array-length))
                  tag-array-length))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name))))

;; the max nodenum gets tagged
(defthm aref1-of-tag-supporters-of-nodes-with-name-and-maxelem
  (implies (and (nat-listp nodenums)
                (consp nodenums)
                (equal max-nodenum (maxelem nodenums))
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (aref1 tag-array-name
                  (tag-supporters-of-nodes-with-name nodenums max-nodenum dag-array-name dag-array tag-array-name tag-array-length)
                  (maxelem nodenums)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name maxelem))))

;; all of the nodenums get tagged
(defthm all-taggedp-with-name-of-tag-supporters-of-nodes-with-name-same
  (implies (and (nat-listp nodenums)
                (consp nodenums)
                (equal max-nodenum (maxelem nodenums))
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (all-taggedp-with-name nodenums tag-array-name (tag-supporters-of-nodes-with-name nodenums max-nodenum dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes-with-name
                                     all-taggedp-with-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Special case for one node.
;; rename make-supporters-tag-array-for-node
;; The "-with-name" suffix indicates that this function takes the dag-array-name and tag-array-name as arguments.
(defund tag-supporters-of-node-with-name (nodenum
                                          dag-array-name dag-array
                                          tag-array-name ;; the name of the tag array to create
                                          tag-array-length ;if we might look up nodes higher than nodenum, we can make this larger than (+ 1 nodenum) to prevent errors
                                          )
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (integerp tag-array-length)
                              (< nodenum tag-array-length) ;implies that tag-array-length is positive
                              (<= tag-array-length *max-1d-array-length*)
                              (symbolp tag-array-name))))
  (tag-supporters-of-nodes-with-name (list nodenum) nodenum dag-array-name dag-array tag-array-name tag-array-length))

(defthm array1p-of-tag-supporters-of-node-with-name
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (array1p tag-array-name (tag-supporters-of-node-with-name nodenum dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-node-with-name))))

(defthm alen1-of-tag-supporters-of-node-with-name
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (equal (alen1 tag-array-name (tag-supporters-of-node-with-name nodenum dag-array-name dag-array tag-array-name tag-array-length))
                  tag-array-length))
  :hints (("Goal" :in-theory (enable tag-supporters-of-node-with-name))))

(defthm aref1-of-tag-supporters-of-node-with-name
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length *max-1d-array-length*)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (aref1 tag-array-name
                  (tag-supporters-of-node-with-name nodenum dag-array-name dag-array tag-array-name tag-array-length)
                  nodenum))
  :hints (("Goal" :use (:instance aref1-of-tag-supporters-of-nodes-with-name-and-maxelem (nodenums (list nodenum)) (max-nodenum nodenum))
           :in-theory (e/d (tag-supporters-of-node-with-name) (aref1-of-tag-supporters-of-nodes-with-name-and-maxelem)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; dropping non-supporters
;;;

;; Returns (mv dag translation-array). This takes a dag-array but returns a dag (as a list).
;; This does not remove duplicates (we are not building even a dag-array, much
;; less a dag-parent-array!), because we assume that the incoming DAG has no
;; duplicates, and we are not changing exprs in a way that can introduce duplicates.
;; TODO: avoid making a node that is a quotep (but then consider what to do about possible duplicate exprs caused by that! and also consider that this might then return a quotep).
;; The "-with-name" suffix indicates that this function takes the dag-array-name as an argument.
(defund build-reduced-dag-with-name (n top-nodenum dag-array-name dag-array
                                       tag-array ; nodes that we want to keep have been tagged
                                       dag-len ;the next nodenum to use in the new DAG
                                       translation-array
                                       dag-acc ; the DAG being built up
                                       )
  (declare (xargs :guard (and (array1p 'translation-array translation-array)
                              (array1p 'tag-array tag-array)
                              (alistp dag-acc)
                              (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                              (natp n)
                              (natp dag-len)
                              (<= dag-len n)
                              (< top-nodenum (alen1 'tag-array tag-array))
                              (< top-nodenum (alen1 'translation-array translation-array))
                              (<= n (+ 1 top-nodenum))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))
                  :measure (+ 1 (nfix (+ 1 (- top-nodenum n))))
                  :guard-hints (("Goal" :in-theory (enable pseudo-dag-arrayp))) ;fixme?
                  :split-types t)
           (type (integer 0 1152921504606846973) top-nodenum)
           (type (integer 0 1152921504606846974) n dag-len))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp top-nodenum)))
          (> n top-nodenum))
      (mv dag-acc translation-array)
    (let ((tag (aref1 'tag-array tag-array n))) ;only nodes that are tagged get put into the result
      (if (not tag) ;drop it and don't increment the dag-len
          (progn$ ;; (cw "Dropping node ~x0: ~x1.~%" n (aref1 dag-array-name dag-array n))
                  (build-reduced-dag-with-name (+ 1 n) top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
        (let* ((expr (aref1 dag-array-name dag-array n))
               (expr (if (or (variablep expr)
                             (fquotep expr)) ;todo: maybe inline constants, but then drop-non-supporters-array-with-name could return a constant
                         ;; Nothing to fix up:
                         expr
                       (let* ((fn (ffn-symb expr))
                              (args (dargs expr))
                              (new-args (translate-args args translation-array)))
                         ;; Could try cons-with-hint here if often nothing will change:
                         (cons fn new-args))))
               ;; Record the new nodenum for old node N:
               (translation-array (aset1 'translation-array translation-array n dag-len))
               (dag-acc (acons-fast dag-len expr dag-acc)))
          (build-reduced-dag-with-name (+ 1 n) top-nodenum dag-array-name dag-array tag-array (+ 1 dag-len) translation-array dag-acc))))))

(defthm consp-of-mv-nth-0-of-build-reduced-dag-with-name
  (implies (consp dag-acc)
           (consp (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag-with-name))))

(defthm alen1-of-mv-nth-1-of-build-reduced-dag-with-name
  (equal (alen1 'translation-array (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
         (alen1 'translation-array translation-array))
  :hints (("Goal" :in-theory (enable build-reduced-dag-with-name))))

(defthm array1p-of-mv-nth-1-of-build-reduced-dag-with-name
  (implies (and (array1p 'translation-array translation-array)
                (<= 0 n)
                (<= n top-nodenum)
                (< top-nodenum (alen1 'translation-array translation-array)))
           (array1p 'translation-array (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag-with-name)
           :expand ((build-reduced-dag-with-name n n dag-array-name
                                        dag-array tag-array dag-len
                                        translation-array dag-acc)))))

(defthm bounded-translation-arrayp-aux-of-translation-array-after-build-reduced-dag-with-name
  (implies (and (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                ;(translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux top-nodenum translation-array (+ 1 (if (consp dag-acc)
                                                                                       (car (car dag-acc))
                                                                                     0)))
                (<= dag-len n)
                (implies (consp dag-acc)
                         (< (car (car dag-acc)) dag-len))
                ;;(PSEUDO-DAGP-AUX dag-acc (car (car dag-acc)))
                (nat-listp (strip-cars dag-acc))
                )
           (bounded-translation-arrayp-aux top-nodenum
                                           (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                           (+ 1 (car (car (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))))))
  :hints (;; ("subgoal *1/1" :use (:instance BOUNDED-TRANSLATION-ARRAYP-AUX-MONOTONE
          ;;                                 (BOUND (+ 1 (CAR (CAR DAG-ACC))))
          ;;                                 (TRANSLATION-ARRAY TRANSLATION-ARRAY)
          ;;                                 (NODENUM (CAR (CAR DAG-ACC)))
          ;;                                 (nodenum2 (+ -1 N))
          ;;                                 (bound2 (+ 1 (CAR (CAR DAG-ACC)))))
          ;;  :in-theory (disable BOUNDED-TRANSLATION-ARRAYP-AUX-MONOTONE))
          ("Goal" :in-theory (enable build-reduced-dag-with-name)
           :expand ((build-reduced-dag-with-name n n dag-array-name
                                        dag-array tag-array dag-len
                                        translation-array dag-acc)))))

(defthm bounded-translation-arrayp-aux-of-translation-array-after-build-reduced-dag-with-name-gen
  (implies (and (<= (+ 1 (car (car (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))) bound)
                (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                ;(translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux top-nodenum translation-array (+ 1 (if (consp dag-acc)
                                                                                       (car (car dag-acc))
                                                                                     0)))
                (<= dag-len n)
                (implies (consp dag-acc)
                         (< (car (car dag-acc)) dag-len))
                ;;(PSEUDO-DAGP-AUX dag-acc (car (car dag-acc)))
                (nat-listp (strip-cars dag-acc))
                )
           (bounded-translation-arrayp-aux top-nodenum
                                           (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                           bound))
  :hints (("Goal" :use (:instance bounded-translation-arrayp-aux-of-translation-array-after-build-reduced-dag-with-name)
           :in-theory (disable bounded-translation-arrayp-aux-of-translation-array-after-build-reduced-dag-with-name))))

(defthm build-reduced-dag-with-name-type
  (implies (and (array1p 'translation-array translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'tag-array tag-array)
                (alistp dag-acc) ;drop?
                (pseudo-dagp-aux dag-acc (+ -1 dag-len))
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len) ;(posp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                ;;(consp (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
                )
           (pseudo-dagp-aux (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                            (if (consp (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
                                (car (car (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
                              -1)))
  :hints (("Goal" :induct (build-reduced-dag-with-name n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1)
                    ;;(pseudo-dagp-aux dag-acc (car (car dag-acc)))
                    )
           :in-theory (e/d (build-reduced-dag-with-name ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                            )))))

(defthm consp-of-mv-nth-0-of-build-reduced-dag-with-name-alt
  (implies (and (aref1 'tag-array tag-array top-nodenum) ;since the top-nodenum is tagged, the result cannot be empty
                (natp top-nodenum)
                (natp n)
                (<= n top-nodenum))
           (consp (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :induct (build-reduced-dag-with-name n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1))
           :in-theory (e/d (build-reduced-dag-with-name ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                               )))))

(defthm natp-of-car-of-car-of-mv-nth-0-of-build-reduced-dag-with-name
  (implies (and (aref1 'tag-array tag-array top-nodenum) ;since the top-nodenum is tagged, the result cannot be empty
                (natp top-nodenum)
                (natp n)
                (<= n top-nodenum)
                (natp dag-len))
           (natp (car (car (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))))
  :hints (("Goal" :induct (build-reduced-dag-with-name n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1))
           :in-theory (e/d (build-reduced-dag-with-name ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                            )))))

(defthm pseudo-dagp-of-mv-nth-0-of-build-reduced-dag-with-name
  (implies (and (aref1 'tag-array tag-array top-nodenum) ;since the top-nodenum is tagged, the result cannot be empty
                (array1p 'translation-array translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array dag-len)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (pseudo-dagp-aux dag-acc (+ -1 dag-len))
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n top-nodenum))
           (pseudo-dagp (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array
                                                      dag-len ;the next nodenum to use in the new dag
                                                      translation-array dag-acc))))
  :hints (("Goal" :use (build-reduced-dag-with-name-type
                        consp-of-mv-nth-0-of-build-reduced-dag-with-name)
           :expand ()
           :in-theory (e/d (pseudo-dagp) (natp build-reduced-dag-with-name-type
                                               consp-of-mv-nth-0-of-build-reduced-dag-with-name
                                               ;;pseudo-dagp-aux-of-car-of-car-when-pseudo-dagp-aux
                                               )))))

(defthm true-listp-of-mv-nth-0-of-build-reduced-dag-with-name
  (implies (true-listp dag-acc)
           (true-listp
            (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array
                                          dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag-with-name))))

(defthm <=-of-len-of-mv-nth-0-of-build-reduced-dag-with-name
  (implies (and (natp n)
                (natp top-nodenum)
                (<= n (+ 1 top-nodenum)))
           (<= (len (mv-nth 0 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
               (+ (len dag-acc)
                  (+ 1 (- top-nodenum n)))))
  :hints (("Goal" :in-theory (enable build-reduced-dag-with-name))))

(defthm <=-of-len-of-mv-nth-0-of-build-reduced-dag-with-name-special
  (implies (natp top-nodenum)
           (<= (len (mv-nth 0 (build-reduced-dag-with-name 0 top-nodenum dag-array-name dag-array tag-array dag-len translation-array nil)))
               (+ 1 top-nodenum)))
  :hints (("Goal" :use (:instance <=-of-len-of-mv-nth-0-of-build-reduced-dag-with-name (dag-acc nil) (n 0))
           :in-theory (disable <=-of-len-of-mv-nth-0-of-build-reduced-dag-with-name))))

(defthm aref1-of-mv-nth-1-of-build-reduced-dag-with-name-too-low
  (implies (and (natp nodenum)
                (< nodenum n)
                (array1p 'translation-array translation-array)
                (natp n)
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                )
           (equal (aref1 'translation-array
                         (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                         nodenum)
                  (aref1 'translation-array
                         translation-array
                         nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag-with-name) (natp)))))

;; nodenum doesn't become unset in the translation-array
(defthm natp-of-aref1-of-mv-nth-1-of-build-reduced-dag-with-name-when-natp-of-aref1
  (implies (and (natp (aref1 'translation-array translation-array nodenum))
                (natp nodenum)
                (<= nodenum top-nodenum)
                (>= nodenum n)
                (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                )
           (natp (aref1 'translation-array
                        (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                        nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag-with-name) (natp)))))

(defthm natp-of-aref1-of-mv-nth-1-of-build-reduced-dag-with-name-when-tagged
  (implies (and (aref1 'tag-array tag-array nodenum)
                (natp nodenum)
                (<= nodenum top-nodenum)
                (>= nodenum n)
                (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                )
           (natp (aref1 'translation-array
                        (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                        nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag-with-name) (natp)))))

(defthm nat-listp-of-aref1-list-aux-of-mv-nth-1-of-build-reduced-dag-with-name-when-all-taggedp-with-name
  (implies (and (all-taggedp-with-name nodenums 'tag-array tag-array)
                (nat-listp nodenums)
                (all-<= nodenums top-nodenum)
                (all-> nodenums (+ -1 n)) ;use all->= ?
                (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (nat-listp acc)
                )
           (nat-listp (aref1-list-aux 'translation-array
                                      (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                      nodenums
                                      acc)))
  :hints (("Goal" :in-theory (e/d (nat-listp aref1-list-aux ALL-TAGGEDP-WITH-NAME) (natp)))))

(defthm nat-listp-of-aref1-list-of-mv-nth-1-of-build-reduced-dag-with-name-when-all-taggedp-with-name
  (implies (and (all-taggedp-with-name nodenums 'tag-array tag-array)
                (nat-listp nodenums)
                (all-<= nodenums top-nodenum)
                (all-> nodenums (+ -1 n)) ;use all->= ?
                (array1p 'translation-array translation-array)
                (array1p 'tag-array tag-array)
                (alistp dag-acc)
                (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (natp n)
                (natp dag-len)
                (< top-nodenum (alen1 'tag-array tag-array))
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                )
           (nat-listp (aref1-list 'translation-array
                                  (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                  nodenums)))
  :hints (("Goal" :in-theory (enable aref1-list))))

;; (thm
;;  (implies (and (all-taggedp-with-name nodenums 'tag-array tag-array)
;;                (natp nodenum)
;;                (< nodenum top-nodenum)
;;                (>= nodenum n)
;;                (array1p 'translation-array translation-array)
;;                (array1p 'tag-array tag-array)
;;                (alistp dag-acc)
;;                (natp top-nodenum)
;;                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
;;                (natp n)
;;                (natp dag-len)
;;                (< top-nodenum (alen1 'tag-array tag-array))
;;                (< top-nodenum (alen1 'translation-array translation-array))
;;                (<= n (+ 1 top-nodenum))
;;                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
;;                )
;;           (natp (aref1 'translation-array
;;                        (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
;;                        nodenum)))
;;  :hints (("Goal" :in-theory (e/d (build-reduced-dag-with-name) (natp)))))

;; (thm
;;  (implies (and (all-taggedp-with-name nodenums 'tag-array tag-array)
;;                (nat-listp nodenums)
;;                (all-< nodenums top-nodenum)
;;                (all-> nodenums (+ -1 n))
;;                (array1p 'translation-array translation-array)
;;                (array1p 'tag-array tag-array)
;;                (alistp dag-acc)
;;                (natp top-nodenum)
;;                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
;;                (natp n)
;;                (natp dag-len)
;;                (< top-nodenum (alen1 'tag-array tag-array))
;;                (< top-nodenum (alen1 'translation-array translation-array))
;;                (<= n (+ 1 top-nodenum))
;;                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
;;                )
;;           (nat-listp (aref1-list 'translation-array
;;                                  (mv-nth 1 (build-reduced-dag-with-name n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
;;                                  nodenums)))
;;  :hints (("Goal" :in-theory (enable nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Takes a dag-array but returns a dag.
;; TODO: Consider allowing this to return a quoted constant?
;smashes the arrays 'tag-array and 'translation-array
;bad to use the name 'tag-array here?
;better to use a worklist algorithm? maybe not..
;; The "-with-name" suffix indicates that this function takes the dag-array-name as an argument.
(defund drop-non-supporters-array-with-name (dag-array-name dag-array top-nodenum print)
  (declare (xargs :guard (and (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
                  :guard-hints (("Goal" :in-theory (disable top-nodenum))) ; disable globally?
                  :verify-guards nil
                  ))
  (b* ((old-node-count (+ 1 top-nodenum))
       (tag-array (tag-supporters-of-node-with-name top-nodenum dag-array-name dag-array 'tag-array (+ 1 top-nodenum)))
       (translation-array (make-empty-array 'translation-array (+ 1 top-nodenum)))
       ((mv dag & ;translation-array
            )
        (build-reduced-dag-with-name 0 top-nodenum dag-array-name dag-array tag-array 0 translation-array nil))
       (new-node-count (+ 1 (top-nodenum  dag)))
       (removed-node-count (- old-node-count new-node-count))
       (- (and print (cw "(Discarding ~x0 unused nodes of ~x1.)~%" removed-node-count old-node-count))))
    dag))

(defthm true-listp-of-drop-non-supporters-array-with-name
  (true-listp (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array-with-name))))

(defthm consp-of-drop-non-supporters-array-with-name
  (implies (and (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
           (consp (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print)))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array-with-name))))

(defthm <=-of-len-of-drop-non-supporters-array-with-name-linear
  (implies (natp top-nodenum)
           (<= (len (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print))
               (+ 1 top-nodenum)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable drop-non-supporters-array-with-name))))

(defthm <=-of-len-of-drop-non-supporters-array-with-name
  (implies (and (<= (+ 1 top-nodenum) bound)
                (natp top-nodenum)
                (integerp bound))
           (<= (len (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print))
               bound))
  :hints (("Goal" :use <=-of-len-of-drop-non-supporters-array-with-name-linear
           :in-theory (disable <=-of-len-of-drop-non-supporters-array-with-name-linear))))

(defthm <-of-len-of-drop-non-supporters-array-with-name
  (implies (and (< (+ 1 top-nodenum) bound)
                (natp top-nodenum))
           (< (len (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print)) bound))
  :hints (("Goal" :use (:instance <=-of-len-of-drop-non-supporters-array-with-name)
           :in-theory (disable <=-of-len-of-drop-non-supporters-array-with-name))))

(defthm pseudo-dagp-of-drop-non-supporters-array-with-name
  (implies (and (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
           (pseudo-dagp (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print)))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array-with-name))))

(verify-guards drop-non-supporters-array-with-name
  :hints (("Goal" :use (:instance pseudo-dagp-of-drop-non-supporters-array-with-name)
           :in-theory (e/d (acl2-numberp-when-natp
                            alistp-when-pseudo-dagp)
                           (pseudo-dagp-of-drop-non-supporters-array-with-name
                            top-nodenum)))))

;; use phrase this using top-nodenum
(defthm <=-of-car-of-car-of-drop-non-supporters-array-with-name
  (implies (and (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
           (<= (car (car (drop-non-supporters-array-with-name dag-array-name dag-array top-nodenum print)))
               *max-1d-array-index*))
  :hints (("Goal" :use (:instance <=-of-len-of-drop-non-supporters-array-with-name)
           :in-theory (e/d (car-of-car-when-pseudo-dagp) (<=-of-len-of-drop-non-supporters-array-with-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Returns (mv renamed-smaller-nodenum renamed-larger-nodenum dag).
;; Only used by the equivalence checker.
;; The "-with-name" suffix indicates that this function takes the dag-array-name as an argument.
(defund drop-non-supporters-array-two-nodes-with-name (dag-array-name dag-array smaller-nodenum larger-nodenum)
  (declare (xargs :guard (and (natp larger-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 larger-nodenum))
                              (natp smaller-nodenum)
                              (< smaller-nodenum larger-nodenum)
                              (<= larger-nodenum *max-1d-array-index*))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :in-theory (enable pseudo-dag-arrayp  ;fixme?
                                                    )))))
  (let* ((tag-array (tag-supporters-of-nodes-with-name (list smaller-nodenum larger-nodenum) (max smaller-nodenum larger-nodenum) dag-array-name dag-array 'tag-array (+ 1 larger-nodenum)))
         (translation-array (make-empty-array 'translation-array (+ 1 larger-nodenum))))
    (mv-let (dag-lst translation-array)
            (build-reduced-dag-with-name 0 larger-nodenum dag-array-name dag-array tag-array 0 translation-array nil)
            (mv (aref1 'translation-array translation-array smaller-nodenum)
                (aref1 'translation-array translation-array larger-nodenum)
                dag-lst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Removes irrelevant nodes (nodes that do not support the top node) and renumbers the remaining nodes.
;; Returns a dag or a quotep.  Uses arrays internally for speed.
;; Smashes the arrays 'tag-array and 'translation-array and 'dag-array-for-drop-non-supporters.
(defund drop-non-supporters (dag-or-quotep)
  (declare (xargs :guard (or (and (pseudo-dagp dag-or-quotep)
                                  (<= (top-nodenum-of-dag dag-or-quotep) *max-1d-array-index*))
                             (myquotep dag-or-quotep))
                  :guard-hints (("Goal" :in-theory (enable
                                                    pseudo-dagp ;todo
                                                    TOP-NODENUM-OF-DAG
                                                    )))))
  (if (quotep dag-or-quotep)
      dag-or-quotep
    (let* ((dag-array-name 'dag-array-for-drop-non-supporters)
           (dag-array (make-dag-into-array dag-array-name dag-or-quotep 0))
           (top-nodenum (top-nodenum-of-dag dag-or-quotep)))
      (drop-non-supporters-array-with-name dag-array-name
                                           dag-array
                                           top-nodenum
                                           nil ; print
                                           ))))

(defthm true-listp-of-drop-non-supporters
  (implies (or (pseudo-dagp dag-or-quotep)
               (myquotep dag-or-quotep))
           (true-listp (drop-non-supporters dag-or-quotep)))
  :hints (("Goal" :in-theory (enable drop-non-supporters))))

(defthm pseudo-dagp-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep))
                    *max-1d-array-index*))
           (pseudo-dagp (drop-non-supporters dag-or-quotep)))
  :hints (("Goal" :cases ((< 0 (car (car dag-or-quotep))))
           :in-theory (enable drop-non-supporters
                              len-when-pseudo-dagp))))

(defthm <=-of-len-of-drop-non-supporters
  (implies (pseudo-dagp dag-or-quotep)
           (<= (len (drop-non-supporters dag-or-quotep))
               (len dag-or-quotep)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable drop-non-supporters
                                     len-when-pseudo-dagp))))

(defthm <=-of-len-of-drop-non-supporters-2-linear
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (top-nodenum-of-dag dag-or-quotep) *max-1d-array-index*))
           (<= (len (drop-non-supporters dag-or-quotep))
               (+ 1 *max-1d-array-index*)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable drop-non-supporters
                                     len-when-pseudo-dagp))))

(defthm consp-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep)) *max-1d-array-index*))
           (consp (drop-non-supporters dag-or-quotep)))
  :hints (("Goal" :in-theory (enable drop-non-supporters))))

(defthm <-of-0-and-len-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep)) *max-1d-array-index*))
           (< 0 (len (drop-non-supporters dag-or-quotep))))
  :hints (("Goal" :use (:instance consp-of-drop-non-supporters)
           :in-theory (disable consp-of-drop-non-supporters))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extracts the subdag with only the nodes needed to support NODENUM-OR-QUOTEP.
;this builds some arrays to do its job fast
;maybe some callers of this function would be okay with just the result of the nthcdr
;might have non-supporting pairs - but maybe they'll get simplified away anyway?
;on the other hand, it's probably better to throw them away before doing a rewrite?
(defund get-subdag (nodenum-or-quotep dag)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (pseudo-dagp dag)
                                  (natp nodenum-or-quotep)
                                  (< nodenum-or-quotep (len dag))
                                  (<= nodenum-or-quotep *max-1d-array-index*)
                                  ))
                  :guard-hints (("Goal" :in-theory (enable car-of-nth-when-pseudo-dagp)))
                  ))
  (if (quotep nodenum-or-quotep)
      nodenum-or-quotep
    (drop-non-supporters (nthcdr (+ -1 (- (len dag) nodenum-or-quotep)) dag) ;this requires the nodenums be consecutive
                         )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns a list of the indices whose elements in the array are non-nil (smaller indices come first)
;; The "-with-name" suffix indicates that this function takes the tag-array-name as an argument.
(defund harvest-non-nil-indices-with-name (n tag-array-name array acc)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (array1p tag-array-name array)
                              (rationalp n)
                              (< n (alen1 tag-array-name array)))))
  (if (not (natp n))
      acc
    (harvest-non-nil-indices-with-name (+ -1 n) tag-array-name array
                             (if (aref1 tag-array-name array n)
                                 (cons n acc)
                               acc))))

(local
  (defthm true-listp-of-harvest-non-nil-indices-with-name
    (equal (true-listp (harvest-non-nil-indices-with-name n tag-array-name array acc))
           (true-listp acc))
    :hints (("Goal" :in-theory (enable harvest-non-nil-indices-with-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of the nodenums that support NODENUM (a node counts as its own supporter).
;; See also make-supporters-array.
;; TODO: Make a version that builds in the array name (as 'tag-array-for-supporters?).
;; TODO: Make a variant that, instead of calling harvest-non-nil-indices-with-name, simply checks whether a given node of interest is among the supporters.
;; The "-with-name" suffix indicates that this function takes the dag-array-name as an argument.
(defund supporters-of-node-with-name (nodenum dag-array-name dag-array tag-array-name)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (symbolp tag-array-name))))
  (let* ((tag-array (tag-supporters-of-node-with-name nodenum dag-array-name dag-array tag-array-name (+ 1 nodenum))))
    (harvest-non-nil-indices-with-name nodenum tag-array-name tag-array nil)))

(defthm true-listp-of-supporters-of-node-with-name
  (true-listp (supporters-of-node-with-name nodenum dag-array-name dag-array tag-array-name))
  :hints (("Goal" :in-theory (enable supporters-of-node-with-name))))
