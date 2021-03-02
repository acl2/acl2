; Computing sets of DAG nodes that support DAG nodes
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
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(local (in-theory (disable (:i alistp))))

;; ;kill
;; (defthm memberp-of-maxelem-same
;;   (implies (consp x)
;;            (memberp (maxelem x) x))
;;   :hints (("Goal" :in-theory (enable maxelem memberp))))

(defthm member-equal-of-maxelem-same
  (implies (consp x)
           (member-equal (maxelem x) x))
  :hints (("Goal" :in-theory (enable maxelem member-equal))))

;move
(defthm all-<-forward-to-posp-when-all-natp
  (implies (and (all-< items x)
                (all-natp items)
                (consp items)
                (integerp x))
           (posp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all-<))))

;move
(defthm reverse-becomes-reverse-list-gen
  (implies (not (stringp x))
           (equal (reverse x)
                  (reverse-list x)))
  :hints
  (("Goal"
    :in-theory (enable reverse reverse-list revappend-lemma))))

;move
(local
 (defthm stringp-of-reverse
   (equal (stringp (reverse x))
          (stringp x))
   :hints (("Goal" :in-theory (enable reverse)))))

(local
 (defthm stringp-of-reverse-type
   (implies (stringp x)
            (stringp (reverse x)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable reverse)))))

;move
(defthm all-<-of-reverse
  (implies t;(true-listp x)
           (equal (all-< (reverse x) bound)
                  (all-< x bound)))
  :hints (("Goal" :cases ((stringp x))
           :in-theory (e/d (reverse-becomes-reverse-list) ()))))

;; ;move
;; (defthm all-<-of-aref1-list-aux-when-bounded-translation-arrayp-aux
;;   (implies (and (bounded-translation-arrayp-aux nodenum2 translation-array bound2)
;;                 (<= bound2 bound)
;;                 (all-<= nodenums nodenum2)
;;                 (all-natp nodenums)
;;                 (natp nodenum2)
;;                 ;(aref1 'translation-array translation-array nodenum)
;;                 ;(not (consp (aref1 'translation-array translation-array nodenum)))
;;                 (all-integerp (aref1-list 'translation-array translation-array nodenums))
;;                 (all-< acc bound)
;;                 )
;;            (all-< (aref1-list-aux 'translation-array translation-array nodenums acc)
;;                   bound))
;;   :hints (("Goal" :in-theory (enable aref1-list-aux AREF1-LIST))))

;; (defthm all-<-of-aref1-list-when-bounded-translation-arrayp-aux
;;   (implies (and (bounded-translation-arrayp-aux nodenum2 translation-array bound2)
;;                 (<= bound2 bound)
;;                 (all-<= nodenums nodenum2)
;;                 (all-natp nodenums)
;;                 (natp nodenum2)
;;                 ;(aref1 'translation-array translation-array nodenum)
;;                 ;(not (consp (aref1 'translation-array translation-array nodenum)))
;;                 (all-integerp (aref1-list 'translation-array translation-array nodenums))
;;                 )
;;            (all-< (aref1-list 'translation-array translation-array nodenums)
;;                   bound))
;;   :hints (("Goal" :in-theory (enable aref1-list))))

;;;
;;; tag-nodenums
;;;

;Set the tag bit for each thing in ITEMS that is a nodeum.  ITEMS are nodenums
;or quoted constants.
(defund tag-nodenums (items array-name array)
  (declare (xargs :guard (and (array1p array-name array)
                              (true-listp items)
                              (all-dargp-less-than items (alen1 array-name array)))))
  (if (endp items)
      array
    (let ((item (first items)))
      (if (consp item) ;; test for quoted constant
          (tag-nodenums (cdr items) array-name array)
        (tag-nodenums (cdr items) array-name (aset1 array-name array item t))))))

(defthm alen1-of-tag-nodenums
  (implies (all-dargp-less-than items (alen1 array-name array))
           (equal (alen1 array-name (tag-nodenums items array-name array))
                  (alen1 array-name array)))
  :hints (("Goal" :in-theory (enable tag-nodenums))))

(defthm array1p-of-tag-nodenums
  (implies (and (array1p array-name array)
                (all-dargp-less-than items (alen1 array-name array)))
           (array1p array-name (tag-nodenums items array-name array)))
  :hints (("Goal" :in-theory (enable tag-nodenums))))

;; the tag doesn't become unset
(defthm aref1-of-tag-nodenums-when-aref1
  (implies (and (aref1 tag-array-name tag-array nodenum)
                (array1p tag-array-name tag-array)
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array))
                (all-dargp-less-than items (alen1 tag-array-name tag-array)))
           (aref1 tag-array-name (tag-nodenums items tag-array-name tag-array) nodenum))
  :hints (("Goal" :in-theory (enable tag-nodenums))))

;;;
;;; all-taggedp
;;;

;; Check that each of the NODENUMS is tagged in the array
(defund all-taggedp (nodenums array-name array)
  (declare (xargs :guard (and (array1p array-name array)
                              (nat-listp nodenums)
                              (all-< nodenums (alen1 array-name array)))))
  (if (endp nodenums)
      t
    (and (aref1 array-name array (first nodenums))
         (all-taggedp (rest nodenums) array-name array))))

(defthm all-taggedp-of-aset1-list
  (implies (and (array1p tag-array-name array)
                (all-natp nodenums)
                (all-< nodenums (alen1 tag-array-name array)))
           (all-taggedp nodenums tag-array-name (aset1-list tag-array-name array nodenums 't)))
  :hints (("Goal" :in-theory (enable all-taggedp aset1-list))))

(defthm all-taggedp-of-aset1-of-t-when-all-taggedp
  (implies (and (all-taggedp nodenums tag-array-name tag-array)
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array))
                (all-natp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array))
                (array1p tag-array-name tag-array)
                )
           (all-taggedp nodenums tag-array-name (aset1 tag-array-name tag-array nodenum t)))
  :hints (("Goal" :in-theory (enable all-taggedp))))

;; tags don't become unset
(defthm all-taggedp-of-tag-nodenums-when-all-taggedp
  (implies (and (all-taggedp nodenums tag-array-name tag-array)
                (all-dargp-less-than nodenums2 (alen1 tag-array-name tag-array))
                (all-natp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array))
                (array1p tag-array-name tag-array))
           (all-taggedp nodenums tag-array-name (tag-nodenums nodenums2 tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable all-taggedp tag-nodenums))))

;;;
;;; tagging supporters
;;;

;processes the nodes top down in order
;before calling this, you should tag the node(s) whose supporters you want to compute (by setting their entries in the tag-array to t)
;if a node is tagged when we reach it, its children get tagged too
;could also use a worklist algorithm (might be better if the number of tagged nodes will be small - saves looping over the whole array)
(defund tag-supporters (n dag-array-name dag-array tag-array-name tag-array)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (integerp n)
                              (<= -1 n)
                              (implies (natp n)
                                       (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                                            (array1p tag-array-name tag-array)
                                            (< n (alen1 tag-array-name tag-array)))))
                  :split-types t)
           (type (integer -1 2147483645) n))
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
                (tag-supporters (+ -1 n) dag-array-name dag-array tag-array-name tag-array)
              (let ((args (dargs expr)))
                (tag-supporters (+ -1 n) dag-array-name dag-array tag-array-name (tag-nodenums args tag-array-name tag-array)))))
        ;;node isn't tagged
        (tag-supporters (+ -1 n) dag-array-name dag-array tag-array-name tag-array)))))

(defthm alen1-of-tag-supporters
  (implies (and (natp top-nodenum)
                (array1p tag-array-name tag-array)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (< top-nodenum (alen1 tag-array-name tag-array)))
           (equal (alen1 tag-array-name (tag-supporters top-nodenum dag-array-name dag-array tag-array-name tag-array))
                  (alen1 tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters)
           :expand ((tag-supporters 0 dag-array-name
                                    dag-array tag-array-name tag-array))
           :do-not '(generalize eliminate-destructors))))

(defthm array1p-of-tag-supporters
  (implies (and (natp top-nodenum)
                (array1p tag-array-name tag-array)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                (< top-nodenum (alen1 tag-array-name tag-array)))
           (array1p tag-array-name (tag-supporters top-nodenum dag-array-name dag-array tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters)
           :expand ((TAG-SUPPORTERS 0 DAG-ARRAY-NAME
                                    DAG-ARRAY TAG-ARRAY-NAME TAG-ARRAY))
           :do-not '(generalize eliminate-destructors))))

;; the tag doesn't become unset
(defthm aref1-of-tag-supporters-when-aref1
  (implies (and (aref1 tag-array-name tag-array nodenum)
                ;; the guard:
                (and (integerp n)
                     (implies (natp n)
                              (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                                   (array1p tag-array-name tag-array)
                                   (< n (alen1 tag-array-name tag-array)))))
                (natp nodenum)
                (< nodenum (alen1 tag-array-name tag-array)))
           (aref1 tag-array-name (tag-supporters n dag-array-name dag-array tag-array-name tag-array) nodenum))
  :hints (("Goal" :in-theory (enable tag-supporters))))

;; tags don't become unset
(defthm all-taggedp-of-tag-supporters-when-all-taggedp
  (implies (and (all-taggedp nodenums tag-array-name tag-array)
                ;; the guard:
                (integerp n)
                (implies (natp n)
                         (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                              (array1p tag-array-name tag-array)
                              (< n (alen1 tag-array-name tag-array))))
                (all-natp nodenums)
                (all-< nodenums (alen1 tag-array-name tag-array))
                )
           (all-taggedp nodenums tag-array-name (tag-supporters n dag-array-name dag-array tag-array-name tag-array)))
  :hints (("Goal" :in-theory (enable tag-supporters NAT-LISTP))))

;; Returns the TAG-ARRAY, named TAG-ARRAY-NAME, which maps each nodenum to a
;; boolean indicating whether it is a supporter of any of the NODENUMS (nodes
;; are considered their own supporters).
;; rename make-supporters-tag-array-for-nodes
(defund tag-supporters-of-nodes (nodenums
                                 dag-array-name dag-array
                                 tag-array-name ;; the name of the tag array to create
                                 tag-array-length ;; the array length to use  -- if we might look up nodes higher than the nodenums, we can make this larger than (+ 1 (maxelem nodenums)) to prevent errors
                                 )
  (declare (xargs :guard (and (true-listp nodenums)
                              (all-natp nodenums)
                              (consp nodenums) ;so we can call maxelem
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                              (integerp tag-array-length)
                              (all-< nodenums tag-array-length) ;implies that tag-array-length is positive
                              (<= tag-array-length 2147483646)
                              (symbolp tag-array-name))))
  (let* ((tag-array (make-empty-array tag-array-name tag-array-length))
         (tag-array (aset1-list tag-array-name tag-array nodenums t)))
    (tag-supporters (maxelem nodenums) dag-array-name dag-array tag-array-name tag-array)))

(defthm array1p-of-tag-supporters-of-nodes
  (implies (and (all-natp nodenums)
                (consp nodenums)
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums))))
           (array1p tag-array-name (tag-supporters-of-nodes nodenums dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (e/d (tag-supporters-of-nodes) (natp)))))

(defthm alen1-of-tag-supporters-of-nodes
  (implies (and (all-natp nodenums)
                (consp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (equal (alen1 tag-array-name (tag-supporters-of-nodes nodenums dag-array-name dag-array tag-array-name tag-array-length))
                  tag-array-length))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes))))

(defthm aref1-of-tag-supporters-of-nodes-and-maxelem
  (implies (and (all-natp nodenums)
                (consp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (aref1 tag-array-name
                  (tag-supporters-of-nodes nodenums dag-array-name dag-array tag-array-name tag-array-length)
                  (maxelem nodenums)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes maxelem))))

(defthm all-taggedp-of-tag-supporters-of-nodes-same
  (implies (and (all-natp nodenums)
                (consp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (all-< nodenums tag-array-length))
           (all-taggedp nodenums tag-array-name (tag-supporters-of-nodes nodenums dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-nodes
                                     all-taggedp))))

;; Special case for one node
;; rename make-supporters-tag-array-for-node
(defund tag-supporters-of-node (nodenum
                               dag-array-name dag-array
                               tag-array-name ;; the name of the tag array to create
                               tag-array-length ;if we might look up nodes higher than nodenum, we can make this larger than (+ 1 nodenum) to prevent errors
                               )
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (integerp tag-array-length)
                              (< nodenum tag-array-length) ;implies that tag-array-length is positive
                              (<= tag-array-length 2147483646)
                              (symbolp tag-array-name))))
  (tag-supporters-of-nodes (list nodenum) dag-array-name dag-array tag-array-name tag-array-length))

(defthm array1p-of-tag-supporters-of-node
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (array1p tag-array-name (tag-supporters-of-node nodenum dag-array-name dag-array tag-array-name tag-array-length)))
  :hints (("Goal" :in-theory (enable tag-supporters-of-node))))

(defthm alen1-of-tag-supporters-of-node
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (equal (alen1 tag-array-name (tag-supporters-of-node nodenum dag-array-name dag-array tag-array-name tag-array-length))
                  tag-array-length))
  :hints (("Goal" :in-theory (enable tag-supporters-of-node))))

(defthm aref1-of-tag-supporters-of-node
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (posp tag-array-length)
                (<= tag-array-length 2147483646)
                (symbolp tag-array-name)
                (< nodenum tag-array-length))
           (aref1 tag-array-name
                  (tag-supporters-of-node nodenum dag-array-name dag-array tag-array-name tag-array-length)
                  nodenum))
  :hints (("Goal" :use (:instance aref1-of-tag-supporters-of-nodes-and-maxelem (nodenums (list nodenum)))
           :in-theory (e/d (tag-supporters-of-node) (aref1-of-tag-supporters-of-nodes-and-maxelem)))))

;;;
;;; dropping non-supporters
;;;

;returns (mv dag-lst translation-array)
;takes arrays but returns a dag-lst
;the name of translation-array must be 'translation-array
;the name of tag-array must be 'tag-array
;the name of dag-array must be dag-array-name
;todo: avoid making a node that is a quotep (but then consider what to do about possible duplicates caused by that)?
(defund build-reduced-dag2 (n top-nodenum dag-array-name dag-array tag-array
                              dag-len ;the next nodenum to use in the new DAG
                              translation-array dag-acc)
  (declare (xargs :measure (+ 1 (nfix (+ 1 (- top-nodenum n))))
                  :guard-hints (("Goal" :in-theory (enable pseudo-dag-arrayp))) ;fixme?
                  :guard (and (array1p 'translation-array translation-array)
                              (array1p 'tag-array tag-array)
                              (alistp dag-acc)
                              (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                              (natp n)
                              (natp dag-len)
                              (< top-nodenum (alen1 'tag-array tag-array))
                              (< top-nodenum (alen1 'translation-array translation-array))
                              (<= n (+ 1 top-nodenum))
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp top-nodenum)))
          (> n top-nodenum))
      (mv dag-acc translation-array)
    (let ((tag (aref1 'tag-array tag-array n))) ;only nodes that are tagged get put into the result
      (if (not tag) ;drop it and don't increment the dag-len
          (build-reduced-dag2 (+ 1 n) top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)
        (let* ((expr (aref1 dag-array-name dag-array n))
               (expr (if (or (variablep expr)
                             (fquotep expr)) ;todo: maybe inline constants
                         expr
                       (let* ((fn (ffn-symb expr))
                              (args (dargs expr))
                              (new-args (translate-args args translation-array)))
                         (cons fn new-args))))
               (translation-array (aset1 'translation-array translation-array n dag-len))
               (dag-acc (acons-fast dag-len expr dag-acc)))
          (build-reduced-dag2 (+ 1 n) top-nodenum dag-array-name dag-array tag-array (+ 1 dag-len) translation-array dag-acc))))))

(defthm consp-mv-nth-0-of-translation-array-after-build-reduced-dag2
  (implies (consp dag-acc)
           (consp (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag2))))

(defthm alen1-of-translation-array-after-build-reduced-dag2
  (equal (alen1 'translation-array (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
         (alen1 'translation-array translation-array))
  :hints (("Goal" :in-theory (enable build-reduced-dag2))))

(defthm array1p-of-translation-array-after-build-reduced-dag2
  (implies (and (array1p 'translation-array translation-array)
                (<= 0 n)
                (<= n top-nodenum)
                (< top-nodenum (alen1 'translation-array translation-array)))
           (array1p 'translation-array (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag2)
           :expand ((build-reduced-dag2 n n dag-array-name
                                        dag-array tag-array dag-len
                                        translation-array dag-acc)))))

(defthm bounded-translation-arrayp-aux-of-translation-array-after-build-reduced-dag2
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
                (all-natp (strip-cars dag-acc))
                )
           (bounded-translation-arrayp-aux (top-nodenum (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
                                           (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                           (+ 1 (car (car (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))))))
  :hints (;; ("subgoal *1/1" :use (:instance BOUNDED-TRANSLATION-ARRAYP-AUX-MONOTONE
          ;;                                 (BOUND (+ 1 (CAR (CAR DAG-ACC))))
          ;;                                 (TRANSLATION-ARRAY TRANSLATION-ARRAY)
          ;;                                 (NODENUM (CAR (CAR DAG-ACC)))
          ;;                                 (nodenum2 (+ -1 N))
          ;;                                 (bound2 (+ 1 (CAR (CAR DAG-ACC)))))
          ;;  :in-theory (disable BOUNDED-TRANSLATION-ARRAYP-AUX-MONOTONE))
          ("Goal" :in-theory (enable build-reduced-dag2)
           :expand ((build-reduced-dag2 n n dag-array-name
                                        dag-array tag-array dag-len
                                        translation-array dag-acc)))))

(defthm build-reduced-dag2-type
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
                ;;(consp (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
                )
           (pseudo-dagp-aux (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                            (if (consp (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
                                (car (car (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
                              -1)))
  :hints (("subgoal *1/1" :cases ((equal 0 dag-len)))
          ("Goal" :induct (build-reduced-dag2 n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1)
                    ;;(pseudo-dagp-aux dag-acc (car (car dag-acc)))
                    )
           :in-theory (e/d (build-reduced-dag2 ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                            )))))

(defthm consp-of-mv-nth-0-of-build-reduced-dag2
  (implies (and (aref1 'tag-array tag-array top-nodenum) ;since the top-nodenum is tagged, the result cannot be empty
                (natp top-nodenum)
                (natp n)
                (<= n top-nodenum))
           (consp (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))
  :hints (("Goal" :induct (build-reduced-dag2 n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1))
           :in-theory (e/d (build-reduced-dag2 ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                               )))))

(defthm natp-of-car-of-car-of-mv-nth-0-of-build-reduced-dag2
  (implies (and (aref1 'tag-array tag-array top-nodenum) ;since the top-nodenum is tagged, the result cannot be empty
                (natp top-nodenum)
                (natp n)
                (<= n top-nodenum)
                (natp dag-len))
           (natp (car (car (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))))))
  :hints (("Goal" :induct (build-reduced-dag2 n top-nodenum
                                              dag-array-name dag-array tag-array
                                              dag-len translation-array dag-acc)
           :expand ((pseudo-dagp-aux dag-acc -1))
           :in-theory (e/d (build-reduced-dag2 ; pseudo-dagp-aux
                            ) (                ;dag-exprp
                            )))))

(defthm pseudo-dagp-of-mv-nth-0-of-build-reduced-dag2
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
           (pseudo-dagp
            (mv-nth 0
                    (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array
                                        dag-len ;the next nodenum to use in the new dag
                                        translation-array dag-acc))))
  :hints (("Goal" :use (build-reduced-dag2-type
                        consp-of-mv-nth-0-of-build-reduced-dag2)
           :expand ()
           :in-theory (e/d (pseudo-dagp) (natp build-reduced-dag2-type
                                               consp-of-mv-nth-0-of-build-reduced-dag2
                                               ;;pseudo-dagp-aux-of-car-of-car-when-pseudo-dagp-aux
                                               )))))

(defthm true-listp-of-mv-nth-0-of-build-reduced-dag2
  (implies (true-listp dag-acc)
           (true-listp
            (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array
                                          dag-len translation-array dag-acc))))
  :hints (("Goal" :in-theory (enable build-reduced-dag2))))

(defthm <=-of-len-of-mv-nth-0-of-build-reduced-dag2
  (implies (and (natp n)
                (natp top-nodenum)
                (<= n (+ 1 top-nodenum)))
           (<= (len (mv-nth 0 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc)))
               (+ (len dag-acc)
                  (+ 1 (- top-nodenum n)))))
  :hints (("Goal" :in-theory (enable build-reduced-dag2))))

(defthm <=-of-len-of-mv-nth-0-of-build-reduced-dag2-special
  (implies (natp top-nodenum)
           (<= (len (mv-nth 0 (build-reduced-dag2 0 top-nodenum dag-array-name dag-array tag-array dag-len translation-array nil)))
               (+ 1 top-nodenum)))
  :hints (("Goal" :use (:instance <=-of-len-of-mv-nth-0-of-build-reduced-dag2 (dag-acc nil) (n 0))
           :in-theory (disable <=-of-len-of-mv-nth-0-of-build-reduced-dag2))))

(defthm aref1-of-mv-nth-1-of-build-reduced-dag2-too-low
  (implies (and (natp nodenum)
                (< nodenum n)
                (array1p 'translation-array translation-array)
                (natp n)
                (< top-nodenum (alen1 'translation-array translation-array))
                (<= n (+ 1 top-nodenum))
                )
           (equal (aref1 'translation-array
                         (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                         nodenum)
                  (aref1 'translation-array
                         translation-array
                         nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag2) (natp)))))

;; nodenum doesn't become unset in the translation-array
(defthm natp-of-aref1-of-mv-nth-1-of-build-reduced-dag2-when-natp-of-aref1
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
                        (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                        nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag2) (natp)))))

(defthm natp-of-aref1-of-mv-nth-1-of-build-reduced-dag2-when-tagged
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
                        (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                        nodenum)))
  :hints (("Goal" :in-theory (e/d (build-reduced-dag2) (natp)))))

(defthm nat-listp-of-aref1-list-aux-of-mv-nth-1-of-build-reduced-dag2-when-all-taggedp
  (implies (and (all-taggedp nodenums 'tag-array tag-array)
                (all-natp nodenums)
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
                                      (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                      nodenums
                                      acc)))
  :hints (("Goal" :in-theory (e/d (nat-listp aref1-list-aux ALL-TAGGEDP) (natp)))))

(defthm nat-listp-of-aref1-list-of-mv-nth-1-of-build-reduced-dag2-when-all-taggedp
  (implies (and (all-taggedp nodenums 'tag-array tag-array)
                (all-natp nodenums)
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
                                  (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
                                  nodenums)))
  :hints (("Goal" :in-theory (e/d (aref1-list) ()))))

;; (thm
;;  (implies (and (all-taggedp nodenums 'tag-array tag-array)
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
;;                        (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
;;                        nodenum)))
;;  :hints (("Goal" :in-theory (e/d (build-reduced-dag2) (natp)))))

;; (thm
;;  (implies (and (all-taggedp nodenums 'tag-array tag-array)
;;                (all-natp nodenums)
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
;;                                  (mv-nth 1 (build-reduced-dag2 n top-nodenum dag-array-name dag-array tag-array dag-len translation-array dag-acc))
;;                                  nodenums)))
;;  :hints (("Goal" :in-theory (enable nat-listp))))

;takes an array but returns a dag-lst
;smashes the arrays 'tag-array and 'translation-array
;bad to use the name 'tag-array here?
;better to use a worklist algorithm? maybe not..
(defund drop-non-supporters-array (dag-array-name dag-array top-nodenum print)
  (declare (xargs :guard (and (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))))
           (ignore print))
  (let* ((tag-array (tag-supporters-of-node top-nodenum dag-array-name dag-array 'tag-array (+ 1 top-nodenum)))
         (translation-array (make-empty-array 'translation-array (+ 1 top-nodenum))))
    (mv-let (dag-lst translation-array)
            (build-reduced-dag2 0 top-nodenum dag-array-name dag-array tag-array 0 translation-array nil)
            (declare (ignore translation-array))
            dag-lst)))

(defthm true-listp-of-drop-non-supporters-array
  (true-listp (drop-non-supporters-array dag-array-name dag-array top-nodenum print))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array))))

(defthm consp-of-drop-non-supporters-array
  (implies (and (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
           (consp (drop-non-supporters-array dag-array-name dag-array top-nodenum print)))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array))))

(defthm <=-of-len-of-drop-non-supporters-array
  (implies (natp top-nodenum)
           (<= (len (drop-non-supporters-array dag-array-name dag-array top-nodenum print))
               (+ 1 top-nodenum)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable DROP-NON-SUPPORTERS-ARRAY))))

(defthm pseudo-dagp-of-drop-non-supporters-array
  (implies (and (natp top-nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum)))
           (pseudo-dagp (drop-non-supporters-array dag-array-name dag-array top-nodenum print)))
  :hints (("Goal" :in-theory (enable drop-non-supporters-array))))

;returns (mv renamed-smaller-nodenum renamed-larger-nodenum dag-lst)
;; Only used by the equivalence checker.
(defund drop-non-supporters-array-two-nodes (dag-array-name dag-array smaller-nodenum larger-nodenum)
  (declare (xargs :guard (and (natp larger-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 larger-nodenum))
                              (natp smaller-nodenum)
                              (< smaller-nodenum larger-nodenum)
                              (<= larger-nodenum 2147483645))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :in-theory (enable pseudo-dag-arrayp  ;fixme?
                                                    )))))
  (let* ((tag-array (tag-supporters-of-nodes (list smaller-nodenum larger-nodenum) dag-array-name dag-array 'tag-array (+ 1 larger-nodenum)))
         (translation-array (make-empty-array 'translation-array (+ 1 larger-nodenum))))
    (mv-let (dag-lst translation-array)
            (build-reduced-dag2 0 larger-nodenum dag-array-name dag-array tag-array 0 translation-array nil)
            (mv (aref1 'translation-array translation-array smaller-nodenum)
                (aref1 'translation-array translation-array larger-nodenum)
                dag-lst))))

;; Removes irrelevant nodes (nodes that do not support the top node) and renumbers the remaining nodes.
;; Returns a dag or a quotep.  Uses arrays internally for speed.
;; Smashes the arrays 'tag-array and 'translation-array and 'dag-array-for-drop-non-supporters.
(defund drop-non-supporters (dag-or-quotep)
  (declare (xargs :guard (or (and (pseudo-dagp dag-or-quotep)
                                  (<= (car (car dag-or-quotep)) 2147483645))
                             (myquotep dag-or-quotep))
                  :guard-hints (("Goal" :in-theory (enable pseudo-dagp)))))
  (if (quotep dag-or-quotep)
      dag-or-quotep
    (let* ((dag-array-name 'dag-array-for-drop-non-supporters)
           (dag-array (make-into-array dag-array-name dag-or-quotep))
           (top-nodenum (top-nodenum dag-or-quotep)))
      (drop-non-supporters-array dag-array-name
                                 dag-array
                                 top-nodenum
                                 nil ;nil
                                 ))))

(defthm true-listp-of-drop-non-supporters
  (implies (or (pseudo-dagp dag-or-quotep)
               (myquotep dag-or-quotep))
           (true-listp (drop-non-supporters dag-or-quotep)))
  :hints (("Goal" :in-theory (enable drop-non-supporters))))

(defthm pseudo-dagp-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep))
                    2147483645))
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

(defthm consp-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep)) 2147483645))
           (consp (drop-non-supporters dag-or-quotep)))
  :hints (("Goal" :in-theory (enable drop-non-supporters))))

(defthm <-of-0-and-len-of-drop-non-supporters
  (implies (and (pseudo-dagp dag-or-quotep)
                (<= (car (car dag-or-quotep)) 2147483645))
           (< 0 (len (drop-non-supporters dag-or-quotep))))
  :hints (("Goal" :use (:instance consp-of-drop-non-supporters)
           :in-theory (disable consp-of-drop-non-supporters))))

;extracts the subdag with only the nodes needed to support the nodenum
;this builds some arrays to do its job fast
;maybe some callers of this function would be okay with just the result of the nthcdr
;might have non-supporting pairs - but maybe they'll get simplified away anyway?
;on the other hand, it's probably better to throw them away before doing a rewrite?
(defund get-subdag (nodenum-or-quotep dag)
  (if (quotep nodenum-or-quotep)
      nodenum-or-quotep
    (drop-non-supporters (nthcdr (+ -1 (- (len dag) nodenum-or-quotep)) dag) ;this requires the nodenums be consecutive
                         )))

;returns a list of the indices whose elements in the array are non-nil (smaller indices come first)
(defund harvest-non-nil-indices (n array-name array acc)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (array1p array-name array)
                              (rationalp n)
                              (< n (alen1 array-name array)))))
  (if (not (natp n))
      acc
    (harvest-non-nil-indices (+ -1 n) array-name array
                             (if (aref1 array-name array n)
                                 (cons n acc)
                               acc))))

(defthm true-listp-of-harvest-non-nil-indices
  (equal (true-listp (harvest-non-nil-indices n array-name array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable harvest-non-nil-indices))))

;returns a list of the nodenums that support NODENUM
;a node counts as its own supporter
;; See also make-supporters-array.
;; TODO: Make a version that builds in the array name (as 'tag-array-for-supporters?).
;; TODO: Make a variant that, instead of calling harvest-non-nil-indices, simply checks whether a given node of interest is among the supporters.
(defund supporters-of-node (nodenum dag-array-name dag-array tag-array-name)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (symbolp tag-array-name))))
  (let* ((tag-array (tag-supporters-of-node nodenum dag-array-name dag-array tag-array-name (+ 1 nodenum))))
    (harvest-non-nil-indices nodenum tag-array-name tag-array nil)))

(defthm true-listp-of-supporters-of-node
  (true-listp (supporters-of-node nodenum dag-array-name dag-array tag-array-name))
  :hints (("Goal" :in-theory (enable supporters-of-node))))
