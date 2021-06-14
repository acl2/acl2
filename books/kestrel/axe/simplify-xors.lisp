; A tool to normalize XOR nests in DAGs
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

;fixme improve this to handle bitnot/bvnot by introducing ones into the accumulated (xored) constant?

;can we now get rid of bitxor in favor of just bvxor?

;add some tests for this book
;ffixme read over this..
;ffixme generalize to any associative/commutative operators?  including ones with a leading size argument - will need to check that the sizes match..

;this can increase the dag size by removing sharing
;operands to bitxor/bvxor are sorted into decreasing order - i hope that helps with sharing
;all constants are combined and put first

;this may now efficiently handle even xor nests with an exponetial number of leaves.. - how will that apply to functions that don't have the nice property of xor that x xor x = 0
;well, for and and or, you can drop all but one of a set of equal operands

;BBOZO handle negations! -well, we handle xoring with 1, right?

(include-book "kestrel/axe/equivalent-dags" :dir :system)
(include-book "kestrel/axe/add-bitxor-nest-to-dag-array" :dir :system)
(include-book "kestrel/axe/add-bvxor-nest-to-dag-array" :dir :system)
(include-book "kestrel/axe/supporting-nodes" :dir :system) ;for drop-non-supporters-array
(include-book "kestrel/axe/dag-array-builders2" :dir :system)
(include-book "kestrel/axe/def-dag-builder-theorems" :dir :system)
(include-book "kestrel/axe/translation-array" :dir :system)
(include-book "kestrel/axe/merge-sort-less-than" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;(local (in-theory (disable car-becomes-nth-of-0)))

(in-theory (disable rational-listp))

(local (in-theory (disable NAT-LISTP
                           DAG-EXPRP0
                           ;;LIST::LEN-WHEN-AT-MOST-1
                           all-natp-when-not-consp
                           all-<-when-not-consp
                           all-dargp-when-not-consp
                           ;; for speed:
                           all-<=-when-not-consp
                           ALL-<-TRANSITIVE-FREE
                           NOT-<-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-2
                           <=-OF-NTH-WHEN-ALL-<= ;disable globally?
                           )))

(local (in-theory (enable consp-of-cdr
                          nth-of-cdr
                          myquotep-of-nth-when-all-dargp
                          <=-of-nth-when-all-<= ;todo
                          <-of-+-of-1-when-integers
                          )))

;move
; can help when backchaining
(defthmd <-of-+-of-1-when-integerp
  (implies (and (integerp x)
                (integerp y))
           (equal (< x (+ 1 y))
                  (<= x y))))

(local (in-theory (disable <-of-+-of-1-when-integerp)))


(defthm consp-of-nth-forward-to-consp
  (implies (consp (nth n x))
           (consp x))
  :rule-classes :forward-chaining)

;(local (in-theory (enable ALL-myquotep))) ;todo

;move
(defthm <-of-maxelem-and-maxelem-of-cdr
  (implies (consp (cdr x))
           (not (< (maxelem x) (maxelem (cdr x))))))




;defforall could do these too?
(defthm all-integerp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-integerp lst)
                (all-integerp acc)
                (<= (len tail) (len lst)))
           (all-integerp (mv-nth 0 (split-list-fast-aux lst tail acc)))))

(defthm all-integerp-of-mv-nth-0-of-split-list-fast
  (implies (all-integerp lst)
           (all-integerp (mv-nth 0 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) ()))))

(defthm all-integerp-of-mv-nth-1-of-split-list-fast-aux
  (implies (all-integerp lst)
           (all-integerp (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm all-integerp-of-mv-nth-1-split-list-fast
  (implies (all-integerp lst)
           (all-integerp (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (e/d (split-list-fast) (SPLIT-LIST-FAST-AUX)))))

;; ;fixme defforall should do this?
;; (defthm all-integerp-of-revappend
;;   (implies (and (all-integerp x)
;;                 (all-integerp y))
;;            (all-integerp (revappend x y)))
;;   :hints (("Goal" :in-theory (enable revappend))))

(defthm all-integerp-of-merge-<
  (implies (and (all-integerp l1)
                (all-integerp l2)
                (all-integerp acc))
           (all-integerp (merge-< l1 l2 acc)))
  :hints (("Goal" :in-theory (enable all-integerp merge-<))))

(defthm all-integerp-of-merge-sort-<
  (implies (and (all-integerp lst)
                (true-listp lst))
           (all-integerp (merge-sort-< lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-sort-<) ()))))

(defthm all-dargp-less-than-of-merge-sort-<
  (implies (all-dargp-less-than items bound)
           (all-dargp-less-than (merge-sort-< items) bound)))

(defund decreasingp (items)
  (declare (xargs :guard (and (true-listp items)
                              (all-integerp items))))
  (if (endp items)
      t
    (if (endp (cdr items))
        t
      (and (> (first items) (second items))
           (decreasingp (rest items))))))

(defthmd maxelem-when-decreasingp
  (implies (and (decreasingp items)
                )
           (equal (maxelem items)
                  (if (consp items)
                      (car items)
                    (negative-infinity))))
  :hints (("Goal" :in-theory (enable decreasingp))))

(local (in-theory (enable maxelem-when-decreasingp)))

(defthm decreasingp-of-cdr
 (implies (decreasingp items)
          (decreasingp (cdr items)))
 :hints (("Goal" :in-theory (enable decreasingp))))

;list should be sorted in decreasing order
;the bitxor/bvxor of everything in the return value should be equal to the bitxor/bvxor of ITEM and everything in LIST
;slow? not sure i can get around it.  could we use a btree?
(defund insert-into-sorted-list-and-remove-dups (item list)
  (declare (xargs :guard (and (integerp item)
                              (all-integerp list) ;use integer-listp?
                              )))
  (if (atom list) ;use endp?
      (list item)
    (let ((first-item (car list)))
      (if (< first-item item)
          (cons item list)
        (if (eql item first-item)
            ;;drop them both:
            (cdr list)
          (cons first-item (insert-into-sorted-list-and-remove-dups item (cdr list))))))))


(defthm all-integerp-of-insert-into-sorted-list-and-remove-dups
  (implies (integerp item)
           (equal (all-integerp (insert-into-sorted-list-and-remove-dups item list))
                  (all-integerp list)))
  :hints (("Goal" :in-theory (enable insert-into-sorted-list-and-remove-dups))))

(defthm all-natp-of-insert-into-sorted-list-and-remove-dups
  (implies (natp item)
           (equal (all-natp (insert-into-sorted-list-and-remove-dups item list))
                  (all-natp list)))
  :hints (("Goal" :in-theory (enable insert-into-sorted-list-and-remove-dups))))

(defthm true-listp-of-insert-into-sorted-list-and-remove-dups
  (implies (true-listp list)
           (true-listp (insert-into-sorted-list-and-remove-dups item list)))
  :hints (("Goal" :in-theory (enable insert-into-sorted-list-and-remove-dups))))

(defthm all-<-of-insert-into-sorted-list-and-remove-dups
  (implies (and (< item bound)
                (all-< list bound))
           (all-< (insert-into-sorted-list-and-remove-dups item list) bound))
  :hints (("Goal" :in-theory (enable insert-into-sorted-list-and-remove-dups))))

;; ;not quite right because of dups
;; (defthm maxelem-of-insert-into-sorted-list-and-remove-dups
;;   (equal (maxelem (insert-into-sorted-list-and-remove-dups item list))
;;          (if (member-equal item list)
;;              (maxelem (remove1-equal item list))
;;            (max item (maxelem list))))
;;   :hints (("Goal" :in-theory (enable MAXELEM))))

(defthm decreasingp-of-insert-into-sorted-list-and-remove-dups
  (implies (and (decreasingp list)
                (integerp item)
                (all-integerp list))
           (decreasingp (insert-into-sorted-list-and-remove-dups item list)))
  :hints (("Goal" :in-theory (enable decreasingp insert-into-sorted-list-and-remove-dups))))

;(def-typed-acl2-array translation-arrayp (natp val) :DEFAULT-SATISFIES-PREDP nil)

;; Returns (mv nodenums combined-constant).  Translates the nodenums according
;; to translation-array and xors all the constants.  The nodenums returned are
;; in reverse order, but callers should not care.  Should avoid stack overflows
;; when nodenums may be very long. Unlike rename-args, the first argument
;; cannot contain quoted constants.  Also, this is tail recursive.  Also, this
;; requires the array to be named 'translation-array and allows null entries in
;; the array.  Note that nodes that are merely internal nodes of xor nests
;; are dropped and so not mapped to anything.
(defund translate-nodenums-rev (nodenums translation-array dag-len xor-size nodenum-acc combined-constant)
  (declare (type integer combined-constant)
           (type (integer 0 *) xor-size)
           (xargs :guard (and (natp dag-len)
                              (true-listp nodenums)
                              (all-natp nodenums)
                              (all-< nodenums dag-len)
                              (array1p 'translation-array translation-array)
                              (equal dag-len (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 dag-len) translation-array)
                              (true-listp nodenum-acc))
                  :guard-hints (("Goal" :in-theory (enable))) ;todo: make a fw-chaining rule for the dims
                  ))
  (if (endp nodenums)
      (mv nodenum-acc combined-constant)
    (let* ((nodenum (first nodenums))
           (renamed-nodenum (aref1 'translation-array translation-array nodenum)))
      (if (null renamed-nodenum)
          (prog2$ (er hard? 'translate-nodenums-rev "Node did not translate to anything.")
                  (mv nodenum-acc combined-constant))
        (if (consp renamed-nodenum) ;check for quotep
            (translate-nodenums-rev (rest nodenums)
                                    translation-array
                                    dag-len
                                    xor-size
                                    nodenum-acc
                                    (bvxor xor-size (ifix (unquote renamed-nodenum)) combined-constant))
          (translate-nodenums-rev (rest nodenums)
                                  translation-array
                                  dag-len
                                  xor-size
                                  (cons renamed-nodenum nodenum-acc)
                                  combined-constant))))))

(defthm true-listp-of-mv-nth-0-of-translate-nodenums-rev
  (implies (true-listp nodenum-acc)
           (true-listp (mv-nth 0 (translate-nodenums-rev nodenums translation-array dag-len xor-size nodenum-acc combined-constant))))
  :hints (("Goal" :in-theory (enable translate-nodenums-rev))))

;; need to know that the translation array is bounded - use def-typed-acl2-array?
(defthm all-natp-of-mv-nth-0-of-translate-nodenums-rev
  (implies (and (all-natp nodenum-acc)
                (all-natp nodenums)
                (all-< nodenums dag-len)
                (array1p 'translation-array translation-array)
                (equal dag-len (alen1 'translation-array translation-array))
                (translation-arrayp-aux (+ -1 dag-len) translation-array))
           (all-natp (mv-nth 0 (translate-nodenums-rev nodenums translation-array dag-len xor-size nodenum-acc combined-constant))))
  :hints (("Goal" :in-theory (enable translate-nodenums-rev))))

(defthmd integerp-when-natp
  (implies (natp x)
           (integerp x)))

;; (defthm all-integerp-of-mv-nth-0-of-translate-nodenums-rev
;;   (implies (and (all-natp nodenum-acc)
;;                 (all-natp nodenums)
;;                 (all-< nodenums dag-len)
;;                 (array1p 'translation-array translation-array)
;;                 (equal dag-len (alen1 'translation-array translation-array))
;;                 (if (consp nodenums)
;;                     (renaming-arrayp-aux 'translation-array translation-array (maxelem nodenums))
;;                   t))
;;            (all-integerp (mv-nth 0 (translate-nodenums-rev nodenums translation-array dag-len xor-size nodenum-acc combined-constant))))
;;   :hints (("Goal" :in-theory (enable translate-nodenums-rev))))

;; they actually can't be quoteps?
(defthm all-dargp-less-than-of-mv-nth-0-of-translate-nodenums-rev
  (implies (and (all-natp nodenums)
                (all-< nodenums dag-len)
                (all-dargp-less-than nodenum-acc bound)
                (array1p 'translation-array translation-array)
                (equal dag-len (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 dag-len) translation-array bound))
           (all-dargp-less-than (mv-nth 0 (translate-nodenums-rev nodenums translation-array dag-len xor-size nodenum-acc combined-constant))
                                           bound))
  :hints (("Goal" :in-theory (enable translate-nodenums-rev))))


;items are sorted, so any duplicates must be adjacent
;bozo pass in the items sorted in the other order and skip the reverses here for efficiency
;fixme think this over!
;old: whoa consider (remove-duplicate-pairs-and-reverse '(1 2 3 3) nil)=(2 1)
;old: but (remove-duplicate-pairs-and-reverse '(1 2 3) nil)=(1 2 3)
(defund remove-duplicate-pairs-and-reverse (items acc)
  (declare (xargs :guard (and (integer-listp items)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable integer-listp)))))
  (if (endp items)
      acc ; (reverse acc)
    (if (endp (cdr items))
        (cons (car items) acc) ;had a reverse here! removed Tue Jun 22 19:31:07 2010
      ;;two or more items:
      (if (eql (first items) (second items))
          ;;drop the pair of equal items:
          (remove-duplicate-pairs-and-reverse (cddr items) acc)
        (remove-duplicate-pairs-and-reverse (cdr items) (cons (first items) acc))))))

(defthm true-listp-of-remove-duplicate-pairs-and-reverse
  (implies (true-listp acc)
           (true-listp (remove-duplicate-pairs-and-reverse items acc)))
  :hints (("Goal" :in-theory (enable remove-duplicate-pairs-and-reverse))))

(defthm all-dargp-less-than-of-remove-duplicate-pairs-and-reverse
  (implies (and (all-dargp-less-than items lim)
                (all-dargp-less-than acc lim))
           (all-dargp-less-than (remove-duplicate-pairs-and-reverse items acc) lim))
  :hints (("Goal" :in-theory (enable remove-duplicate-pairs-and-reverse))))

;;
;; bitxor:
;;

(defund all-nodes-are-bitxorsp (nodenums dag-array-name dag-array)
  (declare (xargs :guard (and (array1p dag-array-name dag-array)
                              (true-listp nodenums)
                              ;;combine these three things?
                              (true-listp nodenums)
                              (all-natp nodenums)
                              (all-< nodenums (alen1 dag-array-name dag-array)))))
  (if (endp nodenums)
      t
    (let ((expr (aref1 dag-array-name dag-array (first nodenums))))
      (and (consp expr)
           (eq 'bitxor (ffn-symb expr))
           (all-nodes-are-bitxorsp (rest nodenums) dag-array-name dag-array)))))

;; sweep down the dag, always processing the highest node first
;; maintains a list of nodes to handle (never contains duplicates)
;; start with singleton set containing the root of the nest to fixup
;; repeatedly, take the highest node in the nest:
;; if it's not a bitxor, add it to the output (either to the acc or the accumulated-constant)
;; if it's a bitxor, remove it and add its children (removing duplicates caused by those additions)
;; at any point, the original nest equals the xor of the output so far (accumulated-constant and acc) with the xor of everything in the pending-list

(local (in-theory (disable RATIONAL-LISTP MAXELEM))) ;prevent inductions

(defthm <-of-nth-1-and-nth-0-when-decreasingp
  (implies (and (decreasingp l)
                (consp (cdr l)))
           (< (nth 1 l)
              (nth 0 l)))
  :hints (("Goal" :in-theory (enable decreasingp))))

;slow?
(defthm <-of-0-when-<-free
  (implies (and (< free n)
                (natp free))
           (< 0 n)))

(DEFTHM not-<-of-MAXELEM-and-0
  (IMPLIES (AND (ALL-NATP X) (CONSP X))
           (not (< (MAXELEM X) 0))))

(defthmd not-<-of-one-less-and-nth
  (implies (and (all-< items bound)
                (all-natp items)
                (natp bound)
                (natp n)
                (< n (len items)))
           (not (< (binary-+ '-1 bound) (nth n items))))
  :hints (("Goal" :in-theory (e/d (all-< nth) (nth-of-cdr)))))

(local (in-theory (enable not-<-of-one-less-and-nth)))

(defthm <-of-nth-when-all-<-free
  (implies (and (all-< l bound2)
                (<= bound2 bound)
                (natp n)
                )
           (equal (< (nth n l) bound)
                  (if (< n (len l))
                      t
                    (< nil bound))))
  :hints (("Goal" :in-theory (e/d (all-< nth) (nth-of-cdr)))))

(local (in-theory (disable <-OF-NTH-WHEN-ALL-DARGP-LESS-THAN)))

(local (in-theory (enable CAR-BECOMES-NTH-OF-0)))

(defthm all-<-of-cdr-and-nth-0-when-decreasingp
  (implies (and (decreasingp l)
                (consp l))
           (ALL-< (CDR l) (NTH '0 l)))
  :hints (("Goal" :in-theory (e/d (decreasingp nth all-<) (nth-of-cdr)))))

(defthmd not-<-of-nth-and-0-when-natp-list
  (implies (all-natp l)
           (not (< (nth n l) 0)))
  :hints (("Goal" :in-theory (e/d (all-natp nth) (nth-of-cdr)))))

(local (in-theory (enable not-<-of-nth-and-0-when-natp-list)))

(DEFTHM <-OF-NTH-1-AND-NTH-0-WHEN-DECREASINGP-alt
  (IMPLIES (AND (DECREASINGP L) (< 1 (len l)))
           (< (NTH 1 L) (NTH 0 L)))
  :HINTS (("Goal" :IN-THEORY (ENABLE DECREASINGP))))

;keeps pending-list sorted in a decreasing order
;the whole point of this is to avoid exploring the same subtree twice (so now we explore the dag in decreasing node order and remove duplicates in the pending list)
;pending-list is a list of nodenums
;throughout the run, a node actually gets added to the pending-list only once (because the list never contains duplicates and after a node is removed it can't be added again later because some larger parent would have to be present in the list, but we only process a node when it is the largest node in the list)
; fixme could the acc ever contain duplicates? (if not, don't take time to remove dups)
;returns (mv nodenum-leaves accumulated-constant) where the bitxor of nodenum-leaves and accumulated-constant is equal to nodenum
(defund bitxor-nest-leaves-aux (pending-list dag-array-name dag-array dag-len acc accumulated-constant)
  (declare (xargs :guard (and (true-listp pending-list)
                              (all-natp pending-list)
                              (decreasingp pending-list)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< pending-list dag-len)
                              (integerp accumulated-constant))
                  :measure (if (endp pending-list)
                               0
                             (+ 1 (nfix (maxelem pending-list))))
                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0
                                                     nth-of-cdr
                                                     <-of-nth-when-all-<)))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0 nth-of-cdr consp-of-cdr)))))
  (if (or (endp pending-list)
          (not (mbt (all-natp pending-list)))
          (not (mbt (decreasingp pending-list))) ;for termination
          (not (mbt (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
          (not (mbt (natp dag-len)))
          (not (mbt (all-< pending-list dag-len)))
          )
      (mv acc accumulated-constant)
    (let* ((highest-node (first pending-list))
           (expr (aref1 dag-array-name dag-array highest-node)))
      (if (not (consp expr))
          ;;add the node to the result, since it's not a bitxor:
          (bitxor-nest-leaves-aux (rest pending-list) dag-array-name dag-array dag-len (cons highest-node acc) accumulated-constant)
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn)
              ;; it's a constant, so xor it into the accumulated constant:
              (bitxor-nest-leaves-aux (rest pending-list) dag-array-name dag-array dag-len acc (bitxor (ifix (unquote expr)) accumulated-constant))
            (if (eq 'bitxor fn)
                ;; it is a bitxor, so handle the children:
                (let ((args (dargs expr)))
                  (if (not (= 2 (len args)))
                      (prog2$ (er hard? 'bitxor-nest-leaves-aux "bitxor with wrong number of args.")
                              (mv (append pending-list acc)
                                  accumulated-constant))
                    (let* ((left-child (first args))
                           (right-child (second args)))
                      ;; next check is for termination
                      (if (not (mbt (and (implies (not (consp left-child)) (< left-child highest-node))
                                         (implies (not (consp right-child)) (< right-child highest-node)))))
                          (mv (er hard? 'bitxor-nest-leaves-aux "child nodes not smaller.")
                              0)
                        (let* ((pending-list (rest pending-list)) ;remove the current node
                               (pending-list (if (consp left-child) pending-list (insert-into-sorted-list-and-remove-dups left-child pending-list))) ;can be slow?
                               (pending-list (if (consp right-child) pending-list (insert-into-sorted-list-and-remove-dups right-child pending-list)))
                               (accumulated-constant (if (consp left-child) (bitxor (ifix (unquote left-child)) accumulated-constant) accumulated-constant))
                               (accumulated-constant (if (consp right-child) (bitxor (ifix (unquote right-child)) accumulated-constant) accumulated-constant))
                               )
                          (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))))))
              ;;add the node to the result, since it's not a bitxor:
              (bitxor-nest-leaves-aux (rest pending-list) dag-array-name dag-array dag-len (cons highest-node acc) accumulated-constant))))))))

(defthm decreasingp-of-singleton
  (decreasingp (list item))
  :hints (("Goal" :in-theory (enable decreasingp))))

(defthm all-natp-of-mv-nth-0-of-bitxor-nest-leaves-aux
  (implies (all-natp acc)
           (all-natp (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm true-listp-of-mv-nth-0-of-bitxor-nest-leaves-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm all-<-of-mv-nth-0-of-bitxor-nest-leaves-aux
  (implies (all-< acc dag-len)
           (all-< (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))
                  dag-len))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm all-<-of-mv-nth-0-of-bitxor-nest-leaves-aux-gen
  (implies (and (all-< acc bound)
                (<= dag-len bound))
           (all-< (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))
                  bound))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux)
                                  (pseudo-dag-arrayp)))))

(defthmd not-<-of-nth-0-and-nth-1-when-decreasingp
  (implies (and (decreasingp pending-list)
                (all-natp pending-list)
                (consp pending-list)
                ;; (consp (cdr pending-list))
                )
           (not (< (nth '0 pending-list) (nth '1 pending-list))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable decreasingp))))

(local (in-theory (enable not-<-of-nth-0-and-nth-1-when-decreasingp)))

(defthm all-<=-of-insert-into-sorted-list-and-remove-dups
  (implies (and (<= val2 val)
                (all-<= lst val))
           (all-<= (insert-into-sorted-list-and-remove-dups val2 lst)
                   val))
  :hints (("Goal" :in-theory (enable insert-into-sorted-list-and-remove-dups))))

(defthm all-<=of-cdr-and-nth-0-when-decreasingp
  (implies (decreasingp pending-list)
           (all-<= (cdr pending-list) (nth '0 pending-list)))
  :hints (("Goal" :in-theory (enable decreasingp all-<=))))

(defthm all-<=-when-<=-and-decreasingp
  (implies (and (<= (car x) bound)
                (decreasingp x))
           (all-<= x bound))
  :hints (("Goal" :in-theory (enable all-<= decreasingp))))

(defthm all-<=-of-mv-nth-0-of-bitxor-nest-leaves-aux-new
  (implies (and (all-natp pending-list)
                (decreasingp pending-list)
                (all-< pending-list dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;                (integerp accumulated-constant)
                (all-<= acc bound)
                (natp bound)
                (if (consp pending-list)
                    (<= (car pending-list) bound)
                  t))
           (all-<= (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))
                   bound))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux all-myquotep)
                                  (pseudo-dag-arrayp quotep)))))

(defthm all-<=-of-+-of--1
  (implies (and (all-integerp acc)
                (integerp bound))
           (equal (all-<= acc (+ -1 bound))
                  (all-< acc bound)))
  :hints (("Goal" :in-theory (e/d (all-< all-<=) (CAR-BECOMES-NTH-OF-0)))))

(defthm integerp-of-nth-when-all-natp
  (implies (and (all-natp x)
                (natp n)
                (< n (len x)))
           (integerp (nth n x)))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (enable all-integerp-when-all-natp)))

(defthm all-<-of-mv-nth-0-of-bitxor-nest-leaves-aux-new
  (implies (and (all-natp pending-list)
                (all-natp acc)
                (decreasingp pending-list)
                (all-< pending-list dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;                (integerp accumulated-constant)
                (all-< acc bound)
                (natp bound)
                (if (consp pending-list)
                    (< (car pending-list) bound)
                  t))
           (all-< (mv-nth 0 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))
                  bound))
  :hints (("Goal" :use (:instance all-<=-of-mv-nth-0-of-bitxor-nest-leaves-aux-new (bound (+ -1 bound)))
           :in-theory (e/d (BITXOR-NEST-LEAVES-AUX ALL-INTEGERP-WHEN-ALL-NATP)
                           (all-<=-of-mv-nth-0-of-bitxor-nest-leaves-aux-new)))))

(defthm integerp-of-mv-nth-1-of-bitxor-nest-leaves-aux
  (implies (integerp accumulated-constant)
           (integerp (mv-nth 1 (bitxor-nest-leaves-aux pending-list dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bitxor-nest-leaves-aux) (quotep PSEUDO-DAG-ARRAYP)))))

(defthmd integer-listp-rewrite
  (equal (integer-listp x)
         (and (all-integerp x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable integer-listp all-integerp))))

;nodenum is the root of a bitxor nest
;this returns a list of nodenums and constants (possibly one constant, followed by nodenums) term equivalent to nodenum but with the leaves fixed up according to translation-array
;fixme can this blowup?! maybe not
(defund bitxor-nest-leaves (nodenum dag-array-name dag-array dag-len translation-array)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              (array1p 'translation-array translation-array)
                              (equal dag-len (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 dag-len) translation-array))
                  :guard-hints (("Goal" :in-theory (enable integer-listp-rewrite ALL-RATIONALP-WHEN-ALL-NATP ALL-INTEGERP-WHEN-ALL-NATP)))))
  (b* (((mv nodenum-leaves combined-constant)
        (bitxor-nest-leaves-aux (list nodenum) dag-array-name dag-array dag-len nil 0) ;;TODO: consider this: (bitxor-nest-leaves-for-node nodenum dag-array-name dag-array)
        )
       ((mv nodenum-leaves combined-constant)
        (translate-nodenums-rev nodenum-leaves translation-array dag-len 1 nil combined-constant)) ;i suppose the fixing up could introduce duplicates (two leaves that map to the same nodenum after the xors they themselves are supported by get normalized?)
       (sorted-nodenum-leaves (merge-sort-< nodenum-leaves))
       ;;xoring something with itself amounts to xoring with 0
       (rev-sorted-nodenum-leaves (remove-duplicate-pairs-and-reverse sorted-nodenum-leaves nil)) ;this could make the xor nest directly?
       (all-leaves (if (eql 0 combined-constant)
                       rev-sorted-nodenum-leaves
                     (cons (enquote combined-constant) ;will always be 1 if it's not 0? ;save this cons?
                           rev-sorted-nodenum-leaves))))
    all-leaves))
;;                  (rev-sorted-nodenum-leaves-with-constant
;;                   (if (eql 0 combined-constant)
;;                       rev-sorted-nodenum-leaves
;;                     ;;bozo inefficient?  careful in the case where there's only one leaf.  previously we made (bitxor <constant> (getbit 0 <leaf>))
;;                     (append rev-sorted-nodenum-leaves (list (enquote combined-constant))))))
;;             (make-reversed-bitxor-nest rev-sorted-nodenum-leaves-with-constant))))

(defthm true-listp-of-bitxor-nest-leaves
  (true-listp (bitxor-nest-leaves nodenum dag-array-name dag-array dag-len translation-array))
  :hints (("Goal" :in-theory (enable bitxor-nest-leaves))))

(defthm all-dargp-less-than-of-bitxor-nest-leaves
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (array1p 'translation-array translation-array)
                (equal dag-len (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 dag-len) translation-array bound))
           (all-dargp-less-than (bitxor-nest-leaves nodenum dag-array-name dag-array dag-len translation-array) bound))
  :hints (("Goal" :in-theory (enable bitxor-nest-leaves))))

;; POSSIBLE BETTER ALGORITHM (linear in the size of the DAG but might perform worse for small nests):

;; (defund flip-tag (tag-array-name tag-array nodenum)
;;   (declare (xargs :guard (and (array1p tag-array-name tag-array)
;;                               (natp nodenum)
;;                               (< nodenum (alen1 tag-array-name tag-array)))))
;;   (aset1 tag-array-name tag-array nodenum (not (aref1 tag-array-name tag-array nodenum))))

;; ;; Returns (mv leaf-nodenums accumulated-constant)
;; ;; TODO: This algorithm may be worse for small nests (linear in the size of the DAG).  But that's the upper bound too, which is good for large nests
;; (defund bitxor-nest-leaves-for-node-aux (nodenum dag-array-name dag-array tag-array-name tag-array acc accumulated-constant)
;;   (declare (xargs :measure (nfix (+ 1 nodenum))
;;                   :guard (or (eql -1 nodenum)
;;                              (and (natp nodenum)
;;                                   (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
;;                                   (array1p tag-array-name tag-array)
;;                                   (< nodenum (alen1 tag-array-name tag-array))
;;                                   (integerp accumulated-constant)))
;;                   :guard-hints (("Goal" :in-theory (enable NTH-OF-CDR flip-tag
;;                                                            pseudo-dag-arrayp
;;                                                            )))))
;;   (if (not (natp nodenum))
;;       (mv acc accumulated-constant)
;;     (if (not (aref1 tag-array-name tag-array nodenum))
;;         ;; not tagged, so skip
;;         (bitxor-nest-leaves-for-node-aux (+ -1 nodenum) dag-array-name dag-array tag-array-name tag-array acc accumulated-constant)
;;       ;; the node is tagged:
;;       (let* ((expr (aref1 dag-array-name dag-array nodenum)))
;;         (if (quotep expr) ;might as well xor in the constant here, even though naked constants may be rare:
;;             (bitxor-nest-leaves-for-node-aux (+ -1 nodenum) dag-array-name dag-array tag-array-name tag-array acc
;;                                              (bitxor (ifix (unquote expr)) accumulated-constant))
;;           (if (and (call-of 'bitxor expr)
;;                    (eql 2 (len (dargs expr)))) ;for guards
;;               (b* ((left-child (darg1 expr))
;;                    (right-child (darg2 expr))
;;                    ;; xor in constant children, flip the tags for nodenum children (appearing twice cancels out)
;;                    ((mv tag-array accumulated-constant)
;;                     (if (consp left-child) ;test for quotep
;;                         (mv tag-array (bitxor (ifix (unquote left-child)) accumulated-constant))
;;                       (mv (flip-tag tag-array-name tag-array left-child) accumulated-constant)))
;;                    ((mv tag-array accumulated-constant)
;;                     (if (consp right-child) ;test for quotep
;;                         (mv tag-array (bitxor (ifix (unquote right-child)) accumulated-constant))
;;                       (mv (flip-tag tag-array-name tag-array right-child) accumulated-constant))))
;;                 (bitxor-nest-leaves-for-node-aux (+ -1 nodenum) dag-array-name dag-array tag-array-name tag-array acc accumulated-constant))
;;             ;; this is a leaf, so add to the accumulator:
;;             (bitxor-nest-leaves-for-node-aux (+ -1 nodenum) dag-array-name dag-array tag-array-name tag-array
;;                                              (cons nodenum acc)
;;                                              accumulated-constant)))))))

;; ;; Returns (mv leaf-nodenums accumulated-constant)
;; (defund bitxor-nest-leaves-for-node (nodenum dag-array-name dag-array)
;;   (declare (xargs :guard (and (natp nodenum)
;;                               (<= nodenum 2147483645)
;;                               (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))))
;;   (let* ((tag-array-name 'bitxor-nest-leaves-for-node-tag-array)
;;          (tag-array (make-empty-array tag-array-name (+ 1 nodenum))) ;all tags are initially nil
;;          (tag-array (aset1 tag-array-name tag-array nodenum t)) ;tag the start node
;;          )
;;     (bitxor-nest-leaves-for-node-aux nodenum
;;                                      dag-array-name dag-array
;;                                      tag-array-name tag-array
;;                                      nil ;acc
;;                                      0   ;accumulated-constant
;;                                      )))

(local (in-theory (disable strip-cdrs)))

;(local (in-theory (enable bounded-dag-parent-arrayp))) ;todo: have the dag builders use better guards


(local (in-theory (enable ;not-cddr-when-all-dargp-less-than ;maybe enable for all axe stuff?
                          ;<-OF-NTH-WHEN-ALL-DARGP-LESS-THAN ;make a cheap version with a free var
                          )))

;; ;returns (mv new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist translation-array)
;; ;check this over..
;; ;! keep this in sync with bvxor version
;; (defun simplify-bitxors-aux (n ;counts up
;;                              dag-array dag-len dag-parent-array dag-array-name dag-parent-array-name
;;                              new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
;;                              translation-array ;maps nodenums in dag-array to equivalent nodes in new-dag-array
;;                              print)
;;   (declare (xargs :measure (+ 1 (nfix (- dag-len n)))))
;;   (if (or (not (natp n))
;;           (not (natp dag-len))
;;           (prog2$ (and print (eql 0 (mod n 1000)) (cw "XORs node ~x0...~%" n))
;;                   (>= n dag-len)))
;;       (mv new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist translation-array)
;;     (let* ((expr (aref1 dag-array-name dag-array n)))
;;       (if (variablep expr)
;;           ;; If it's a variable, just add it to the DAG and update the translation-array:
;;           (mv-let (nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
;;                   (add-variable-to-dag-array-with-name expr new-dag-array new-dag-len
;;                                                               new-dag-parent-array ;;just passed through
;;                                                               new-dag-constant-alist ;;just passed through
;;                                                               new-dag-variable-alist
;;                                                               new-dag-array-name new-dag-parent-array-name)
;;                   (simplify-bitxors-aux (+ 1 n)
;;                                         dag-array dag-len dag-parent-array
;;                                         dag-array-name dag-parent-array-name
;;                                         new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
;;                                         (aset1 'translation-array translation-array n nodenum-or-quotep)
;;                                         print))
;;         (let ((fn (ffn-symb expr)))
;;           (if (eq 'quote fn)
;;               ;; If it's a quoted constant just update the translation-array:
;;               (simplify-bitxors-aux (+ 1 n)
;;                                     dag-array dag-len dag-parent-array
;;                                     dag-array-name dag-parent-array-name
;;                                     new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
;;                                     (aset1 'translation-array translation-array n expr)
;;                                     print)
;;             ;;function call:
;;             (let* ((args (dargs expr)))
;;               (if (eq 'bitxor fn)
;;                   ..
;;                 ;; it's a function call other than a bitxor...
;;                 (let ((fixed-up-args (fixup-args-allows-quotes-array-version-tail args translation-array nil))) ;is fixup-args-allows-quotes-array-version-tail overkill here?
;;                   (mv-let (nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
;;                           (add-function-call-expr-to-dag-array-with-name fn fixed-up-args new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist
;;                                                                                 new-dag-array-name new-dag-parent-array-name)
;;                           (simplify-bitxors-aux (+ 1 n)
;;                                                 dag-array dag-len dag-parent-array
;;                                                 dag-array-name dag-parent-array-name
;;                                                 new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
;;                                                 (aset1 'translation-array translation-array n nodenum-or-quotep)
;;                                                 print)))))))))))

;; (skip- proofs (verify-guards simplify-bitxors-aux))

;; ;ffixme don't go back and forth from lists to arrays!
;; ;dag-lst should not be a quotep or empty
;; ;returns either a new dag-lst whose top node is equal to the top node of DAG-LST, or a quotep equal to the top node of DAG-LST
;; (defun simplify-bitxors (dag-lst print)
;;   (let* ( ;;convert dag-lst to an array:
;;          (dag-len (len dag-lst))
;;          (top-nodenum (top-nodenum dag-lst))
;;          (dag-array-name 'simplify-bitxors-array)
;;          (dag-array (make-into-array dag-array-name dag-lst)) ;could pass in the len? ;add slack space?
;;          (dag-parent-array-name 'simplify-bitxors-parent-array))
;;     (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
;;             (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len)
;;             (declare (ignore dag-constant-alist dag-variable-alist)) ;ffixme dont waste time computing these!
;;             (let* ((new-dag-size (* 2 dag-len)) ;none of the nodes are valid
;;                    (new-dag-array-name 'simplify-bitxors-new-array)
;;                    (new-dag-array (make-empty-array new-dag-array-name new-dag-size)) ;will get expanded if it needs to be bigger
;;                    (new-dag-parent-array-name 'simplify-bitxors-new-parent-array)
;;                    (new-dag-parent-array (make-empty-array new-dag-parent-array-name new-dag-size))
;;                    (new-dag-constant-alist (empty-alist))
;;                    (new-dag-variable-alist (empty-alist))
;;                    ;;indicates what each node in the original dag rewrote to:
;;                    (translation-array (make-empty-array 'translation-array dag-len)))
;;               (prog2$ (and ;print
;;                        (cw "(Simplifying bitxors (len is ~x0)...~%" dag-len))
;;                       (mv-let (new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist translation-array)
;;                               (simplify-bitxors-aux 0 dag-array dag-len dag-parent-array
;;                                                     dag-array-name dag-parent-array-name
;;                                                     new-dag-array 0 ;;new-dag-len
;;                                                     new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
;;                                                     translation-array print)
;;                               (declare (ignore new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
;;                               (let ((result (aref1 'translation-array translation-array top-nodenum)))
;;                                 (if (quotep result)
;;                                     (prog2$ (and ;print
;;                                              (cw ")~%"))
;;                                             result)
;;                                   (let ((dag-lst
;;                                          (drop-non-supporters-array new-dag-array-name new-dag-array result print)
;;                                          ))
;;                                     (progn$ (and (eq :verbose print) (print-list dag-lst))
;;                                             (and print (cw ")~%"))
;;                                             dag-lst))))))))))

;; (skip- proofs (verify-guards simplify-bitxors))

;;
;; bvxor:
;;

;keep in sync with bitxor version
(defund all-nodes-are-bvxorsp (nodenums quoted-size dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (true-listp nodenums)
                              ;;combine these three things?
                              (true-listp nodenums)
                              (all-natp nodenums)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      t
    (let ((expr (aref1 dag-array-name dag-array (first nodenums))))
      (and (consp expr)
           (eq 'bvxor (ffn-symb expr))
           (consp (dargs expr))
           (equal quoted-size (darg1 expr))
           (all-nodes-are-bvxorsp (rest nodenums) quoted-size dag-array-name dag-array dag-len)))))

;we always want to go to nth of dargs
(defthm nth-of-0-and-cddr-of-dargs
  (equal (nth 0 (cddr (dargs expr)))
         (nth 2 (dargs expr)))
  :hints (("Goal" :in-theory (enable nth-of-cdr))))

(defthm nth-of-0-and-cdr-of-dargs
  (equal (nth 0 (cdr (dargs expr)))
         (nth 1 (dargs expr)))
  :hints (("Goal" :in-theory (enable nth-of-cdr))))

(defthm not-equal-of-nth-0-and-nth-1-when-decreasingp
  (implies (and (decreasingp x)
                (all-integerp x)
                (consp x))
           (not (EQUAL (NTH 1 x)
                       (NTH 0 x))))
  :hints (("Goal" :in-theory (enable DECREASINGP ALL-INTEGERP))))

;; sweep down the dag, always processing the highest node first
;; list of nodes to handle (never contains duplicates)
;; start with singleton set containing the root of the nest to fixup
;; repeatedly, take the highest node in the nest:
;; if it's not a bvxor of the right size, add it to the output (either to the acc or the accumulated-constant)
;; if it's a bvxor of the right size, remove it and add its children (removing duplicates caused by those additions)
;; at any point, the original nest equals the xor of the output so far (accumulated-constant and acc) with the xor of everything in the pending-list

;keeps pending-list sorted in a decreasing order
;the whole point of this is to avoid exploring the same subtree twice (so now we explore subtrees in decreasing node order and remove duplicates in the pending list)
;pending-list is a list of nodenums
;throughout the run, a node actually gets added to the pending-list only once (because the list never contains duplicates and after a node is removed it can't be added again later because some larger parent would have to be present in the list, but we only process a node when it is the largest node in the list - whew!)
; fixme could the acc ever contain duplicates? (if not, don't take time to remove dups)
;returns (mv nodenum-leaves accumulated-constant) where the bvxor of nodenum-leaves and accumulated-constant is equal to nodenum
;keep in sync with bitxor version
;the acc returned will be sorted in increasing order
(defund bvxor-nest-leaves-aux (pending-list
                               size ;the unquoted size
                               dag-array-name dag-array dag-len acc accumulated-constant)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (true-listp pending-list)
                              (all-natp pending-list)
                              (decreasingp pending-list)
                              (all-< pending-list dag-len)
                              (integerp accumulated-constant)
                              (natp size))
                  :measure (if (endp pending-list)
                               0
                             (+ 1 (nfix (maxelem pending-list))))
                  :hints (("Goal" :in-theory (enable car-becomes-nth-of-0
                                                     nth-of-cdr
                                                     <-of-nth-when-all-<)))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0 nth-of-cdr)))))
  (if (or (endp pending-list)
          (not (mbt (all-natp pending-list)))
          (not (mbt (decreasingp pending-list))) ;for termination
          (not (mbt (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
          (not (mbt (natp dag-len)))
          (not (mbt (all-< pending-list dag-len))))
      (mv acc accumulated-constant)
    (let* ((highest-node (first pending-list))
           (expr (aref1 dag-array-name dag-array highest-node)))
      (if (or (not (consp expr))
              (not (eq 'bvxor (ffn-symb expr)))
              (not (= 3 (len (dargs expr))))
              (not (quotep (darg1 expr)))
              (not (eql size (unquote (darg1 expr)))))
          ;;add the node to the result, since it's not a bvxor of the right size:
          (if (quotep expr) ;slow?
              (bvxor-nest-leaves-aux (rest pending-list) size dag-array-name dag-array dag-len acc (bvxor size (ifix (unquote expr)) accumulated-constant))
            (bvxor-nest-leaves-aux (rest pending-list) size dag-array-name dag-array dag-len (cons highest-node acc) accumulated-constant))
        ;; it is a bvxor of the right size, so handle the children:
        (let* ((dargs (dargs expr))
               (left-child (second dargs))
               (right-child (third dargs)))
          ;; next check is for termination
          (if (not (mbt (and (implies (not (consp left-child)) (< left-child highest-node))
                             (implies (not (consp right-child)) (< right-child highest-node)))))
              (mv (er hard? 'bvxor-nest-leaves-aux "child nodes not smaller.")
                  0)
            (let* ((pending-list (rest pending-list)) ;remove the current node
                   (pending-list (if (consp left-child) pending-list (insert-into-sorted-list-and-remove-dups left-child pending-list))) ;can be slow?
                   (pending-list (if (consp right-child) pending-list (insert-into-sorted-list-and-remove-dups right-child pending-list)))
                   (accumulated-constant (if (consp left-child) (bvxor size (ifix (unquote left-child)) accumulated-constant) accumulated-constant))
                   (accumulated-constant (if (consp right-child) (bvxor size (ifix (unquote right-child)) accumulated-constant) accumulated-constant)))
              (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))))))))

(defthm all-natp-of-mv-nth-0-of-bvxor-nest-leaves-aux
  (implies (all-natp acc)
           (all-natp (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm true-listp-of-mv-nth-0-of-bvxor-nest-leaves-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm all-<-of-mv-nth-0-of-bvxor-nest-leaves-aux
  (implies (all-< acc dag-len)
           (all-< (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant)) dag-len))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux) (pseudo-dag-arrayp)))))

(defthm all-<-of-mv-nth-0-of-bvxor-nest-leaves-aux-gen
  (implies (and (all-< acc bound)
                (<= dag-len bound))
           (all-< (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant)) bound))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux)
                                  (pseudo-dag-arrayp)))))

(defthm integer-of-mv-nth-1-of-bvxor-nest-leaves-aux
  (implies (integerp accumulated-constant)
           (integerp (mv-nth 1 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux) (pseudo-dag-arrayp
                                                           DAG-EXPRP0)))))

(defthm all-<=-of-mv-nth-0-of-bvxor-nest-leaves-aux-new
  (implies (and (all-natp pending-list)
                (decreasingp pending-list)
                (all-< pending-list dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;                (integerp accumulated-constant)
                (all-<= acc bound)
                (natp bound)
                (if (consp pending-list)
                    (<= (car pending-list) bound)
                  t))
           (all-<= (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))
                   bound))
  :hints (("Goal" :in-theory (e/d (bvxor-nest-leaves-aux)
                                  (pseudo-dag-arrayp quotep)))))

(defthm all-<-of-mv-nth-0-of-bvxor-nest-leaves-aux-new
  (implies (and (all-natp pending-list)
                (all-natp acc)
                (decreasingp pending-list)
                (all-< pending-list dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;                (integerp accumulated-constant)
                (all-< acc bound)
                (natp bound)
                (if (consp pending-list)
                    (< (car pending-list) bound)
                  t))
           (all-< (mv-nth 0 (bvxor-nest-leaves-aux pending-list size dag-array-name dag-array dag-len acc accumulated-constant))
                  bound))
  :hints (("Goal" :use (:instance all-<=-of-mv-nth-0-of-bvxor-nest-leaves-aux-new (bound (+ -1 bound)))
           :in-theory (e/d (BvXOR-NEST-LEAVES-AUX ALL-INTEGERP-WHEN-ALL-NATP)
                           (all-<=-of-mv-nth-0-of-bvxor-nest-leaves-aux-new)))))

;keep in sync with bitxor version
;nodenum is the root of a bvxor nest whose size parameter is SIZE (quoted or not?)
;this returns a list of nodenums and constants (possibly one constant, followed by nodenums) whose bvxor is equivalent to nodenum but with the leaves fixed up according to translation-array
;fixme can this blowup?! maybe not
(defund bvxor-nest-leaves (nodenum size dag-array-name dag-array dag-len translation-array)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              (array1p 'translation-array translation-array)
                              (equal dag-len (alen1 'translation-array translation-array))
                              (translation-arrayp-aux (+ -1 dag-len) translation-array)
                              (natp size))
                  :guard-hints (("Goal" :in-theory (enable integer-listp-rewrite ALL-RATIONALP-WHEN-ALL-NATP ALL-INTEGERP-WHEN-ALL-NATP)))))
  (mv-let (nodenum-leaves combined-constant)
    (bvxor-nest-leaves-aux (list nodenum) size dag-array-name dag-array dag-len nil 0)
    (b* (((mv nodenum-leaves combined-constant)
          (translate-nodenums-rev nodenum-leaves translation-array dag-len size nil combined-constant)) ;i suppose the fixing up could introduce duplicates (two leaves that map to the same nodenum after the xors they themselves are supported by get normalized?)
         (sorted-nodenum-leaves (merge-sort-< nodenum-leaves))
         ;;xoring something with itself amounts to xoring with 0
         (rev-sorted-nodenum-leaves (remove-duplicate-pairs-and-reverse sorted-nodenum-leaves nil)) ;this could make the xor nest directly? ;fixme do we still need to remove dups here?
         (all-leaves (if (eql 0 combined-constant)
                         rev-sorted-nodenum-leaves
                       (cons (enquote combined-constant) ;save this cons? ;fixme when the result is reversed, does that mean the constant goes last?
                             rev-sorted-nodenum-leaves)))
;(dummy (cw "~x0 leaves.~%" (len all-leaves)))
         )
;            (declare (ignore dummy))
      all-leaves)))

(defthm true-listp-of-bvxor-nest-leaves
  (true-listp (bvxor-nest-leaves nodenum size dag-array-name dag-array dag-len translation-array))
  :hints (("Goal" :in-theory (enable bvxor-nest-leaves))))

(defthm all-dargp-less-than-of-bvxor-nest-leaves
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< nodenum dag-len)
                (array1p 'translation-array translation-array)
                (equal (alen1 'translation-array translation-array) dag-len)
                (bounded-translation-arrayp-aux (+ -1 dag-len) translation-array bound))
           (all-dargp-less-than (bvxor-nest-leaves nodenum size dag-array-name dag-array dag-len translation-array) bound))
  :hints (("Goal" :in-theory (enable bvxor-nest-leaves))))

(local (in-theory (disable myquotep)))

;returns (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
;check this over..
(defund simplify-xors-aux (n ;counts up
                           ;;the DAG we are copying (and normalizing xor nests as we go):
                           old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                           ;;the new DAG (initially empty):
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                           translation-array ;maps nodenums in old-dag-array to equivalent nodes (or quoteps?) in dag-array
                           print)
  (declare (type (integer 0 2147483646) old-dag-len)
           (xargs :measure (+ 1 (nfix (- old-dag-len n)))
                  :guard (and (natp n)
                              (natp old-dag-len)
                              (<= n old-dag-len)
                              ;;stuff about the old dag (can't use wf-dagp since dag-constant-alist and dag-variable-alist are missing):
                              (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
                              (bounded-dag-parent-arrayp old-dag-parent-array-name old-dag-parent-array old-dag-len)
                              (equal (alen1 old-dag-array-name old-dag-array)
                                     (alen1 old-dag-parent-array-name old-dag-parent-array))
                              ;; stuff about the new dag:
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              ;; stuff about the renaming array:
                              (array1p 'translation-array translation-array)
                              (equal old-dag-len (alen1 'translation-array translation-array))
                              (bounded-translation-arrayp-aux (+ -1 old-dag-len) translation-array dag-len)
                              )
                  :split-types t
                  :guard-hints (("Goal" :in-theory (e/d ()
                                                        (dargp dargp-less-than natp))))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp old-dag-len)))
          (prog2$ (and print (eql 0 (mod n 1000)) (cw "XORs node ~x0...~%" n))
                  (>= n old-dag-len)))
      (mv (erp-nil) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
    (let* ((expr (aref1 old-dag-array-name old-dag-array n)))
      (if (variablep expr)
          ;; If it's a variable, just add it to the new DAG and update the translation-array:
          (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (add-variable-to-dag-array-with-name expr dag-array dag-len
                                                       dag-parent-array ;;just passed through
                                                       dag-constant-alist ;;just passed through
                                                       dag-variable-alist
                                                       dag-array-name dag-parent-array-name)
            (if erp
                (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
              (simplify-xors-aux (+ 1 n)
                                 old-dag-array old-dag-len old-dag-parent-array
                                 old-dag-array-name old-dag-parent-array-name
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 (aset1 'translation-array translation-array n nodenum-or-quotep)
                                 print)))
        (let ((fn (ffn-symb expr)))
          (if (eq 'quote fn)
              ;; If it's a quoted constant just update the translation-array:
              (simplify-xors-aux (+ 1 n)
                                 old-dag-array old-dag-len old-dag-parent-array
                                 old-dag-array-name old-dag-parent-array-name
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 (aset1 'translation-array translation-array n expr)
                                 print)
            ;;function call:
            (let* ((args (dargs expr)))
              (if (and (eq 'bvxor fn)
                       (consp (dargs expr)) ;; (= 3 (len (dargs expr)))
                       (consp (darg1 expr)) ;; tests for quotep
                       (natp (unquote (darg1 expr))))
                  ;; it's a bvxor with a constant size:
                  (if (and (not (eql n (+ -1 old-dag-len))) ;special case for the top node (avoid checking this each time?)
                           (all-nodes-are-bvxorsp (aref1 old-dag-parent-array-name old-dag-parent-array n)
                                                  (darg1 expr)
                                                  old-dag-array-name old-dag-array old-dag-len))
                      ;; if all the node's parents are bvxors of the right size (and this isn't the top node), we drop the node for now (we'll handle it when we handle its parents)
                      (simplify-xors-aux (+ 1 n)
                                         old-dag-array old-dag-len old-dag-parent-array
                                         old-dag-array-name old-dag-parent-array-name
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         translation-array print)
                    ;; this is the top node of an xor nest (some parent is not an xor or we are handling the top node), so we have to handle the nest rooted at this node...
                    (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                      (add-bvxor-nest-to-dag-array
                       ;;may have 0 or just 1 leaf:
                       ;;avoid the reverse by doing the merge-sort in bvxor-nest-leaves by the opposite order..
                       (reverse-list (bvxor-nest-leaves n ;avoid making this list? ;fixme can this be exponentially large?! maybe not..
                                                        (unquote (darg1 expr))
                                                        old-dag-array-name
                                                        old-dag-array
                                                        old-dag-len
                                                        translation-array))
                       (unquote (darg1 expr))           ;size
                       (darg1 expr)                     ;quoted size
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
                      (if erp
                          (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
                        (simplify-xors-aux (+ 1 n)
                                           old-dag-array old-dag-len old-dag-parent-array
                                           old-dag-array-name old-dag-parent-array-name
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           (aset1 'translation-array translation-array n nodenum-or-quotep)
                                           print))))
                (if (and (eq 'bitxor fn)
                         (= 2 (len (dargs expr))))
                    ;; it's a bitxor:
                    (if (and (not (eql n (+ -1 old-dag-len))) ;special case for the top node (avoid checking this each time?)
                             (all-nodes-are-bitxorsp (aref1 old-dag-parent-array-name old-dag-parent-array n) old-dag-array-name old-dag-array))
                        ;; if all the node's parents are bitxors (and this isn't the top node), we drop the node for now (we'll handle it when we handle its parents)
                        (simplify-xors-aux (+ 1 n)
                                           old-dag-array old-dag-len old-dag-parent-array
                                           old-dag-array-name old-dag-parent-array-name
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           translation-array print)
                      ;; this is the top node of a bitxor nest (some parent is not a bitxor or we are handling the top node), so we have to handle the nest rooted at this node...
                      (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                        (add-bitxor-nest-to-dag-array
                         ;;may have 0 or just 1 leaf:
;avoid the reverse by doing the merge-sort in bitxor-nest-leaves by the opposite order..
;fixme does this put the constant last?
                         (reverse-list (bitxor-nest-leaves n ;avoid making this list? ;fixme can this be exponentially large?! maybe not..
                                                           old-dag-array-name
                                                           old-dag-array
                                                           old-dag-len
                                                           translation-array))
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
                        (if erp
                            (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
                          (simplify-xors-aux (+ 1 n)
                                             old-dag-array old-dag-len old-dag-parent-array
                                             old-dag-array-name old-dag-parent-array-name
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             (aset1 'translation-array translation-array n nodenum-or-quotep)
                                             print))))
                  ;; it's a function call other than a bitxor or a bvxor on a constant size ...
                  (let ((fixed-up-args (translate-args args translation-array)))
                    (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                      (add-function-call-expr-to-dag-array-with-name fn fixed-up-args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                           dag-array-name dag-parent-array-name)
                      (if erp
                          (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
                        (simplify-xors-aux (+ 1 n)
                                           old-dag-array old-dag-len old-dag-parent-array
                                           old-dag-array-name old-dag-parent-array-name
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           (aset1 'translation-array translation-array n nodenum-or-quotep)
                                           print)))))))))))))

(def-dag-builder-theorems
  (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print)
  (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist translation-array)
  :dag-array-name dag-array-name
  :dag-parent-array-name dag-parent-array-name
  :expand (:free (old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print) ;;everything but n
                 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print))
  :dont-enable t ;led to loops?
  :hyps ((natp n)
          (natp old-dag-len)
          (<= n old-dag-len)
          ;;stuff about the old dag:
          (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
          (bounded-dag-parent-arrayp old-dag-parent-array-name old-dag-parent-array old-dag-len)
          (equal (alen1 old-dag-array-name old-dag-array)
                 (alen1 old-dag-parent-array-name old-dag-parent-array))
          ;; stuff about the renaming array:
          (array1p 'translation-array translation-array)
          (equal old-dag-len (alen1 'translation-array translation-array))
          (bounded-translation-arrayp-aux (+ -1 old-dag-len) translation-array dag-len)
          ))

(defthm type-of-simplify-xors-aux-other-params
  (implies (and (natp n)
                (natp old-dag-len)
                (<= n old-dag-len)
                ;;stuff about the old dag:
                (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
                (bounded-dag-parent-arrayp old-dag-parent-array-name old-dag-parent-array old-dag-len)
                (equal (alen1 old-dag-array-name old-dag-array)
                       (alen1 old-dag-parent-array-name old-dag-parent-array))
                ;; stuff about the new dag:
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; stuff about the renaming array:
                (array1p 'translation-array translation-array)
                (equal old-dag-len (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 old-dag-len) translation-array dag-len)
                )
           (and (equal (alen1 'translation-array
                              (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print)))
                       old-dag-len)
                (array1p 'translation-array
                         (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print)))
                (bounded-translation-arrayp-aux (+ -1 old-dag-len)
                                                (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                             translation-array print))
                                                (mv-nth 2 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                             translation-array print)))
                (translation-arrayp-aux (+ -1 old-dag-len)
                                        (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                     translation-array print)))))
  :hints (("Goal" :induct (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print)
           :expand (simplify-xors-aux n old-dag-array
                                      (alen1 'translation-array
                                             translation-array)
                                      old-dag-parent-array old-dag-array-name
                                      old-dag-parent-array-name
                                      dag-array dag-len dag-parent-array
                                      dag-constant-alist dag-variable-alist
                                      dag-array-name dag-parent-array-name
                                      translation-array print)
           :in-theory (enable simplify-xors-aux))))

(defthm type-of-simplify-xors-aux-other-params-gen-1
  (implies (and (natp n)
                (natp old-dag-len)
                (<= n old-dag-len)
                ;;stuff about the old dag:
                (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
                (bounded-dag-parent-arrayp old-dag-parent-array-name old-dag-parent-array old-dag-len)
                (equal (alen1 old-dag-array-name old-dag-array)
                       (alen1 old-dag-parent-array-name old-dag-parent-array))
                ;; stuff about the new dag:
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; stuff about the renaming array:
                (array1p 'translation-array translation-array)
                (equal old-dag-len (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 old-dag-len) translation-array dag-len)
                (<= (mv-nth 2 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print))
                    bound)
                (natp bound)
                )
           (bounded-translation-arrayp-aux (+ -1 old-dag-len)
                                           (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name translation-array print))
                                           bound))
  :hints (("Goal" :use (:instance type-of-simplify-xors-aux-other-params)
           :in-theory (disable type-of-simplify-xors-aux-other-params natp))))

(defthm TRANSLATION-ARRAYP-AUX-when-negative
  (implies (< TOP-NODENUM-TO-CHECK 0)
           (TRANSLATION-ARRAYP-AUX TOP-NODENUM-TO-CHECK ARRAY))
  :hints (("Goal" :in-theory (enable TRANSLATION-ARRAYP-AUX))))

(defthm type-of-simplify-xors-aux-other-params-gen-2
  (implies (and (natp n)
                (natp old-dag-len)
                (<= n old-dag-len)
                ;;stuff about the old dag:
                (pseudo-dag-arrayp old-dag-array-name old-dag-array old-dag-len)
                (bounded-dag-parent-arrayp old-dag-parent-array-name old-dag-parent-array old-dag-len)
                (equal (alen1 old-dag-array-name old-dag-array)
                       (alen1 old-dag-parent-array-name old-dag-parent-array))
                ;; stuff about the new dag:
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                ;; stuff about the renaming array:
                (array1p 'translation-array translation-array)
                (equal old-dag-len (alen1 'translation-array translation-array))
                (bounded-translation-arrayp-aux (+ -1 old-dag-len) translation-array dag-len)
                (integerp v)
                (<= v (+ -1 old-dag-len)))
           (translation-arrayp-aux v
                                   (mv-nth 6 (simplify-xors-aux n old-dag-array old-dag-len old-dag-parent-array old-dag-array-name old-dag-parent-array-name
                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                                translation-array print))))
  :hints (("Goal" :use (:instance type-of-simplify-xors-aux-other-params)
           :cases ((Natp v))
           :in-theory (disable type-of-simplify-xors-aux-other-params))))




;need a bound on the size?
;; (defthm renaming-arrayp-aux-of-mv-nth-5-of-simplify-xors-aux
;;   (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (pseudo-dag-arrayp new-dag-array-name new-dag-array new-dag-len)
;;                 (dag-parent-arrayp new-dag-parent-array-name new-dag-parent-array)
;;                 (bounded-dag-constant-alistp new-dag-constant-alist ..)
;;                 (all-< (strip-cdrs new-dag-constant-alist) new-dag-len)
;;                 (renaming-arrayp-aux 'translation-array translation-array (+ -1 dag-len)) ;not really a translation array since vals may be constant
;;                 (equal (alen1 new-dag-array-name new-dag-array)
;;                        (alen1 new-dag-parent-array-name
;;                                         new-dag-parent-array))
;;                 (natp n)
;;                 (natp dag-len))
;;            (renaming-arrayp-aux 'translation-array (mv-nth 5 (simplify-xors-aux n dag-array dag-len dag-parent-array dag-array-name dag-parent-array-name new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name translation-array print)) (+ -1 dag-len)))
;;   :hints (("Goal" :in-theory (enable SIMPLIFY-XORS-AUX))))

(local
 (defthm integerp-of-if
   (equal (integerp (if test tp ep))
          (if test
              (integerp tp)
            (integerp ep)))))

;disable?
(defthm natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x))))

;TODO: Consider making a version that returns an array, to avoid the caller having to convert so much between lists and arrays.
;dag-lst should not be a quotep or empty
;Returns (mv erp dag-lst-or-quotep changep) where the result is either a new dag-lst whose top node is equal to the top node of DAG-LST, or a quotep equal to the top node of DAG-LST
(defund simplify-xors (dag-lst print)
  (declare (xargs :guard (and (pseudo-dagp dag-lst)
                              (<= (* 2 (len dag-lst)) 2147483646) ;todo
                              )
                  :guard-hints (("Goal" :in-theory (disable pseudo-dag-arrayp natp quotep)))))
  (if (not (intersection-eq '(bitxor bvxor) (dag-fns dag-lst))) ;; TODO: Optimize the check
      ;; nothing to do (TODO: We could do a bit better by selecting this case if there are bvxors but all are of non-constant size)
      ;; What if there is just one xor?
      ;; And what if there are xors but they are not nested?  I suppose we still might need to commute arguments?
      (mv (erp-nil) dag-lst nil)
    (let* ( ;;convert dag-lst to an array:
           (dag-len (len dag-lst))
           (top-nodenum (top-nodenum dag-lst))
           (dag-array-name 'simplify-xors-array) ;use a better name?
           (dag-array (make-into-array dag-array-name dag-lst)) ;could pass in the len? ;add slack space?
           (dag-parent-array-name 'simplify-xors-parent-array))
      (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len)
        (declare (ignore dag-constant-alist dag-variable-alist)) ;ffixme dont waste time computing these!
        (let* ((new-dag-size (* 2 dag-len)) ;none of the nodes are valid
               (new-dag-array-name 'simplify-xors-new-array)
               (new-dag-array (make-empty-array new-dag-array-name new-dag-size)) ;will get expanded if it needs to be bigger
               (new-dag-parent-array-name 'simplify-xors-new-parent-array)
               (new-dag-parent-array (make-empty-array new-dag-parent-array-name new-dag-size))
               (new-dag-constant-alist nil)
               (new-dag-variable-alist nil)
               ;;indicates what each node in the original dag rewrote to:
               (translation-array (make-empty-array 'translation-array dag-len)))
          (prog2$ (and print
                       (cw "(Simplifying xors (len is ~x0)...~%" dag-len))
                  (mv-let (erp new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist translation-array)
                    (simplify-xors-aux 0 dag-array dag-len dag-parent-array
                                       dag-array-name dag-parent-array-name
                                       new-dag-array 0 ;;new-dag-len
                                       new-dag-parent-array new-dag-constant-alist new-dag-variable-alist new-dag-array-name new-dag-parent-array-name
                                       translation-array print)
                    (declare (ignore new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
                    (if erp
                        (mv erp nil nil)
                      (let ((result (aref1 'translation-array translation-array top-nodenum)))
                        (if (null result)
                            (prog2$ (er hard? 'simplify-xors "Unexpected missing node translation")
                                    (mv (erp-t) nil nil))
                          (if (quotep result)
                              (prog2$ (and print
                                           (cw ")~%"))
                                      (mv (erp-nil) result t))
                            (b* ((new-dag-lst (drop-non-supporters-array new-dag-array-name new-dag-array result print))
                                 ((when (<= 2147483646 (+ (len dag-lst) ;;todo: this is for equivalent-dags below but that should be made more flexible (returning an erp)
                                                          (len new-dag-lst))))
                                  (er hard? 'simplify-xors "DAGs too large.")
                                  (mv :dag-too-large nil nil))
                                 (changep (not (equivalent-dags dag-lst new-dag-lst))))
                              (progn$ (and (eq :verbose print)
                                           (progn$ (cw "(xors result:~%")
                                                   (print-list new-dag-lst)
                                                   (cw ")~%")))
                                      (and print (not changep) (cw " (No effect.)"))
                                      (and print
                                           (cw ")~%")) ;matches "Simplifying xors ..."
                                      (mv (erp-nil) new-dag-lst changep))))))))))))))

;(simplify-xors '((2 bvxor '32 0 1) (1 . x) (0 . y)) t)

;;   (let* ((dag-len (len dag))
;;          (dag-array (make-into-array 'dag-array dag))
;;          (parent-array (make-dag-parent-array-with-name 0 dag-len dag-array (make-empty-array 'parent-array dag-len)))
;;          (translation-array (make-empty-array 'translation-array dag-len)))
;;     (prog2$ (cw "Simplifying bitxors...~%" nil)
;;             (simplify-bitxors-aux 0 dag-len dag-array parent-array nil translation-array)))
;)

;; ;unlike add-to-dag2, this one doesn't allow duplicates... is it a lot slower?

;; ;term has nodenums instead of (some) variables (might have new constants though?)
;; ;might have new variables!
;; ;term might have subterms!
;; ;returns (mv nodenum new-dag) or  (mv nodenum-lst new-dag)
;; ;"term" can be a term list if the flg is t
;; ;now evaluates ground terms! - is that really necessary for simplifying bitxors?  will that ever happen?
;; (defund add-to-dag3-aux (term dag lst-flg)
;;   (declare (xargs  :GUARD (and (true-listp term)
;;                                (ALIST-with-integer-keysp dag))
;;                    :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
;;                    :verify-guards nil
;;                    ))
;;   (if lst-flg
;;       (if (consp term)
;;           (mv-let (nodenum dag)
;;                   (add-to-dag3-aux (car term) dag nil)
;;                   (mv-let (nodenums dag)
;;                           (add-to-dag3-aux (cdr term) dag t)
;;                           (mv (cons nodenum nodenums)
;;                               dag)))
;;         (mv nil dag))
;;     (if (integerp term) ;if it's a nodenum
;;         (mv term dag)
;;       (if (variablep term) ;yikes, "variablep" would hit on a integer too?
;;           (add-to-dag ;-cheap
;;            term dag)
;;         (if (fquotep term)
;;             (mv term dag) ;;(add-to-dag term dag) if it's a quotep we just return it (will check in the non-aux caller that it doesn't return just a quotep)
;;           ;;otherwise, it's a function call
;;           (let* ((fn (ffn-symb term))
;;                  (args (fargs term)))

;;             (if (eq 'if fn)

;;                 ;;if it's an IF, first try to add the test
;;                 (mv-let (test-result new-dag)
;;                         (add-to-dag3-aux (first args) dag nil)
;;                         (if (quotep test-result)
;;                             (if (unquote test-result) ;if the test is non-nil, add the then-part, else add the else-part
;;                                 (add-to-dag3-aux (second args) dag nil)
;;                               (add-to-dag3-aux (third args) dag nil))
;;                           ;; if the test isn't a quote, add both branches
;;                           (mv-let (then-result new-dag)
;;                                   (add-to-dag3-aux (second args) new-dag nil)
;;                                   (mv-let (else-result new-dag)
;;                                           (add-to-dag3-aux (third args) new-dag nil)
;;                                           (let* ((new-entry (list fn test-result then-result else-result)))
;;                                             (add-to-dag ;-cheap
;;                                              new-entry new-dag))))))

;;               (mv-let (arg-nodenums new-dag)
;;                       (add-to-dag3-aux args dag t)

;;                       ;if we can run the function, do it!
;;                       (if (and (my-all-quoteps arg-nodenums)
;;                                (member-eq fn *known-fns*))
;;                           (mv (list 'quote (eval-fn fn (unquote-list arg-nodenums)))
;;                               dag)

;;                         (let* ((new-entry (cons fn arg-nodenums)))
;;                           (add-to-dag ;-cheap
;;                            new-entry new-dag)))))))))))

;; (skip- proofs (verify-guards add-to-dag3-aux))

;; ;this calls the main routine and handles the special case where term is just a quotep
;; (defun add-to-dag3 (term dag)
;;   (declare (xargs  :GUARD (ALIST-with-integer-keysp dag)
;;             :guard-hints (("Goal" :in-theory (enable alistp-guard-hack)))
;;                    :verify-guards nil
;;             ))
;;   (mv-let (nodenum-or-quotep new-dag)
;;           (add-to-dag3-aux term dag nil)
;;           (if (quotep nodenum-or-quotep)
;;               (add-to-dag-cheap nodenum-or-quotep dag)
;;             (mv nodenum-or-quotep new-dag))))

;; (skip- proofs (verify-guards add-to-dag3))


;; (defun make-blasted-bvcat-nest-for-var (var width)
;;   (if (or (zp width)
;;           (eql 1 width))
;;       `,(mypackn (list 'new_ var '_ "0"))
;;     `(bvcat '1
;;             ,(mypackn (list 'new_ var '_  (nat-to-string (+ -1 width))))
;;             ',(+ -1 width)
;;             ,(make-blasted-bvcat-nest-for-var var (+ -1 width)))))

;; (skip- proofs (verify-guards make-blasted-bvcat-nest-for-var))

;; (defun bit-blast-vars-aux (n len dag-array var-width-alist new-dag-acc translation-array)
;;   (declare (xargs :measure (+ 1 (nfix (- len n)))
;;                   ))
;;   (if (or (not (natp n))
;;           (not (natp len))
;;           (prog2$ nil ;(cw "~x0.~%" n)
;;                   (>= n len))
;;           )
;;       new-dag-acc ;(mv new-dag-acc translation-alist)
;;     (let* ((expr (aref1 'dag-array dag-array n)))
;;       (if (variablep expr)
;;           (let* ((width (lookup-equal expr var-width-alist)))
;;             (if (not width) ;not bit-blasting this var
;;                 (mv-let (nodenum new-dag-acc)
;;                         (add-to-dag expr new-dag-acc) ;use the -cheap version?  here and elsewhere in this function?
;;                         (bit-blast-vars-aux
;;                          (+ 1 n)
;;                          len
;;                          dag-array
;;                          var-width-alist
;;                          new-dag-acc
;;                          (aset1 'translation-array translation-array n nodenum)))

;;               (mv-let (nodenum new-dag-acc)
;;                       (add-to-dag3 (make-blasted-bvcat-nest-for-var expr width)
;;                                    new-dag-acc)
;;                       (bit-blast-vars-aux
;;                        (+ 1 n)
;;                        len
;;                        dag-array
;;                        var-width-alist
;;                        new-dag-acc
;;                        (aset1 'translation-array translation-array n nodenum)))
;;               ))
;;         (if (fquotep expr)
;;             (mv-let (nodenum new-dag-acc)
;;                     (add-to-dag expr new-dag-acc)
;;                     (bit-blast-vars-aux
;;                      (+ 1 n)
;;                      len
;;                      dag-array
;;                      var-width-alist
;;                      new-dag-acc
;;                      (aset1 'translation-array translation-array n nodenum)))
;;           ;;function call
;;           (let* ((fn (ffn-symb expr))
;;                  (args (fargs expr)))
;;             (let ((fixed-up-args (fixup-args-allows-quotes-array-version-tail args translation-array nil)))
;;               (mv-let (nodenum new-dag-acc)
;;                       (add-to-dag (cons fn fixed-up-args) new-dag-acc)
;;                       (bit-blast-vars-aux (+ 1 n)
;;                                           len
;;                                           dag-array
;;                                           var-width-alist
;;                                           new-dag-acc
;;                                           (aset1 'translation-array translation-array n nodenum))))))))))

;; (skip- proofs (verify-guards bit-blast-vars-aux))

;; (defun bit-blast-vars (dag var-width-alist)
;;   (let* ((dag-len (len dag))
;;          (dag-array (make-into-array 'dag-array dag))
;; 	 (translation-array (make-empty-array 'translation-array dag-len))
;; 	 )
;;     (bit-blast-vars-aux 0 dag-len dag-array var-width-alist nil translation-array)))

;; (skip- proofs (verify-guards bit-blast-vars))

;; (defun rename-vars-aux (n len dag-array renaming-alist new-dag-acc)
;;   (declare (xargs :measure (+ 1 (nfix (- len n)))
;;                   ))
;;   (if (or (not (natp n))
;;           (not (natp len))
;;           (prog2$ nil ;(cw "~x0.~%" n)
;;                   (>= n len))
;;           )
;;       new-dag-acc ;(mv new-dag-acc translation-alist)
;;     (let* ((expr (aref1 'dag-array dag-array n)))
;;       (if (variablep expr)
;;           (let* ((possible-match (lookup-eq expr renaming-alist))
;;                  (new-name (if possible-match possible-match expr)))
;;             (mv-let (nodenum new-dag-acc)
;;                     (add-to-dag new-name new-dag-acc) ;use the -cheap version?  here and elsewhere in this function?
;;                     (declare (ignore nodenum))
;;                     (rename-vars-aux
;;                      (+ 1 n)
;;                      len
;;                      dag-array
;;                      renaming-alist
;;                      new-dag-acc
;;                     )))
;;         (if (fquotep expr)
;;             (mv-let (nodenum new-dag-acc)
;;                     (add-to-dag expr new-dag-acc)
;;                     (declare (ignore nodenum))
;;                     (rename-vars-aux
;;                      (+ 1 n)
;;                      len
;;                      dag-array
;;                      renaming-alist
;;                      new-dag-acc
;;                     ))
;;           ;;function call
;;           (let* ((fn (ffn-symb expr))
;;                  (args (fargs expr)))
;;             (mv-let (nodenum new-dag-acc)
;;                     (add-to-dag (cons fn args) new-dag-acc)
;;                     (declare (ignore nodenum))
;;                     (rename-vars-aux (+ 1 n)
;;                                      len
;;                                      dag-array
;;                                      renaming-alist
;;                                      new-dag-acc
;;                     ))))))))

;; (skip- proofs (verify-guards rename-vars-aux))

;; ;this one doesn't change any node numbering, just renames vars
;; (defun rename-vars (dag renaming-alist)
;;   (let* ((dag-len (len dag))
;;          (dag-array (make-into-array 'dag-array dag))
;; 	 )
;;     (rename-vars-aux 0 dag-len dag-array renaming-alist nil)))

;; (skip- proofs (verify-guards rename-vars))


;BOZO move this stuff

;; (defun resolve-refs-to-constants-in-args2
;;   (args dag)
;;   (if
;;    (endp args)
;;    nil
;;    (let
;;     ((arg (car args)))
;;     (if
;;      (atom arg)
;;      (let
;;       ((expr (lookup arg dag)))
;;       (if (and (consp expr)
;;                (fquotep expr)
;;                ;(not (consp (unquote expr)))
;;                )
;;           (cons expr
;;                 (resolve-refs-to-constants-in-args2 (cdr args)
;;                                                    dag))
;;           (cons arg
;;                 (resolve-refs-to-constants-in-args2 (cdr args)
;;                                                    dag))))
;;      (cons arg
;;            (resolve-refs-to-constants-in-args2 (cdr args)
;;                                               dag))))))

;; (skip- proofs (verify-guards RESOLVE-REFS-TO-CONSTANTS-IN-ARGS2))

;; (DEFUN RESOLVE-REFS-TO-CONSTANTS2 (DAG)
;;   (IF
;;    (ENDP DAG)
;;    NIL
;;    (LET*
;;     ((ENTRY (CAR DAG))
;;      (NODENUM (CAR ENTRY))
;;      (EXPR (CDR ENTRY)))
;;     (IF
;;      (OR (NOT (CONSP EXPR)) (FQUOTEP EXPR))
;;      (CONS ENTRY
;;            (RESOLVE-REFS-TO-CONSTANTS2 (CDR DAG)))
;;      (LET*
;;       ((FN (CAR EXPR))
;;        (ARGS (FARGS EXPR))
;;        (NEW-ARGS (RESOLVE-REFS-TO-CONSTANTS-IN-ARGS2 ARGS DAG)))
;;       (CONS (CONS NODENUM (CONS FN NEW-ARGS))
;;             (RESOLVE-REFS-TO-CONSTANTS2 (CDR DAG))))))))

;; (skip- proofs (verify-guards RESOLVE-REFS-TO-CONSTANTS2))

;; (defun add-as-parent-for-nodes (parent children parent-array)
;;   (if (endp children)
;;       parent-array
;;     (let* ((current-parents (aref1 'parent-array parent-array (car children)))
;;            (new-parents (cons parent current-parents)))
;;       (add-as-parent-for-nodes parent
;;                                (cdr children)
;;                                (aset1 'parent-array parent-array (car children) new-parents)))))

;; (skip- proofs (verify-guards add-as-parent-for-nodes))

;; (defun make-dag-parent-array-with-name (n len dag-array parent-array)
;;   (declare (xargs :measure (+ 1 (nfix (- len n)))
;;                   ))
;;   (if (or (not (natp n))
;;           (not (natp len))
;;           (>= n len))
;;       parent-array
;;     (let ((expr (aref1 'dag-array dag-array n)))
;;       (if (or (variablep expr)
;;               (fquotep expr))
;;           (make-dag-parent-array-with-name (+ 1 n) len dag-array parent-array)
;;         (let* ((args (dargs expr))
;;                (node-args (keep-non-quoteps-tail args nil)))
;;           (make-dag-parent-array-with-name (+ 1 n)
;;                              len
;;                              dag-array
;;                              (add-as-parent-for-nodes n node-args parent-array)))))))

;; (skip- proofs (verify-guards make-dag-parent-array-with-name))

;; ;kill
;; (defun add-bitxor-nest-to-dag-array (leaves)
;;   (if (endp leaves)
;;       ''0 ;bozo yuck?
;;     (if (endp (cdr leaves))
;;         `(getbit '0 ,(car leaves))
;;       (if (endp (cdr (cdr leaves)))
;;           `(bitxor ,(first leaves) ,(second leaves))
;;         ;; more than 2 leaves
;;         `(bitxor ,(first leaves)
;;                  ,(add-bitxor-nest-to-dag-array (cdr leaves)))))))

;; (skip- proofs (verify-guards add-bitxor-nest-to-dag-array))

;;BBOZO move this stuff to another file

;; ;could speed this up...
;; ;nodenum might be a quoted constant
;; ;do we expect bitxor nests to be associated to grow to the right?
;; ;should now be tail-recursive on one call
;; (skip- proofs
;;  (defun get-bitxor-nest-leaves (nodenum dag-array dag-array-name acc)
;;    (if (quotep nodenum)
;;        (cons nodenum acc) ;i don't see a reason to reverse the acc, since we'll sort these later
;;      ;;it's a nodenum:
;;      (let ((expr (aref1 dag-array-name dag-array nodenum)))
;;        (if (or (atom expr) ;(variablep expr)
;;                (not (eq 'bitxor (ffn-symb expr))))
;;            (cons nodenum acc) ;i don't see a reason to reverse the acc, since we'll sort these later

;;          ;;otherwise, it's a call to bitxor
;;          ;; without the let, weird stuff happened
;;          (let ((acc (get-bitxor-nest-leaves (first (dargs expr)) dag-array dag-array-name acc)))
;;            (get-bitxor-nest-leaves (second (dargs expr))
;;                                    dag-array
;;                                    dag-array-name
;;                                    ;;this call should be cheap if bitxor nests are associated to the right
;;                                    acc)))))))

;; (skip- proofs (verify-guards get-bitxor-nest-leaves))

;; ;do we already have something like this?
;; (defun integerp-or-quotep (x)
;;   (declare (xargs :guard t))
;;   (or (integerp x)
;;       (and (consp x)
;;            (eq 'quote (car x))
;;            (consp (cdr x)))))

;; ;do we already have something like this?
;; (defun integerp-or-quotep-lst (x)
;;   (declare (xargs :guard t))
;;   (if (atom x)
;;       t
;;     (and (integerp-or-quotep (car x))
;;          (integerp-or-quotep-lst (cdr x)))))

;; ;reverses the order of non-quoteps, but that shouldn't matter (the caller of this later sorts)
;; (defun filter-quoteps-and-xor (items constant-acc non-quotep-acc)
;;   (declare (type integer constant-acc)
;;            (xargs :guard (integerp-or-quotep-lst items))
;;            )
;;   (if (atom items) ;use endp?
;;       (mv constant-acc non-quotep-acc) ;not reversing the accs
;;     (let ((item (car items)))
;;       (if (quotep item)
;;           (filter-quoteps-and-xor (cdr items) (bitxor (ifix (unquote item)) constant-acc) non-quotep-acc)
;;         (filter-quoteps-and-xor (cdr items) constant-acc (cons item non-quotep-acc))))))

;; (defun make-reversed-bitxor-nest-aux (leaves acc)
;;   (if (endp leaves)
;;       acc
;;     (make-reversed-bitxor-nest-aux (cdr leaves)
;;                                    `(bitxor ,(first leaves)
;;                                             ,acc))))

;; (skip- proofs (verify-guards make-reversed-bitxor-nest-aux))

;; (defun make-reversed-bitxor-nest (leaves)
;;   (if (endp leaves)
;;       ''0 ;bozo yuck?
;;     (if (endp (cdr leaves))
;;         `(getbit '0 ,(car leaves))
;;       ;;at least two leaves:
;;       (make-reversed-bitxor-nest-aux (cddr leaves)
;;                                      ;we are reversing, so second comes first
;;                                      `(bitxor ,(second leaves) ,(first leaves))))))

;; (skip- proofs (verify-guards make-reversed-bitxor-nest))

;; ;fixme doesn't something like this already exist?
;; (skip- proofs
;;  (mutual-recursion
;;   ;;returns (mv nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;; ;ffixme allow variables?
;;   (defun add-term-to-dag (term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
;;     (if (integerp term)
;;         (mv term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;       (if (fquotep term)
;;           (mv term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;         ;; function call
;;         (let* ((fn (ffn-symb term))
;;                (args (fargs term)))
;;           (mv-let (args-indices dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                   (add-term-to-dag-lst args dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
;;                   (let* ((expr (cons fn args-indices)))
;;                     (add-function-call-expr-to-dag-array-with-name ..expr
;;                                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))))

;;   (defun add-term-to-dag-lst (term-lst dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
;;     (if (endp term-lst)
;;         (mv nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;       (mv-let (car-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;               (add-term-to-dag (car term-lst) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
;;               (mv-let (cdr-result dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;                       (add-term-to-dag-lst (cdr term-lst) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
;;                       (mv (cons car-result cdr-result)
;;                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))))

;; (skip- proofs (verify-guards add-term-to-dag))


;uses car instead of nth to check for a quotep
(defthm integerp-of-nth-of-dargs-alt
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr))))
           (equal (integerp (nth n (dargs expr)))
                  (not (consp (nth n (dargs expr))))))
  :hints (("Goal" :in-theory (enable integerp-of-nth-when-all-dargp))))

;; we prefer nth of dargs
(defthmd car-of-dargs
  (equal (car (dargs expr))
         (nth 0 (dargs expr))))



;move
(DEFTHM rationalp-OF-NTH-WHEN-ALL-INTEGERP
  (IMPLIES (AND (ALL-INTEGERP X)
                (NATP N)
                (< N (LEN X)))
           (rationalp (NTH N X)))
  :HINTS (("Goal" :IN-THEORY (ENABLE ALL-INTEGERP (:i NTH)))))

;move
;args are sorted in increasing order
;result is sorted in decreasing order
(defund merge-and-remove-dups (lst1 lst2 acc)
  (declare (xargs :measure (+ 1 (len lst1) (len lst2))
                  :guard (and (all-integerp lst1)
                              (true-listp lst1)
                              (all-integerp lst2)
                              (true-listp lst2)
                              (all-integerp acc))))
  (if (endp lst1)
      (revappend lst2 acc)
    (if (endp lst2)
        (revappend lst1 acc)
      (let ((item1 (first lst1))
            (item2 (first lst2)))
        (if (< item1 item2)
            (merge-and-remove-dups (rest lst1) lst2 (cons item1 acc))
          (if (< item2 item1)
              (merge-and-remove-dups lst1 (rest lst2) (cons item2 acc))
            ;;they are equal, so drop them both
            (merge-and-remove-dups (rest lst1) (rest lst2) acc)))))))
