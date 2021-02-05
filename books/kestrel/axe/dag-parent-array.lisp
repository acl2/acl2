; Using the dag-parent-array
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
(include-book "bounded-dag-parent-arrayp")
(include-book "no-atoms")
(include-book "shorter-list")

;; This book deals with populating and using the dag-parent-array.
;; See also dag-parent-arrayp.lisp and bounded-dag-parent-arrayp.lisp.
;; See also parent-array-with-name.lisp.

;; NOTE: Do not change the parent array (e.g., to store only partial parent
;; info) without considering the effect on tools like
;; rebuild-literals-with-substitution2 that expect all parents to be stored.

;;;
;;; find-shortest-parent-lst
;;;

;the first list might be very long, so we don't want to walk down it.
;items are nodenums and quoteps
(defund find-shortest-parent-lst (current-shortest-lst items dag-parent-array)
  (declare (xargs :guard (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                              (true-listp items)
                              (true-listp current-shortest-lst))))
  (if (endp items)
      current-shortest-lst
    (let ((item (first items)))
      (if (not (atom item)) ;skip quoteps
          (find-shortest-parent-lst current-shortest-lst (rest items) dag-parent-array)
        ;; it's a nodenum, so check whether its parent list is shorter than current-shortest-lst
        (let* ((new-lst (aref1 'dag-parent-array dag-parent-array item)))
          (find-shortest-parent-lst (shorter-lst current-shortest-lst
                                                 new-lst
                                                 current-shortest-lst
                                                 new-lst)
                                    (rest items)
                                    dag-parent-array))))))

(defthm nat-listp-of-find-shortest-parent-lst
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (nat-listp current-shortest-lst)
                (all-dargp items))
           (nat-listp (find-shortest-parent-lst current-shortest-lst items dag-parent-array)))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst))))

(defthm true-listp-of-find-shortest-parent-lst
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                (true-listp current-shortest-lst)
                (all-dargp items))
           (true-listp (find-shortest-parent-lst current-shortest-lst items dag-parent-array)))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst))))

(defthm all-<-of-find-shortest-parent-lst
  (implies (and ;(dag-parent-arrayp 'dag-parent-array dag-parent-array top-nodenum-to-check)
            ;; (true-listp items)
            (bounded-dag-parent-entriesp n 'dag-parent-array dag-parent-array limit)
            (all-< current-shortest-lst limit)
            (all-dargp-less-than items (+ 1 n))
            ;;(all-dargp items)
            (integerp n))
           (all-< (find-shortest-parent-lst current-shortest-lst items dag-parent-array)
                  limit))
  :hints (("Goal" :in-theory (enable find-shortest-parent-lst dag-parent-arrayp bound-lemma-for-car-when-all-dargp-less-than))))

;;returns (mv first-atom rest)
(defund first-atom (items)
  (declare (xargs :guard (and (true-listp items))))
  (if (endp items)
      (mv (hard-error 'first-atom "We expected to find an atom" nil) nil)
    (let ((item (car items))
          (rest (cdr items)))
      (if (atom item)
          (mv item rest)
        (first-atom rest)))))

(defthm all-dargp-less-than-of-mv-nth-1-of-first-atom
  (implies (all-dargp-less-than args bound)
           (all-dargp-less-than (mv-nth 1 (first-atom args)) bound))
  :hints (("Goal" :in-theory (enable first-atom))))

(defthm <-of-mv-nth-0-of-first-atom
  (implies (and (all-dargp-less-than args bound)
                (natp bound)
                (not (no-atoms args))
                )
           (< (mv-nth 0 (first-atom args)) bound))
  :hints (("Goal" :in-theory (enable first-atom ALL-DARGP-LESS-THAN no-atoms))))

(defthm true-listp-of-mv-nth-1-of-first-atom
  (implies (true-listp args)
           (true-listp (mv-nth 1 (first-atom args))))
  :hints (("Goal" :in-theory (enable first-atom))))

(defthm natp-of-mv-nth-0-of-first-atom
  (implies (and (all-dargp args)
                (not (no-atoms args)))
           (natp (mv-nth 0 (first-atom args))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable first-atom no-atoms))))

(defthm integerp-of-mv-nth-0-of-first-atom
  (implies (and (all-dargp args)
                (not (no-atoms args)))
           (integerp (mv-nth 0 (first-atom args))))
  :hints (("Goal" :in-theory (enable first-atom))))

(defthm <=-of-0-and-mv-nth-0-of-first-atom
  (implies (and (all-dargp args)
                (not (no-atoms args)))
           (<= 0 (mv-nth 0 (first-atom args)))))

(defthm all-dargp-of-mv-nth1-of-first-atom
  (implies (all-dargp items)
           (all-dargp (mv-nth 1 (first-atom items))))
  :hints (("Goal" :in-theory (enable first-atom))))

(defthm not-<-of-largest-non-quotep-and-mv-nth-0-of-first-atom
  (implies (and (not (no-atoms items))
                (all-dargp items))
           (not (< (largest-non-quotep items)
                   (mv-nth '0 (first-atom items)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep first-atom no-atoms))))

(defthm first-atom-bound-lemma
  (implies (and (<= (largest-non-quotep items) x)
                (not (no-atoms items))
                (all-dargp items))
           (not (< x
                   (mv-nth '0 (first-atom items)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable largest-non-quotep first-atom no-atoms))))

(defthm all-dargp-less-than-of-plus1-of-largest-non-quotep
 (implies (and (not (no-atoms items))
               (all-dargp items))
          (all-dargp-less-than items (+ 1 (largest-non-quotep items))))
 :hints (("Goal" :in-theory (enable largest-non-quotep all-dargp-less-than no-atoms))))

;rename
(defthm all-dargp-less-than-lemma2
  (implies (and (not (no-atoms items))
                (all-dargp items))
           (not (< (largest-non-quotep items)
                   (largest-non-quotep (mv-nth 1 (first-atom items))))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable first-atom no-atoms))))

(defthm <-of-largest-non-quotep-and-0
  (implies (all-dargp items)
           (equal (< (largest-non-quotep items) 0)
                  (no-atoms items)))
  :hints (("Goal" :in-theory (enable no-atoms))))

(defthm all-dargp-less-than-lemma
  (implies (and (not (no-atoms items))
                (all-dargp items))
           (all-dargp-less-than (mv-nth 1 (first-atom items))
                                           (+ 1 (largest-non-quotep items))))
  :hints (("Goal" :in-theory (enable largest-non-quotep first-atom no-atoms))))

;;;
;;; find-matching-node
;;;

;returns the nodenum from NODENUMS at which (cons fn args) exists (if any), otherwise nil
(defund find-matching-node (fn args nodenums dag-array)
  (declare (xargs :guard (and (symbolp fn)
                              (not (equal 'quote fn))
                              (array1p 'dag-array dag-array)
                              (nat-listp nodenums)
                              (all-< nodenums (alen1 'dag-array dag-array)))))
  (if (endp nodenums)
      nil
    (let* ((nodenum (car nodenums))
           (expr (aref1 'dag-array dag-array nodenum)))
      (if (and (consp expr) ;; TODO: Drop this check (maybe add a type decl) since the expr is always a cons?
               (eq fn (ffn-symb expr))
               (equal args (fargs expr)))
          nodenum
        (find-matching-node fn args (cdr nodenums) dag-array)))))

(defthm integerp-of-find-matching-node
  (implies (nat-listp nodenums)
           (iff (integerp (find-matching-node fn args nodenums dag-array))
                (find-matching-node fn args nodenums dag-array)))
  :hints (("Goal" :in-theory (enable find-matching-node))))

(defthm nonneg-of-find-matching-node
  (implies (nat-listp nodenums)
           (<= 0 (find-matching-node fn args nodenums dag-array)))
  :hints (("Goal" :in-theory (enable find-matching-node))))

;;;
;;; find-expr-using-parents
;;;

;;returns the nodenum of (cons fn args) in dag-array, or nil if it's not present
;expr must have at last one child that's a nodenum (not a quotep).  we pick such a child and then compare expr to each of its parents
(defund find-expr-using-parents (fn args dag-array dag-parent-array dag-len)
  (declare (xargs :guard (and (symbolp fn)
                              (not (equal 'quote fn))
                              (true-listp args)
                              (not (no-atoms args)) ;at least one child must be a nodenum so we can look up its parents
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (all-dargp-less-than args dag-len)
                              (equal (alen1 'dag-array dag-array)
                                     (alen1 'dag-parent-array dag-parent-array)))
                  :guard-hints (("Goal" :use (:instance all-<-of-find-shortest-parent-lst
                                                        (limit (alen1 'dag-array dag-array))
                                                        (dag-parent-array dag-parent-array)
                                                        (items (mv-nth 1 (first-atom args)))
                                                        (current-shortest-lst
                                                         (aref1 'dag-parent-array
                                                                dag-parent-array
                                                                (mv-nth 0 (first-atom args))))
                                                        (n  (+ -1 (alen1 'dag-array dag-array))))
                                 :in-theory (e/d (<-of-+-of-minus1-arith-hack bounded-dag-parent-arrayp)
                                                 (all-<-of-find-shortest-parent-lst)))))
           (ignore dag-len) ;todo: avoid passing this in?
           )
  (mv-let (first-node-child rest)
    (first-atom args)
    ;; TODO: Think about whether it is worth it to find the shortest parent list here (maybe not, if the parent array could store exprs rather than nodenums -- could also index by function symbol):
    (let ((parents (find-shortest-parent-lst (aref1 'dag-parent-array dag-parent-array first-node-child)
                                             rest
                                             dag-parent-array)))
      (find-matching-node fn args parents dag-array))))

(defthm integerp-of-find-expr-using-parents
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                ;(symbolp fn)
                ;(not (equal 'quote fn))
                (all-dargp args)
                ;(true-listp args)
                (not (no-atoms args)))
           (iff (integerp (find-expr-using-parents fn args dag-array dag-parent-array dag-len))
                (find-expr-using-parents fn args dag-array dag-parent-array dag-len)))
  :hints (("Goal" :in-theory (enable find-expr-using-parents))))

(defthm nonneg-of-find-expr-using-parents
  (implies (and (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                ;(symbolp fn)
                ;(not (equal 'quote fn))
                (all-dargp args)
                ;(true-listp args)
                (not (no-atoms args)))
           (<= 0 (find-expr-using-parents fn args dag-array dag-parent-array dag-len)))
  :hints (("Goal" :in-theory (enable find-expr-using-parents))))

(defthm <-of-find-matching-node
  (implies (and (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)
                (natp dag-len)
;                (array1p 'dag-array dag-array)
                (nat-listp nodenums)
                (true-listp nodenums)
                (all-< nodenums dag-len ;(alen1 'dag-array dag-array)
                       )
                (find-matching-node fn args nodenums dag-array))
           (< (find-matching-node fn args nodenums dag-array)
              dag-len))
  :hints (("Goal" :in-theory (enable find-matching-node))))



;; (thm
;;  (ALL-< (FIND-SHORTEST-PARENT-LST (AREF1 'DAG-PARENT-ARRAY
;;                                         DAG-PARENT-ARRAY
;;                                         (MV-NTH '0 (FIRST-ATOM (DARGS EXPR))))
;;                                  (MV-NTH '1 (FIRST-ATOM (DARGS EXPR)))
;;                                  DAG-PARENT-ARRAY)
;;        DAG-LEN)

(defthm <-of-find-expr-using-parents
  (implies (and (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                (not (no-atoms args))
                (all-dargp-less-than args (alen1 'dag-array dag-array))
                (natp dag-len)
                (equal (alen1 'dag-array dag-array)
                       (alen1 'dag-parent-array dag-parent-array))
                (find-expr-using-parents fn args dag-array dag-parent-array dag-len))
           (< (find-expr-using-parents fn args dag-array dag-parent-array dag-len) dag-len))
  :hints (("Goal"
           :use ((:instance all-<-of-aref1-when-bounded-dag-parent-entriesp
                            (limit2 dag-len)
                            (limit dag-len)
                            (n (mv-nth 0 (first-atom args)))
                            (dag-parent-array dag-parent-array)
                            (dag-parent-array-name 'dag-parent-array))
                 (:instance all-<-of-find-shortest-parent-lst
                            (n (+ -1 (alen1 'dag-array dag-array)))
                            (limit dag-len)
                            (dag-parent-array dag-parent-array)
                            (items (mv-nth 1 (first-atom args)))
                            (current-shortest-lst
                             (aref1 'dag-parent-array
                                    dag-parent-array
                                    (mv-nth 0 (first-atom args)))))
                 (:instance <-of-find-matching-node
                            (dag-len dag-len)
                            (dag-array dag-array)
                            (nodenums (find-shortest-parent-lst
                                       (aref1 'dag-parent-array
                                              dag-parent-array
                                              (mv-nth 0 (first-atom args)))
                                       (mv-nth 1 (first-atom args))
                                       dag-parent-array))
                            (dag-parent-array-name 'dag-parent-array)
                            ))
           :in-theory (e/d (bounded-dag-parent-arrayp
                            find-expr-using-parents)
                           (all-<-of-find-shortest-parent-lst
                            ;<-of-find-matching-node
                            )))))

;;;
;;; add-to-parents-of-atoms
;;;

;;add NODENUM to the parent lists for those ITEMS which are not quoteps
;; Same as add-to-parents-of-atoms-with-name except this fixes 'dag-parent-array as the dag-parent-array-name.
(defund add-to-parents-of-atoms (items nodenum dag-parent-array)
  (declare (xargs :guard (and (true-listp items)
                              (natp nodenum)
                              (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                              (all-dargp-less-than items nodenum)
                              (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array)))))
  (if (endp items)
      dag-parent-array
    (let ((item (first items)))
      (if (atom item)
          (let* ((old-parents (aref1 'dag-parent-array dag-parent-array item))
                 (new-parents (cons ;add-to-set-eql ;i think it's okay to just use cons here, since the nodenum being added is a new node in the dag (so it shouldn't already be among the parents) -- todo: what if two children of a node are the same?
                               nodenum old-parents))) ;fixme what if this is used in merging?
            (add-to-parents-of-atoms (rest items)
                                     nodenum
                                     (aset1 'dag-parent-array dag-parent-array item new-parents)))
        (add-to-parents-of-atoms (rest items) nodenum dag-parent-array)))))

(defthm array1p-of-add-to-parents-of-atoms
  (implies (and (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                ;(all-dargp items)
                (natp nodenum)
                ;(<= nodenum top-nodenum-to-check)
                (array1p 'dag-parent-array dag-parent-array))
           (array1p 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms integer-listp))))

(defthm default-of-add-to-parents-of-atoms
  (implies (and (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                ;(all-dargp items)
                (natp nodenum)
                ;(<= nodenum top-nodenum-to-check)
                (array1p 'dag-parent-array dag-parent-array))
           (equal (default 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array))
                  (default 'dag-parent-array dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms integer-listp))))

(defthm alen1-of-add-to-parents-of-atoms
  (implies (all-dargp items) ;(natp nodenum)
           (equal (alen1 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array))
                  (alen1 'dag-parent-array dag-parent-array)))
  :hints (("Goal" :in-theory (enable add-to-parents-of-atoms integer-listp))))

(defthm all-dag-parent-entriesp-of-add-to-parents-of-atoms
  (implies (and (all-dargp-less-than items nodenum)
                (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                (natp nodenum)
                (integerp n)
                (array1p 'dag-parent-array dag-parent-array)
                ;(< nodenum (alen1 'dag-parent-array dag-parent-array))
                (< n (alen1 'dag-parent-array dag-parent-array))
                (all-dag-parent-entriesp n 'dag-parent-array dag-parent-array))
           (all-dag-parent-entriesp n 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array)))
  :hints (("Subgoal *1/6" :cases ((< N (CAR ITEMS))))
          ("Goal" :in-theory (enable add-to-parents-of-atoms integer-listp
                                     <-of-car-when-all-dargp-less-than
                                     not-<-of-car-when-all-dargp-less-than))))

(defthm dag-parent-arrayp-of-add-to-parents-of-atoms
  (implies (and (all-dargp-less-than items nodenum)
                (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                (natp nodenum)
                ;(< nodenum (alen1 'dag-parent-array dag-parent-array))
                (dag-parent-arrayp 'dag-parent-array dag-parent-array))
           (dag-parent-arrayp 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp add-to-parents-of-atoms integer-listp))))

(defthm all-<-of-aref1-of-add-to-parents-of-atoms
  (implies (and (natp n)
                (natp nodenum)
                (array1p 'dag-parent-array dag-parent-array)
                (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array))
                (< n (alen1 'dag-parent-array dag-parent-array))
                (< nodenum limit)
                (all-< (aref1 'dag-parent-array dag-parent-array n) limit))
           (all-< (aref1 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array) n) limit))
  :hints (("Goal" :in-theory (enable add-to-parents-of-atoms))))

(defthm bounded-dag-parent-entriesp-of-add-to-parents-of-atoms
  (implies (and (bounded-dag-parent-entriesp n 'dag-parent-array dag-parent-array limit)
                (natp nodenum)
                (< nodenum limit)
                (natp limit)
                (array1p 'dag-parent-array dag-parent-array)
                (< n (alen1 'dag-parent-array dag-parent-array))
                (all-dargp-less-than items (alen1 'dag-parent-array dag-parent-array)))
           (bounded-dag-parent-entriesp n 'dag-parent-array (add-to-parents-of-atoms items nodenum dag-parent-array) limit))
  :hints (("Goal" :in-theory (enable bounded-dag-parent-entriesp))))
