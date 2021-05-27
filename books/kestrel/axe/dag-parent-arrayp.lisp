; Tracking parents of nodes in a DAG
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

;; The parent-array maps nodes in the DAG to lists of all of their parents.
;; For example, if node 1000 is (bvxor '32 2 3), then the parent-array includes
;; node 1000 in the parent lists for nodes 2 and 3.  The parent-array can be
;; used to quickly determine whether a function-call expression already exists
;; in the DAG, by checking the parents of one of the nodes mentioned in the
;; expression.  For example, to check whether (bvxor '32 2 3) already exists in
;; the DAG, go through the parents of node 2 (or node 3), checking whether any
;; of them is the expression (bvxor '32 2 3).

;; TODO: Consider only storing a node in the parent list of its largest child
;; (may need to make a variant that does that).

;; TODO: Consider having the parent-array store the actual expressions, not the
;; nodenums (perhaps an alist from expressions to nodenums).

;; TODO: Consider having the parent-array index parent expressions by top
;; function symbol?

;; TODO: Add fixnum declarations?

;; See also parent-arrays.lisp.

(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/typed-lists-light/all-greater" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "bounded-dag-exprs")
(include-book "kestrel/acl2-arrays/expandable-arrays" :dir :system)
;(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (enable symbolp-of-car-when-dag-exprp0)))

(defthmd all-dargp-less-than-when-<-of-largest-non-quotep
  (implies (and (< (largest-non-quotep items) bound)
;                (not (all-consp items))
                (all-dargp items))
           (all-dargp-less-than items bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than all-dargp
                                     ;;all-consp
                                     largest-non-quotep))))

;may help during backchaining?
(defthmd <-of-+-of-minus1-arith-hack
  (implies (and (integerp x)
                (integerp y))
           (equal (< (binary-+ '-1 x) y)
                  (<= x y))))

;disable?
;move
(defthm <-of-maxelem-when-all->
  (implies (and (all-> x n)
                (consp x))
           (< n (maxelem x)))
  :hints (("Goal" :in-theory (enable maxelem all->))))

(defthm not-<-of-car-when-all-<-2
  (implies (and (all-< items (+ 1 bound))
                (integerp bound)
                (integerp (car items))
                (consp items))
           (not (< bound (car items)))))

(defthm integerp-of-car-when-nat-listp-cheap
  (implies (and (nat-listp x)
                (consp x))
           (integerp (car x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;;;
;;; all-dag-parent-entriesp
;;;

;; This also works for unassigned array elems, for which we get the default value.
;; Requires that all the parents are greater than the node.
(defund all-dag-parent-entriesp (n dag-parent-array-name dag-parent-array)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (integerp n)
                              (array1p dag-parent-array-name dag-parent-array)
                              (< n (alen1 dag-parent-array-name dag-parent-array)))))
  (if (not (natp n))
      t
    (let ((parents (aref1 dag-parent-array-name dag-parent-array n)))
      (and (nat-listp parents)
           ;; todo: require no duplicates?
           (all-> parents n) ;todo: switch to using <-all?
           (all-dag-parent-entriesp (+ -1 n) dag-parent-array-name dag-parent-array)))))

(defthm all-dag-parent-entriesp-monotone-1
  (implies (and (all-dag-parent-entriesp n1 dag-parent-array-name dag-parent-array)
                (<= n2 n1)
                (integerp n1)
                (integerp n2)
                (integerp limit))
           (all-dag-parent-entriesp n2 dag-parent-array-name dag-parent-array))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

;; (defthm all-dag-parent-entriesp-monotone-2
;;   (implies (and (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit1)
;;                 (<= limit1 limit2)
;;                 (integerp n)
;;                 (integerp limit1)
;;                 (integerp limit2))
;;            (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array limit2)))

(defthm true-listp-of-aref1-when-all-dag-parent-entriesp
  (implies (and (all-dag-parent-entriesp m dag-parent-array-name dag-parent-array)
                (<= n m)
                (integerp m)
                (natp n))
           (true-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

(defthm nat-listp-of-aref1-when-all-dag-parent-entriesp
  (implies (and (all-dag-parent-entriesp m dag-parent-array-name dag-parent-array)
                (<= n m)
                (integerp m)
                (natp n))
           (nat-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

(defthm integer-listp-of-aref1-when-all-dag-parent-entriesp
  (implies (and (all-dag-parent-entriesp m dag-parent-array-name dag-parent-array)
                (<= n m)
                (integerp m)
                (natp n))
           (integer-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

(defthm all-integerp-of-aref1-when-all-dag-parent-entriesp
  (implies (and (all-dag-parent-entriesp m dag-parent-array-name dag-parent-array)
                (<= n m)
                (integerp m)
                (natp n))
           (all-integerp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

;todo: deprecate?
(defthm all->-of-aref1-when-all-dag-parent-entriesp
  (implies (and (all-dag-parent-entriesp m dag-parent-array-name dag-parent-array)
                (<= n m)
                (integerp m)
                (natp n))
           (all-> (aref1 dag-parent-array-name dag-parent-array n) n))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

(defthm all-dag-parent-entriesp-of-aset1
  (implies (and (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array)
                (integerp n)
                (natp index)
                (< index (alen1 dag-parent-array-name dag-parent-array))
;                (true-listp val)
                (implies (<= index n)
                         (and (nat-listp val)
                              (all-> val index)))
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (array1p dag-parent-array-name dag-parent-array))
           (all-dag-parent-entriesp n dag-parent-array-name (aset1 dag-parent-array-name dag-parent-array index val)))
  :hints (("Goal" :in-theory (enable all-dag-parent-entriesp))))

(defthm all-dag-parent-entriesp-of-make-empty-array
  (implies (and ;(natp n)
            (< n size)
            (natp size)
            (symbolp dag-parent-array-name)
            (< size 2147483647))
           (all-dag-parent-entriesp n
                                    dag-parent-array-name
                                    (make-empty-array dag-parent-array-name
                                                      size)))
  :hints (("Goal" :expand (all-dag-parent-entriesp 0 dag-parent-array-name
                                                   (make-empty-array dag-parent-array-name size))
           :in-theory (enable all-dag-parent-entriesp))))

(defthm all-dag-parent-entriesp-of-compress1
  (implies (and (force (array1p dag-parent-array-name dag-parent-array))
                (< n (alen1 dag-parent-array-name dag-parent-array)))
           (equal (all-dag-parent-entriesp n dag-parent-array-name (compress1 dag-parent-array-name dag-parent-array))
                  (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable all-dag-parent-entriesp ))))

(defthm all-dag-parent-entriesp-of-cons-of-cons-of-header
  (implies (and (force (array1p dag-parent-array-name dag-parent-array))
                ;(< n (alen1 dag-parent-array-name dag-parent-array))
                (integerp n)
                (<= (alen1 dag-parent-array-name dag-parent-array)
                    (car (cadr (assoc-keyword :dimensions header))))
                (equal (cadr (assoc-keyword :default header))
                       (default dag-parent-array-name dag-parent-array))
                (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array))
           (all-dag-parent-entriesp n dag-parent-array-name (cons (cons :header header) dag-parent-array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((all-dag-parent-entriesp 0 dag-parent-array-name dag-parent-array)
                    (all-dag-parent-entriesp 0 dag-parent-array-name
                                  (cons (cons :header header) dag-parent-array)))
           :in-theory (enable all-dag-parent-entriesp header aref1))))

(defthm all-dag-parent-entriesp-of-maybe-expand-array
  (implies (and (array1p dag-parent-array-name dag-parent-array)
                (all-dag-parent-entriesp (+ -1 (alen1 dag-parent-array-name dag-parent-array))
                                         dag-parent-array-name dag-parent-array)
                (natp index)
                (<= index 2147483645)
                (equal (default dag-parent-array-name dag-parent-array) nil)
;                (<= (+ -1 (alen1 dag-parent-array-name dag-parent-array)) index)
                ;; (integerp n)
                ;; (<= -1 n)
    ;                (<= n index)
                (<= new-len (alen1 dag-parent-array-name (maybe-expand-array dag-parent-array-name dag-parent-array index)))
                )
           (all-dag-parent-entriesp new-len
                                    dag-parent-array-name
                                    (maybe-expand-array dag-parent-array-name dag-parent-array index)))
  :hints (("subgoal *1/4" :cases ((< new-len (alen1 dag-parent-array-name dag-parent-array))))
          ("subgoal *1/3" :cases ((< new-len (alen1 dag-parent-array-name dag-parent-array))))
          ("Goal" ;:cases ((natp n))
           :induct (all-dag-parent-entriesp new-len
                                    dag-parent-array-name
                                    (maybe-expand-array dag-parent-array-name dag-parent-array index))
           :in-theory (enable all-dag-parent-entriesp))))

;nested induction
;todo: replace the no-gen one
(defthm all-dag-parent-entriesp-of-maybe-expand-array-gen
  (implies (and (array1p dag-parent-array-name dag-parent-array)
                (natp index)
                (<= index 2147483645))
           (equal (all-dag-parent-entriesp n dag-parent-array-name (maybe-expand-array dag-parent-array-name dag-parent-array index))
                  (all-dag-parent-entriesp n dag-parent-array-name dag-parent-array)))
  :hints (("Goal" ;:cases ((natp n))
           :induct (all-dag-parent-entriesp new-len
                                            dag-parent-array-name
                                            (maybe-expand-array dag-parent-array-name dag-parent-array index))
           :in-theory (enable all-dag-parent-entriesp))))

;;;
;;; dag-parent-arrayp
;;;

;; Check for a well-formed dag-parent-array.  A dag-parent-array maps nodenums
;; in the dag to lists of parent nodenums (in the dag). The size of the
;; dag-parent-array is kept in sync with the dag-array.  The dag-parent-array
;; maps all nodes that are valid (< dag-len) to the list of the nodenums of
;; their parents.  The other elements in the dag-parent-array are unassigned
;; and so essentially contain the default value of nil (so that when we add a
;; node, its parents are correct without us having to do anything).
(defund dag-parent-arrayp (dag-parent-array-name dag-parent-array)
  (declare (xargs :guard t))
  (and (array1p dag-parent-array-name dag-parent-array)
       (equal (default dag-parent-array-name dag-parent-array) nil)
       (all-dag-parent-entriesp (+ -1 (alen1 dag-parent-array-name dag-parent-array))
                                dag-parent-array-name
                                dag-parent-array)))

(defthm default-when-dag-parent-arrayp
  (implies (dag-parent-arrayp dag-parent-array-name dag-parent-array)
           (equal (default dag-parent-array-name dag-parent-array)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp))))

;; ;gen to "when array1p"?
;; (defthm <-of-car-and-alen1-when-dag-parent-arrayp
;;   (implies (dag-parent-arrayp dag-parent-array-name dag-parent-array (largest-non-quotep items))
;;            (< (car items) (alen1 dag-parent-array-name dag-parent-array)))
;;   :hints (("Goal" :in-theory (enable dag-parent-arrayp largest-non-quotep))))

(defthm consp-of-dimensions-when-dag-parent-arrayp-cheap
  (implies (dag-parent-arrayp dag-parent-array-name dag-parent-array)
           (consp (dimensions dag-parent-array-name dag-parent-array)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp))))

(defthm dag-parent-arrayp-forward-to-array1p
  (implies (dag-parent-arrayp dag-parent-array-name dag-parent-array)
           (array1p dag-parent-array-name dag-parent-array))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp)))
  :rule-classes :forward-chaining)

;; (defthm dag-parent-arrayp-monotone
;;   (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array len1)
;;                 (<= len2 len1)
;;                 (integerp len1)
;;                 (integerp len2)
;;                 (<= -1 len2)
;;                 )
;;            (dag-parent-arrayp dag-parent-array-name dag-parent-array len2))
;;   :hints (("Goal" :in-theory (enable dag-parent-arrayp))))

(defthm dag-parent-arrayp-of-make-empty-array
  (implies (and (posp size)
                (<= size 2147483646)
                (symbolp dag-parent-array-name))
           (dag-parent-arrayp dag-parent-array-name (make-empty-array dag-parent-array-name size)))
  :hints (("Goal" :in-theory (enable dag-parent-arrayp))))

(defthm dag-parent-arrayp-of-aset1
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp n)
                (< n (alen1 dag-parent-array-name dag-parent-array))
                (all-> val n)
                (nat-listp val))
           (dag-parent-arrayp dag-parent-array-name (aset1 dag-parent-array-name dag-parent-array n val)))
  :hints (("Goal" :in-theory (enable DAG-PARENT-ARRAYP))))

(defthm true-listp-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                ;(< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (true-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :cases ((< n (alen1 dag-parent-array-name dag-parent-array)))
           :in-theory (enable dag-parent-arrayp))))

(defthm nat-listp-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
       ;         (< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (nat-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :cases ((< n (alen1 dag-parent-array-name dag-parent-array)))
           :in-theory (enable dag-parent-arrayp))))

(defthm all-natp-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp n))
           (all-natp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :use (:instance nat-listp-of-aref1-when-dag-parent-arrayp)
           :in-theory (disable nat-listp-of-aref1-when-dag-parent-arrayp))))

(defthm integer-listp-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                ;(< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (integer-listp (aref1 dag-parent-array-name dag-parent-array n)))
  :hints (("Goal" :cases ((< n (alen1 dag-parent-array-name dag-parent-array)))
           :in-theory (enable dag-parent-arrayp))))

(defthm all->-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                ;(< n (alen1 dag-parent-array-name dag-parent-array))
                (natp n))
           (all-> (aref1 dag-parent-array-name dag-parent-array n) n))
  :hints (("Goal" :cases ((< n (alen1 dag-parent-array-name dag-parent-array)))
           :in-theory (enable dag-parent-arrayp))))

(defthm dag-parent-arrayp-of-maybe-expand-array
  (implies (and; (<= (+ -1 (alen1 dag-parent-array-name dag-parent-array)) index)
                (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                (natp index)
                (<= index 2147483645))
           (dag-parent-arrayp dag-parent-array-name (maybe-expand-array dag-parent-array-name dag-parent-array index)))
  :hints (("Goal" :in-theory (e/d (dag-parent-arrayp) (all-dag-parent-entriesp-of-maybe-expand-array-gen)))))

(defthm <-of-maxelem-of-aref1-when-dag-parent-arrayp
  (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array)
                ;;(< n (alen1 dag-parent-array-name dag-parent-array))
                (consp (aref1 dag-parent-array-name dag-parent-array n))
                (natp n))
           (< n (maxelem (aref1 dag-parent-array-name dag-parent-array n))))
  :hints (("Goal" :use (:instance all->-of-aref1-when-dag-parent-arrayp)
           :in-theory (disable all->-of-aref1-when-dag-parent-arrayp))))

;; (defthm all-<-of-aref1-when-dag-parent-arrayp
;;   (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array top-nodenum-to-check)
;;                 (<= n top-nodenum-to-check)
;;                 (natp n))
;;            (all-< (aref1 dag-parent-array-name dag-parent-array n) top-nodenum-to-check))
;;   :hints (("Goal" :in-theory (enable dag-parent-arrayp))))

;; (defthm all-<-of-aref1-when-dag-parent-arrayp-and-alen1
;;   (implies (and (dag-parent-arrayp dag-parent-array-name dag-parent-array top-nodenum-to-check)
;;                 (<= n top-nodenum-to-check)
;;                 (natp n))
;;            (all-< (aref1 dag-parent-array-name dag-parent-array n) (alen1 dag-parent-array-name dag-parent-array)))
;;   :hints (("Goal" :in-theory (enable dag-parent-arrayp))))
