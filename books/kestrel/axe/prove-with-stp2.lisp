; Calling STP to prove things about DAGs and terms
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

; These functions are only used by the equivalence-checker.  They notably each take a var-type-alist.

(include-book "depth-array")
(include-book "translate-dag-to-stp") ; has ttags, for add-assert-if-a-mult (move that here?)
(include-book "type-inference") ; for maybe-get-type-of-function-call, reduce?
;(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "supporting-nodes") ;for tag-nodenums-with-name
(include-book "supporting-vars") ; for vars-that-support-dag-node
(include-book "kestrel/typed-lists-light/decreasingp" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-lists" :dir :system))
(local (include-book "kestrel/typed-lists-light/decreasingp" :dir :system))
(local (include-book "kestrel/utilities/make-ord" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/bv-lists/bv-arrays" :dir :system))
(local (include-book "kestrel/bv/bvlt" :dir :system))

(local (in-theory (enable rationalp-when-natp)))

;move, dup
(local
 (defthm nat-listp-of-reverse-list
  (equal (nat-listp (reverse-list x))
         (all-natp x))
  :hints (("Goal" :in-theory (enable nat-listp reverse-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund integer-average-round-up (x y)
  (declare (xargs :guard (and (integerp x)
                              (integerp y))))
  (ceiling (/ (+ x y) 2) 1))

(local
  (defthm <=-of-integer-average-round-up-1
    (implies (and (<= x y)
                  (natp x)
                  (natp y))
             (<= (integer-average-round-up x y) y))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable integer-average-round-up)))))

(local
  (defthm <=-of-integer-average-round-up-2
    (implies (and (<= x y)
                  (natp x)
                  (natp y))
             (<= x (integer-average-round-up x y)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable integer-average-round-up)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a string-tree that extends extra-asserts.
;; todo: should we use this more?
;fixme rectify this printing with the other use of this function
;todo: pass in the ffn-symb (maybe) and the dargs
;todo: don't throw an error (via get-type-of-arg-during-cutting) if the args are not good.
(defund add-assert-if-a-mult (n expr dag-array-name dag-array var-type-alist print extra-asserts)
  (declare (xargs :guard (and (natp n)
                              (bounded-dag-exprp n expr)
                              (dag-function-call-exprp expr)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n))
                              (var-type-alistp var-type-alist)
                              (string-treep extra-asserts))
                  :guard-hints (("Goal" :in-theory (enable bounded-dag-exprp car-becomes-nth-of-0
                                                           not-<-of-nth-when-bounded-darg-listp-gen
                                                           darg-quoted-posp)))))
  (make-string-tree (and (eq 'bvmult (ffn-symb expr))
                         (= 3 (len (dargs expr)))
                         (darg-quoted-posp (darg1 expr))
                         (let ((arg2-type (get-type-of-arg-during-cutting (darg2 expr) dag-array-name dag-array var-type-alist))
                               (arg3-type (get-type-of-arg-during-cutting (darg3 expr) dag-array-name dag-array var-type-alist)))
                           (and (bv-typep arg2-type)
                                (bv-typep arg3-type)
                                ;; The sum of the widths of the arguments must be <= the width of the product for the extra assert to be helpful:
                                (let ((arg2-width (bv-type-width arg2-type))
                                      (arg3-width (bv-type-width arg3-type)))
                                  (and (<= (+ arg2-width arg3-width)
                                           (unquote (darg1 expr)))
                                       (let ((max-product-value (* (+ -1 (expt 2 arg2-width))
                                                                   (+ -1 (expt 2 arg3-width)))))
                                         (prog2$ (and print (cw ", which is a BVMULT: ~x0" expr))
                                                 (list* "ASSERT(BVLE("
                                                        (make-node-var n)
                                                        ","
                                                        (translate-bv-constant max-product-value (unquote (darg1 expr)))
                                                        "));"
                                                        (newline-string)))))))))
                    extra-asserts))

(defthm string-treep-of-add-assert-if-a-mult
  (implies (string-treep extra-asserts)
           (string-treep (add-assert-if-a-mult n expr dag-array-name dag-array var-type-alist print extra-asserts)))
  :hints (("Goal" :in-theory (enable add-assert-if-a-mult))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This assumes the miter is pure. -- or just the relevant nodes??
;; Only used for pure probably-constant nodes.
;;only used for probably-constant nodes
;;only cuts at variables
;FIXME can we clean this up?
;; Returns (mv erp nodenums-to-translate cut-nodenum-type-alist) where NODENUMS-TO-TRANSLATE is in decreasing order.
;; TODO: implement increasingly aggressive cuts?
; TODO: Consider using a worklist.
;todo: compare to gather-nodes-to-translate-up-to-depth
;todo: generate extra asserts for bvmults?
(defund gather-nodes-for-translation (n ;counts down and stops at -1
                                      dag-array-name dag-array dag-len ; dag-len is only used for the guard
                                      var-type-alist
                                      needed-for-node1-tag-array ; todo: rename this array, since there is only one node
                                      nodenums-to-translate-acc ;gets extended, in increasing order
                                      cut-nodenum-type-alist ; an accumulator, gets extended
                                      )
  (declare (xargs :guard (and (integerp n)
                              (<= -1 n)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< n dag-len)
                              (var-type-alistp var-type-alist)
                              (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                              (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                              (nat-listp nodenums-to-translate-acc)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :measure (nfix (+ 1 n))))
  (if (not (natp n))
      (mv (erp-nil) (reverse-list nodenums-to-translate-acc) cut-nodenum-type-alist)
    (mv-let (erp needed-for-node1-tag-array nodenums-to-translate-acc cut-nodenum-type-alist)
      (if (not (aref1 'needed-for-node1-tag-array needed-for-node1-tag-array n))
          ;; this node is not needed, so skip it:
          (mv (erp-nil) needed-for-node1-tag-array nodenums-to-translate-acc cut-nodenum-type-alist)
        (let ((expr (aref1 dag-array-name dag-array n)))
          (if (variablep expr)
              ;; variable; we'll cut:
              (let ((type (lookup-eq expr var-type-alist)))
                (if (not type)
                    (prog2$ (er hard? 'gather-nodes-for-translation "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist)
                            (mv :type-error nil nil nil))
                  (mv (erp-nil) needed-for-node1-tag-array nodenums-to-translate-acc (acons-fast n type cut-nodenum-type-alist))))
            (if (fquotep expr)
                ;; constant; we'll translate it:
                (mv (erp-nil) needed-for-node1-tag-array (cons n nodenums-to-translate-acc) cut-nodenum-type-alist)
              ;; function call (we'll translate it and mark its children as being needed):
              ;; todo: consider cutting!
              (mv (erp-nil)
                  (tag-nodenums-with-name (dargs expr) 'needed-for-node1-tag-array needed-for-node1-tag-array)
                  (cons n nodenums-to-translate-acc)
                  cut-nodenum-type-alist)))))
      (if erp
          (mv erp nil nil)
        (gather-nodes-for-translation (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate-acc cut-nodenum-type-alist)))))

(local
  (defthm gather-nodes-for-translation-return-type-1
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (< n dag-len)
                  (var-type-alistp var-type-alist)
                  (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                  (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (no-nodes-are-variablesp nodenums-to-translate dag-array-name dag-array dag-len)
                  (all-< nodenums-to-translate dag-len))
             (and (nat-listp (mv-nth 1 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist)))
                  (no-nodes-are-variablesp (mv-nth 1 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist))
                                           dag-array-name dag-array dag-len)
                  (all-< (mv-nth 1 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist))
                         dag-len)))
    :hints (("Goal" :in-theory (enable gather-nodes-for-translation)))))

(local
  (defthm gather-nodes-for-translation-return-type-2
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (< n dag-len)
                  (var-type-alistp var-type-alist)
                  (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                  (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (all-< (strip-cars cut-nodenum-type-alist)
                         dag-len))
             (and (nodenum-type-alistp (mv-nth 2 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist)))
                  (all-< (strip-cars (mv-nth 2 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist)))
                         dag-len)))
    :hints (("Goal" :in-theory (enable gather-nodes-for-translation)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This currently does no cutting.  Assumes the node is pure.
;; Returns (mv result state) where result is :error, :valid, :invalid, :timedout, (:counterexample <counterexample>), or (:possible-counterexample <counterexample>).
(defund prove-node-is-constant-with-stp (nodenum
                                         constant-value
                                         dag-array-name dag-array dag-len
                                         var-type-alist
                                         print
                                         max-conflicts
                                         proof-name
                                         state)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len)
                              ;; constant-value can be any pure value?
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (or (null max-conflicts) (natp max-conflicts))
                              (symbolp proof-name))
                  :stobjs state))
  (b* ((needed-for-node1-tag-array (make-empty-array 'needed-for-node1-tag-array (+ 1 nodenum))) ; todo: rename the array
       (needed-for-node1-tag-array (aset1 'needed-for-node1-tag-array needed-for-node1-tag-array nodenum t))
       ;; Choose which nodes to translate (no cutting):
       ((mv erp nodenums-to-translate cut-nodenum-type-alist)
        (gather-nodes-for-translation nodenum dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nil nil))
       ((when (not (consp nodenums-to-translate))) ; todo: can this happen?  should this be an error or a failure? can the node be a constant node?  a var?
        (cw "ERROR: No nodes to translate.")
        (mv *error* state))
       ((when erp)
        (mv *error* state)) ; or pass back this error?
       ;; Call STP on the proof obligation without replacement:
       ((mv result state)
        (prove-equality-with-stp (enquote constant-value)
                                 nodenum
                                 dag-array-name dag-array dag-len
                                 nodenums-to-translate
                                 (concatenate 'string (symbol-name proof-name) "-CONSTANT-" (nat-to-string nodenum))
                                 cut-nodenum-type-alist
                                 nil ;extra-asserts ;todo
                                 print
                                 max-conflicts
                                 nil ;no counterexample (for now)
                                 nil ; print-cex-as-signedp (irrelevant?)
                                 state)))
    (if (eq *error* result)
        (prog2$ (er hard? 'prove-node-is-constant-with-stp "Error calling STP.")
                (mv result state))
      (if (eq *valid* result)
          (prog2$ (cw "STP proved that node ~x0 is the constant ~x1.~%" nodenum constant-value)
                  (mv result state))
        ;; TODO: Use the counterexample if there is one.
        (prog2$
          (cw "STP FAILED to prove that node ~x0 is the constant ~x1.~%" nodenum constant-value)
          ;;fffixme return "timed out" if it did
          (mv result state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; No longer used (could make this an option)
;; This assumes the miter is pure.
;; Only used by the equivalence checker.
;fixme could use a worklist instead of walking the whole dag? perhaps merge the supporters lists for the two dags?
; cuts the proof at nodes that support both node1 and node2 and gathers for translation only the nodes above the cut that support node1 or node2
; walks down the DAG.
;if the node is not tagged as supporting either nodenum, we skip it, don't gather it for translation and don't do anything to its children.
;if the node supports both nodenum1 and nodenum2 we cut (refrain from gathering it for translation and generate an entry in cut-nodenum-type-alist).
;if the node supports just one of nodenum1 and nodenum2 then we gather the node itself for translation (unless its a var or constant) and tag its children as supporting that nodenum
;Returns (mv erp nodenums-to-translate ;sorted in decreasing order
;            cut-nodenum-type-alist ;now includes vars
;            extra-asserts ;can arise, e.g., from cutting out a BVMULT of two 4-bit values, where the maximum product is 15x15=225, not 255.
;            )
(defund gather-nodes-to-translate-for-aggressively-cut-proof (n ;counts down and stops at -1
                                                              dag-array-name dag-array dag-len
                                                              var-type-alist
                                                              needed-for-node1-tag-array ;initially only node1 is tagged (there are nodes that support node1 and are above the shared nodes)
                                                              needed-for-node2-tag-array ;initially only node2 is tagged (there are nodes that support node2 and are above the shared nodes)
                                                              nodenums-to-translate ;this is an accumulator sorted in increasing order
                                                              cut-nodenum-type-alist ; todo: make this an array?
                                                              extra-asserts ;an accumulator (a string-tree)
                                                              print)
  (declare (xargs :guard (and (integerp n)
                              (<= -1 n)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< n dag-len)
                              (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                              (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                              (array1p 'needed-for-node2-tag-array needed-for-node2-tag-array)
                              (< n (alen1 'needed-for-node2-tag-array needed-for-node2-tag-array))
                              (var-type-alistp var-type-alist)
                              (nat-listp nodenums-to-translate)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (string-treep extra-asserts)
                              (print-levelp print))
                  :measure (nfix (+ 1 n))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :split-types t)
           (type integer n) ; can't say unsigned-byte because -1 is possible
           )
  (if (or (not (mbt (integerp n)))
          (< n 0))
      (mv (erp-nil) (reverse-list nodenums-to-translate) cut-nodenum-type-alist extra-asserts)
    (let* ((needed-for-node1p (aref1 'needed-for-node1-tag-array needed-for-node1-tag-array n))
           (needed-for-node2p (aref1 'needed-for-node2-tag-array needed-for-node2-tag-array n)))
      (if (and (not needed-for-node1p)
               (not needed-for-node2p))
          ;; Node n is not needed for either node, so skip it:
          (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print)
        ;; Node n is needed for at least one of node1 and node2:
        ;;fixme move these tests down?  constants and variables are rare?
        (let ((expr (aref1 dag-array-name dag-array n)))
          (if (variablep expr)
              ;; if it's a variable, we will cut (the variable generated in STP will be named NODEXXX, so we don't have to worry about the actual name of expr clashing with something) and add info about its type to cut-nodenum-type-alist:
              (b* ((type (lookup-eq expr var-type-alist))
                   ((when (not type)) ; should not happen (var-type-alist should assign types to all vars in the dag)
                    (er hard? 'gather-nodes-to-translate-for-aggressively-cut-proof "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist) ; (cw "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist)
                    (mv :type-error nil nil extra-asserts)))
                (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array
                                                                      nodenums-to-translate ;not adding n
                                                                      (acons-fast n type cut-nodenum-type-alist)
                                                                      extra-asserts print))
            (if (fquotep expr)
                ;; it's a constant; we'll always translate it:
                ;; fixme can this happen?  or when we merge a node with a constant, does the value get changed in each parent?
                (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array
                                                                      (cons n nodenums-to-translate) ;translate it
                                                                      cut-nodenum-type-alist
                                                                      extra-asserts print)
              ;; expr must be a function call:
              (if needed-for-node1p
                  (if needed-for-node2p
                      ;; needed for both nodes; we'll cut here (refrain adding it to the list of nodenums to translate and add its type info to cut-nodenum-type-alist)
                      ;; note: before april 2010, this code always translated any bvnth (not sure why, and what about bv-array-read?)
                      (b* ((- (and print (cw "~%  (Cutting at shared node ~x0" n)))
                           (type (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)))
                           ((when (not (axe-typep type)))
                            (er hard? 'gather-nodes-for-translation "ERROR: Bad type for ~x0.~%" expr)
                            (mv :type-error nil nil extra-asserts))
                           ;;Special handling for BVMULT when the arguments
                           ;;are small.  Consider the product of two 4-bit
                           ;;values.  Since the max. 4-bit value is 15, the
                           ;;max product is 225.  This is smaller than 255!
                           ;;If we cut out the BVMULT, we lose this
                           ;;information.  So we add extra-asserts to the
                           ;;query to recapture it.  In particular, if the
                           ;;args have width m and n, then the maximum
                           ;;values for the product is: (2^m-1)*(2^n-1).
                           (extra-asserts (add-assert-if-a-mult n expr dag-array-name dag-array var-type-alist print extra-asserts))
                           (- (and print (cw ".)"))))
                        (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array
                                                                              nodenums-to-translate ;don't translate
                                                                              ;;fixme will expr always have a known type? ;;FIXME think about arrays here?
                                                                              (acons-fast n type cut-nodenum-type-alist)
                                                                              extra-asserts print))
                    ;;needed for node1 but not node2
                    ;; translate it and mark its children as being needed for node1
                    (gather-nodes-to-translate-for-aggressively-cut-proof
                      (+ -1 n) dag-array-name dag-array dag-len var-type-alist
                      (tag-nodenums-with-name (dargs expr) 'needed-for-node1-tag-array needed-for-node1-tag-array)
                      needed-for-node2-tag-array
                      (cons n nodenums-to-translate)
                      cut-nodenum-type-alist extra-asserts print))
                ;; needed for node2 but not node1
                ;; translate it and mark its children as being needed for node2
                (gather-nodes-to-translate-for-aggressively-cut-proof
                  (+ -1 n) dag-array-name dag-array dag-len var-type-alist
                  needed-for-node1-tag-array
                  (tag-nodenums-with-name (dargs expr) 'needed-for-node2-tag-array needed-for-node2-tag-array)
                  (cons n nodenums-to-translate)
                  cut-nodenum-type-alist extra-asserts print)))))))))

(local
  (defthm nat-listp-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (nat-listp nodenums-to-translate))
             (nat-listp (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

(local
  (defthm no-nodes-are-variablesp-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (nat-listp nodenums-to-translate)
                  (no-nodes-are-variablesp nodenums-to-translate
                                           dag-array-name dag-array dag-len))
             (no-nodes-are-variablesp (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))
                                      dag-array-name dag-array dag-len))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

;; ;drop?
;; (defthmd all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof
;;   (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (integerp n)
;;                 (<= -1 n)
;;                 (< n dag-len)
;;                 (nat-listp nodenums-to-translate)
;;                 (all-< nodenums-to-translate dag-len))
;;            (all-< (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n
;;                                                                                    dag-array-name
;;                                                                                    dag-array
;;                                                                                    dag-len
;;                                                                                    needed-for-node1-tag-array
;;                                                                                    needed-for-node2-tag-array
;;                                                                                    nodenums-to-translate
;;                                                                                    cut-nodenum-type-alist
;;                                                                                    extra-asserts
;;                                                                                    print var-type-alist))
;;                   dag-len))
;;   :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

(local
  (defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (< n dag-len)
                  (nat-listp nodenums-to-translate)
                  (all-< nodenums-to-translate bound)
                  (<= (+ 1 n) bound)
                  (all-< nodenums-to-translate dag-len))
             (all-< (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))
                    bound))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

(local
  (defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new-special
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (< n dag-len)
                  (nat-listp nodenums-to-translate)
                  (all-< nodenums-to-translate (+ 1 n))
                  (all-< nodenums-to-translate dag-len))
             (all-< (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))
                    (+ 1 n)))
    :hints (("Goal" :use (:instance all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new (bound (+ 1 n)))
             :in-theory (disable all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new)))))

;todo: may need the ability to return an error
(local
  (defthm nodenum-type-alistp-of-mv-nth-2-of-gather-nodes-to-translate-for-aggressively-cut-proof
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist))
             (nodenum-type-alistp (mv-nth 2 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-2-of-gather-nodes-to-translate-for-aggressively-cut-proof
    (implies (and (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (<= -1 n)
                  (< n dag-len)
                  (nat-listp nodenums-to-translate)
                  (all-< nodenums-to-translate dag-len))
             (all-< (strip-cars (mv-nth 2 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print)))
                    dag-len))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

(local
  (defthm string-treep-of-mv-nth-3-of-gather-nodes-to-translate-for-aggressively-cut-proof
    (implies (string-treep extra-asserts)
             (string-treep (mv-nth 3 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts print))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move up

(include-book "merge-sort-greater-than-and-remove-dups")

;dup
(local
 (defthmd not-equal-of-nth-0-and-nth-1-when-decreasingp
   (implies (and (decreasingp x)
                 (nat-listp x))
            (equal (equal (nth 0 x) (nth 1 x))
                   (not (consp x))))
   :hints (("Goal" :in-theory (enable decreasingp)))))

(local
 (defthm helper-fw
   (implies (< 0 (nth 0 x))
            (consp x))
   :rule-classes :forward-chaining))

(local
 (defthm rational-listp-when-nat-listp
   (implies (nat-listp x)
            (rational-listp x))))

(local
 (defthm all-rationalp-when-nat-listp
   (implies (nat-listp x)
            (all-rationalp x))
   :hints (("Goal" :in-theory (enable all-rationalp)))))

(local
 (defthmd decreasingp-forward-to-sortedp->=
   (implies (decreasingp x)
            (sortedp->= x))
   :hints (("Goal" :in-theory (enable decreasingp sortedp->=)))))

;nested induction
(local
 (defthmd decreasingp-forward-to-no-duplicatesp-equal
   (implies (decreasingp x)
            (no-duplicatesp-equal x))
   :hints (("Goal" :in-theory (enable decreasingp no-duplicatesp-equal)))))

(local
 (defthmd no-duplicatesp-equal-when-decreasingp
   (implies (decreasingp x)
            (no-duplicatesp-equal x))
   :hints (("Goal" :in-theory (enable decreasingp no-duplicatesp-equal)))))

(local
 (defthmd decreasingp-when-sortedp->=-helper
   (implies (and (sortedp->= x)
                 (no-duplicatesp-equal x)
                 (rational-listp x))
            (decreasingp x))
   :hints (("Goal" :in-theory (enable decreasingp sortedp->= no-duplicatesp-equal)))))

;nested induction
(local
 (defthmd decreasingp-when-sortedp->=
   (implies (and (sortedp->= x)
                 (rational-listp x))
            (equal (decreasingp x)
                   (no-duplicatesp-equal x)))
   :hints (("Goal" :in-theory (enable decreasingp sortedp->= no-duplicatesp-equal)))))

(local
 (defthm all-rationalp-when-rational-listp
   (implies (rational-listp x)
            (all-rationalp x))))

(defthm decreasingp-of-merge->-and-remove-dups
  (implies (and (decreasingp x)
                (decreasingp y)
                (rational-listp x)
                (rational-listp y)
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y))
           (decreasingp (merge->-and-remove-dups x y)))
  :hints (("Goal" :in-theory (enable decreasingp-when-sortedp->=))))

(defthm decreasingp-of-merge-sort->-and-remove-dups
  (implies (rational-listp x)
           (decreasingp (merge-sort->-and-remove-dups x)))
  :hints (("Goal" :in-theory (enable decreasingp-when-sortedp->=))))

;; A double-worklist algorithm.
;Returns (mv erp nodenums-to-translate ;sorted in increasing order
;            cut-nodenum-type-alist
;            extra-asserts ;can arise, e.g., from cutting out a BVMULT of two 4-bit values, where the maximum product is 15x15=225, not 255.
;            )
;; Assumes the DAG is pure
(defun gather-nodes-to-translate-for-aggressively-cut-proof2 (worklist1
                                                              worklist2
                                                              dag-array-name dag-array dag-len
                                                              var-type-alist
                                                              print
                                                              ;; accumulators:
                                                              nodenums-to-translate ;in increasing order
                                                              cut-nodenum-type-alist
                                                              extra-asserts)
  (declare (xargs :guard (and (nat-listp worklist1)
                              (decreasingp worklist1)
                              (nat-listp worklist2)
                              (decreasingp worklist2)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< worklist1 dag-len)
                              (all-< worklist2 dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print)
                              (nat-listp nodenums-to-translate) ; increasing
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (string-treep extra-asserts))
                  ;; :guard-debug t
                  :measure (if (consp worklist1)
                               (if (consp worklist2)
                                   (+ 1 (nfix (max (first worklist1) (first worklist2))))
                                 (+ 1 (nfix (first worklist1))))
                             (if (consp worklist2)
                                 (+ 1 (nfix (first worklist2)))
                               0))
                  :ruler-extenders :lambdas
                  :hints (("Goal" :in-theory (enable not-equal-of-nth-0-and-nth-1-when-decreasingp
                                                     <-OF-NTH-1-AND-NTH-0-WHEN-DECREASINGP
                                                     <-of-nth-when-all-<
                                                     car-becomes-nth-of-0
                                                     not-<-of-nth-0-and-nth-1-when-decreasingp
                                                     ALL-<-WHEN-<-OF-CAR-AND-DECREASINGP
                                                     ALL-<-OF-CDR-AND-NTH-0-WHEN-DECREASINGP
                                                     INTEGERP-WHEN-NATP
                                                     NOT-<-OF-NTH-AND-0-WHEN-ALL-NATP)))
                  :guard-hints (("Goal" :in-theory (enable no-duplicatesp-equal-when-decreasingp)))))
  (if (not (mbt (and (nat-listp worklist1)  ;; for termination
                     (decreasingp worklist1)
                     (nat-listp worklist2)
                     (decreasingp worklist2)
                     (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                     (all-< worklist1 dag-len)
                     (all-< worklist2 dag-len))))
      (mv :bad-input nodenums-to-translate cut-nodenum-type-alist extra-asserts)
    (let ((action (if (endp worklist1)
                      (if (endp worklist2)
                          ;; both worklists are empty, so we are done:
                          :done
                        ;; nodes remain in worklist2 only (todo: could call something faster here with a single worklist?)
                        :node2)
                    (if (endp worklist2)
                        :node1 ;; nodes are left in worklist1 only (todo: could call something faster here with a single worklist?)
                      ;; nodes are present in both worklists:
                      (let ((node1 (the (unsigned-byte 60) (first worklist1)))
                            (node2 (the (unsigned-byte 60) (first worklist2))))
                        (if (= node1 node2)
                            :skip ; found a shared node, so do not explore it (unless it's a constant)
                          ;; the nodes differ, so we process whichever node is greater:
                          (if (> node1 node2)
                              ;; We'll process node1:
                              :node1
                            ;; We'll process node2:
                            :node2)))))))
      (if (eq :done action)
          (mv (erp-nil) nodenums-to-translate cut-nodenum-type-alist extra-asserts)
        (if (eq :skip action)
            ;; shared node:
            (b* ((node (the (unsigned-byte 60) (first worklist1))) ; could use either nodenum here since they are equal
                 (- (and print (cw "~%  (Cutting at shared node ~x0" node)))
                 (expr (aref1 dag-array-name dag-array node)))
              (if (variablep expr)
                  (b* ((type (lookup-eq expr var-type-alist))
                       ((when (not type)) ; todo: should not happen (var-type-alist should assign types to all vars in the dag)
                        (cw "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist)
                        (mv :type-error nil nil extra-asserts)))
                      ;; Remove node from both lists and continue:
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 (rest worklist1) (rest worklist2)
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           nodenums-to-translate ; not adding node
                                                                           (acons-fast node type cut-nodenum-type-alist) ; we cut
                                                                           extra-asserts))
                (if (fquotep expr)
                    ;; always translate a constant, even if shared:
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 (rest worklist1) (rest worklist2) ; remove from both lists
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           (cons node nodenums-to-translate) ; translate it
                                                                           cut-nodenum-type-alist ; don't cut
                                                                           extra-asserts)
                  ;; it's a function call, so cut:
                  (b* ((type (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)))
                       ((when (not (axe-typep type)))
                        (cw "ERROR: Bad type for ~x0.~%" expr)
                        (mv :type-error nodenums-to-translate cut-nodenum-type-alist extra-asserts))
                       ;;Special handling for BVMULT when the arguments
                       ;;are small.  Consider the product of two 4-bit
                       ;;values.  Since the max. 4-bit value is 15, the
                       ;;max product is 225.  This is smaller than 255!
                       ;;If we cut out the BVMULT, we lose this
                       ;;information.  So we add extra-asserts to the
                       ;;query to recapture it.  In particular, if the
                       ;;args have width m and n, then the maximum
                       ;;values for the product is: (2^m-1)*(2^n-1).
                       (extra-asserts (add-assert-if-a-mult node expr dag-array-name dag-array var-type-alist print extra-asserts))
                       (- (and print (cw ".)"))))
                    ;; Remove both nodes and continue:
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 (rest worklist1) (rest worklist2)
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           nodenums-to-translate ; don't translate
                                                                           (acons node type cut-nodenum-type-alist) ; do cut
                                                                           extra-asserts)))))
          (if (eq :node1 action)
              (let* ((node1 (the (unsigned-byte 60) (first worklist1)))
                     (expr (aref1 dag-array-name dag-array node1)))
                (if (variablep expr)
                    ;; if it's a variable, we cut (the variable generated in STP will be named NODEXXX, so we don't have to worry about the actual name of expr clashing with something) and add info about its type to cut-nodenum-type-alist:
                    (b* ((type (lookup-eq expr var-type-alist))
                         ((when (not type)) ; todo: should not happen (var-type-alist should assign types to all vars in the dag)
                          (cw "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist)
                          (mv :type-error nil nil extra-asserts)))
                      ;; Remove node1 and continue:
                      (gather-nodes-to-translate-for-aggressively-cut-proof2 (rest worklist1) worklist2
                                                                             dag-array-name dag-array dag-len var-type-alist print
                                                                             nodenums-to-translate ; not adding node1
                                                                             (acons-fast node1 type cut-nodenum-type-alist) ; we cut
                                                                             extra-asserts))
                  (if (fquotep expr)
                      ;; it's a constant; we'll always translate it:
                      ;; todo: can this happen?  when we merge a node with a constant, does the value get changed in each parent?
                      (gather-nodes-to-translate-for-aggressively-cut-proof2 (rest worklist1) worklist2
                                                                             dag-array-name dag-array dag-len var-type-alist print
                                                                             (cons node1 nodenums-to-translate) ; translate it
                                                                             cut-nodenum-type-alist ; don't cut
                                                                             extra-asserts)
                    ;; expr must be a function call, and it's not a shared node, so we translate it (we should be able to because it is pure):
                    ;; We "expand" the node by adding its children to the worklist:
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 (merge->-and-remove-dups (merge-sort->-and-remove-dups (keep-nodenum-dargs (dargs expr))) (rest worklist1))
                                                                           worklist2
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           (cons node1 nodenums-to-translate) ; translate it
                                                                           cut-nodenum-type-alist ; don't cut
                                                                           extra-asserts))))
            ;; action is :node2:
            (let* ((node2 (the (unsigned-byte 60) (first worklist2)))
                   (expr (aref1 dag-array-name dag-array node2)))
              (if (variablep expr)
                  ;; if it's a variable, we cut (the variable generated in STP will be named NODEXXX, so we don't have to worry about the actual name of expr clashing with something) and add info about its type to cut-nodenum-type-alist:
                  (b* ((type (lookup-eq expr var-type-alist))
                       ((when (not type)) ; todo: should not happen (var-type-alist should assign types to all vars in the dag)
                        (cw "ERROR: No type for ~x0 in alist ~x1.~%" expr var-type-alist)
                        (mv :type-error nil nil extra-asserts)))
                    ;; Remove node2 and continue:
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1 (rest worklist2)
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           nodenums-to-translate ; not adding node2
                                                                           (acons-fast node2 type cut-nodenum-type-alist) ; we cut
                                                                           extra-asserts))
                (if (fquotep expr)
                    ;; it's a constant; we'll always translate it:
                    ;; todo: can this happen?  when we merge a node with a constant, does the value get changed in each parent?
                    (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1 (rest worklist2)
                                                                           dag-array-name dag-array dag-len var-type-alist print
                                                                           (cons node2 nodenums-to-translate) ; translate it
                                                                           cut-nodenum-type-alist ; don't cut
                                                                           extra-asserts)
                  ;; expr must be a function call, and it's not a shared node, so we translate it (we should be able to because it is pure):
                  ;; We "expand" the node by adding its children to the worklist:
                  (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                         (merge->-and-remove-dups (merge-sort->-and-remove-dups (keep-nodenum-dargs (dargs expr))) (rest worklist2))
                                                                         dag-array-name dag-array dag-len var-type-alist print
                                                                         (cons node2 nodenums-to-translate) ; translate it
                                                                         cut-nodenum-type-alist ; don't cut
                                                                         extra-asserts))))))))))

(local
 (defthm gather-nodes-to-translate-for-aggressively-cut-proof2-return-type
   (implies (and (nat-listp worklist1)
;               (decreasingp worklist1)
                 (nat-listp worklist2)
 ;              (decreasingp worklist2)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (all-< worklist1 dag-len)
                 (all-< worklist2 dag-len)
                 (var-type-alistp var-type-alist)
                 (print-levelp print)
                 (nat-listp nodenums-to-translate) ; increasing
                 (nodenum-type-alistp cut-nodenum-type-alist)
                 (string-treep extra-asserts)
                 (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                 (all-< nodenums-to-translate dag-len)
                 (no-nodes-are-variablesp nodenums-to-translate
                                          dag-array-name dag-array dag-len))
            (and (nat-listp (mv-nth 1
                                    (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                           worklist2
                                                                                           dag-array-name dag-array dag-len
                                                                                           var-type-alist
                                                                                           print
                                                                                   ;; accumulators:
                                                                                           nodenums-to-translate ;in increasing order
                                                                                           cut-nodenum-type-alist
                                                                                           extra-asserts)))
                 (all-< (mv-nth 1
                                (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                       worklist2
                                                                                       dag-array-name dag-array dag-len
                                                                                       var-type-alist
                                                                                       print
                                                                                   ;; accumulators:
                                                                                       nodenums-to-translate ;in increasing order
                                                                                       cut-nodenum-type-alist
                                                                                       extra-asserts))
                        dag-len)
                 (no-nodes-are-variablesp (mv-nth 1
                                                  (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                                         worklist2
                                                                                                         dag-array-name dag-array dag-len
                                                                                                         var-type-alist
                                                                                                         print
                                                                                   ;; accumulators:
                                                                                                         nodenums-to-translate ;in increasing order
                                                                                                         cut-nodenum-type-alist
                                                                                                         extra-asserts))
                                          dag-array-name dag-array dag-len)
                 (nodenum-type-alistp (mv-nth 2
                                              (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                                     worklist2
                                                                                                     dag-array-name dag-array dag-len
                                                                                                     var-type-alist
                                                                                                     print
                                                                                   ;; accumulators:
                                                                                                     nodenums-to-translate ;in increasing order
                                                                                                     cut-nodenum-type-alist
                                                                                                     extra-asserts)))
                 (string-treep (mv-nth 3
                                       (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                              worklist2
                                                                                              dag-array-name dag-array dag-len
                                                                                              var-type-alist
                                                                                              print
                                                                                   ;; accumulators:
                                                                                              nodenums-to-translate ;in increasing order
                                                                                              cut-nodenum-type-alist
                                                                                              extra-asserts)))))
   :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof2)))))

(local
 (defthm all-<-of-strip-cars-of-mv-nth-2-of-gather-nodes-to-translate-for-aggressively-cut-proof2
   (implies (and (nat-listp worklist1)
;               (decreasingp worklist1)
                 (nat-listp worklist2)
 ;              (decreasingp worklist2)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (all-< worklist1 dag-len)
                 (all-< worklist2 dag-len)
                 (var-type-alistp var-type-alist)
                 (print-levelp print)
                 (nat-listp nodenums-to-translate) ; increasing
                 (nodenum-type-alistp cut-nodenum-type-alist)
;               (string-treep extra-asserts)
                 (all-< (strip-cars cut-nodenum-type-alist) dag-len))
            (all-< (strip-cars (mv-nth 2
                                       (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                              worklist2
                                                                                              dag-array-name dag-array dag-len
                                                                                              var-type-alist
                                                                                              print
                                                                                   ;; accumulators:
                                                                                              nodenums-to-translate ;in increasing order
                                                                                              cut-nodenum-type-alist
                                                                                              extra-asserts)))
                   dag-len))
   :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof2)))))

(local
 (defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof2
   (implies (and (nat-listp worklist1)
                 (decreasingp worklist1)
                 (nat-listp worklist2)
                 (decreasingp worklist2)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (all-< worklist1 dag-len)
                 (all-< worklist2 dag-len)
                 (var-type-alistp var-type-alist)
                 (print-levelp print)
                 (nat-listp nodenums-to-translate) ; increasing
                 (nodenum-type-alistp cut-nodenum-type-alist)
;               (string-treep extra-asserts)
                 (all-< nodenums-to-translate bound)
                 (all-< worklist1 bound)
                 (all-< worklist2 bound)
                ;; (implies (consp worklist1) (< (car worklist1) bound))
                ;; (implies (consp worklist2) (< (car worklist2) bound))
                 (integerp bound) ; why?
                 )
            (all-< (mv-nth 1
                           (gather-nodes-to-translate-for-aggressively-cut-proof2 worklist1
                                                                                  worklist2
                                                                                  dag-array-name dag-array dag-len
                                                                                  var-type-alist
                                                                                  print
                                                                                   ;; accumulators:
                                                                                  nodenums-to-translate ;in increasing order
                                                                                  cut-nodenum-type-alist
                                                                                  extra-asserts))
                   bound))
   :hints (("Goal" :induct t
            :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof2
                               car-becomes-nth-of-0
                               <-of-nth-when-all-<
                              ;; not-equal-of-nth-0-and-nth-1-when-decreasingp
                              ;; <-of-nth-1-and-nth-0-when-decreasingp
                              ;; not-<-of-nth-0-and-nth-1-when-decreasingp
                              ;; all-<-when-<-of-car-and-decreasingp
                              ;; all-<-of-cdr-and-nth-0-when-decreasingp
                              ;; integerp-when-natp
                              ;; not-<-of-nth-and-0-when-all-natp
                               )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Tries to prove that smaller-nodenum equals larger-nodenum, but replaces some (all?) shared supporting nodes by variables (and so proves a more general goal).
;If this succeeds, the nodes are equal.  If this fails, they may still be equal, because the failure might be due to the cutting.
;returns (mv erp provedp
;            nodenums-translated ;;in decreasing order
;            state)
;; Assumes that smaller-nodenum and larger-nodenum are pure.
(defund try-aggressively-cut-equivalence-proof (smaller-nodenum
                                                larger-nodenum
                                                dag-array-name
                                                dag-array ;this is the miter-array
                                                dag-len
                                                var-type-alist ;gives types to the variables in the dag (are these really needed? maybe not if we use induced types?)
                                                print max-conflicts proof-name
                                                state)
  (declare (xargs :guard (and (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (<= smaller-nodenum larger-nodenum) ; is equal possible?
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< smaller-nodenum dag-len)
                              (< larger-nodenum dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print) ; tighter?
                              (or (null max-conflicts) (natp max-conflicts))
                              (symbolp proof-name))
                  :guard-hints (("Goal" :in-theory (e/d (true-listp-when-nat-listp-rewrite) (reverse))))
                  :stobjs state))
  (b* ((- (and print (cw " (Cutting at shared nodes...")))
       ;; (num-nodes-to-consider (+ 1 larger-nodenum))
       ;;both of these arrays must have length at least (+ 1 larger-nodenum), since nodes up to larger-nodenum will be looked up?  could skip the array access for nodenums larger that smaller-nodenum (they obviously can't support it)
       ;; (needed-for-smaller-nodenum-tag-array (make-empty-array 'needed-for-node1-tag-array num-nodes-to-consider)) ;ffixme rename these arrays (but have to do it everywhere!)
       ;; (needed-for-smaller-nodenum-tag-array (aset1 'needed-for-node1-tag-array needed-for-smaller-nodenum-tag-array smaller-nodenum t))
       ;; (needed-for-larger-nodenum-tag-array (make-empty-array 'needed-for-node2-tag-array num-nodes-to-consider))
       ;; (needed-for-larger-nodenum-tag-array (aset1 'needed-for-node2-tag-array needed-for-larger-nodenum-tag-array larger-nodenum t))
       ;; Use our heuristic to cut the proof (nodes above the cut are marked for translation, nodes at the cut get entries made in cut-nodenum-type-alist):
       ((mv erp
            nodenums-to-translate ;in decreasing order
            cut-nodenum-type-alist extra-asserts)
         ; todo: consider a worklist algorithm for this:
        ;; (gather-nodes-to-translate-for-aggressively-cut-proof larger-nodenum ;skip everything above larger-nodenum
        ;;                                                       dag-array-name dag-array dag-len
        ;;                                                       var-type-alist
        ;;                                                       needed-for-smaller-nodenum-tag-array
        ;;                                                       needed-for-larger-nodenum-tag-array
        ;;                                                       nil ;nodenums-to-translate
        ;;                                                       nil ;cut-nodenum-type-alist ; todo: use an array for this, for speed?
        ;;                                                       nil ;extra-asserts
        ;;                                                       print)
        (gather-nodes-to-translate-for-aggressively-cut-proof2 (list larger-nodenum)
                                                               (list smaller-nodenum)
                                                               dag-array-name dag-array dag-len
                                                               var-type-alist
                                                               print
                                                               ;; accumulators:
                                                               nil nil nil))
       (nodenums-to-translate (reverse-list nodenums-to-translate))
       ((when erp)
        (cw "ERROR (~x0) in gathering nodes.~%" erp)
        (mv erp
            nil ; not proved
            nodenums-to-translate
            state))
       ((when (not (consp nodenums-to-translate))) ; can this happen?  two vars? two constants? a var and a constant?
        (cw "ERROR: No nodes to translate.")
        (mv :no-nodes-to-translate
            nil ; not proved
            nodenums-to-translate
            state))
       (- (and print (cw ")~%")))
       ;; Call STP:
       (- (and print ;(cw "Proving with STP...~%" nil)
               (cw "  ~x0 nodes to translate.~%" (len nodenums-to-translate))
               ))
       ((mv result state)
        (prove-equality-with-stp smaller-nodenum larger-nodenum dag-array-name dag-array dag-len
                                 nodenums-to-translate
                                 (n-string-append (symbol-name proof-name) ;use concatenate? ;todo: pass the proof-name as a string throughout?
                                                  "-"
                                                  (nat-to-string smaller-nodenum)
                                                  "="
                                                  (nat-to-string larger-nodenum))
                                 cut-nodenum-type-alist
                                 extra-asserts
                                 print
                                 max-conflicts
                                 nil ;no counterexample (for now)
                                 nil
                                 state)))
    (if (eq result *error*)
        (prog2$ (er hard? 'try-aggressively-cut-equivalence-proof "Error calling STP." nil)
                (mv :error-calling-stp
                    nil ;not proved
                    nodenums-to-translate
                    state))
      (prog2$ (and (eq result *timedout*) (cw "STP timed out.~%"))
              (mv (erp-nil)
                  (eq result *valid*) ;ttodo: user the counterexample, if present?
                  nodenums-to-translate
                  state)))))

(local
  (defthm nat-listp-of-mv-nth-2-of-try-aggressively-cut-equivalence-proof
    (implies (and (natp smaller-nodenum)
                  (natp larger-nodenum)
                  (<= smaller-nodenum larger-nodenum) ; is equal possible?
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< smaller-nodenum dag-len)
                  (< larger-nodenum dag-len)
                  (var-type-alistp var-type-alist)
                  (print-levelp print) ; tighter?
                  ;; (natp max-conflicts) ; allow nil?
                  (symbolp proof-name))
             (nat-listp (mv-nth 2 (try-aggressively-cut-equivalence-proof smaller-nodenum larger-nodenum dag-array-name dag-array dag-len var-type-alist print max-conflicts proof-name state))))
    :hints (("Goal" :in-theory (enable try-aggressively-cut-equivalence-proof)))))

(local
  (defthm all-<-of-mv-nth-2-of-try-aggressively-cut-equivalence-proof
    (implies (and (natp smaller-nodenum)
                  (natp larger-nodenum)
                  (<= smaller-nodenum larger-nodenum) ; is equal possible?
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< smaller-nodenum dag-len)
                  (< larger-nodenum dag-len)
                  (var-type-alistp var-type-alist)
                  (print-levelp print) ; tighter?
                  ;; (natp max-conflicts) ; allow nil?
                  (symbolp proof-name))
             (all-< (mv-nth 2 (try-aggressively-cut-equivalence-proof smaller-nodenum larger-nodenum dag-array-name dag-array dag-len var-type-alist print max-conflicts proof-name state))
                    (+ 1 larger-nodenum)))
    :hints (("Goal" :in-theory (enable try-aggressively-cut-equivalence-proof)))))

;; (defthm all-<-of-mv-nth-2-of-try-aggressively-cut-equivalence-proof-gen
;;   (implies (and (<= dag-len bound)
;;                 (natp smaller-nodenum)
;;                 (natp larger-nodenum)
;;                 (<= smaller-nodenum larger-nodenum) ; is equal possible?
;;                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (< smaller-nodenum dag-len)
;;                 (< larger-nodenum dag-len)
;;                 (var-type-alistp var-type-alist)
;;                 (print-levelp print) ; tighter?
;;                 ;; (natp max-conflicts) ; allow nil?
;;                 (symbolp proof-name))
;;            (all-< (mv-nth 2 (try-aggressively-cut-equivalence-proof smaller-nodenum larger-nodenum dag-array-name dag-array dag-len var-type-alist print max-conflicts proof-name state))
;;                   bound))
;;   :hints (("Goal" :use all-<-of-mv-nth-2-of-try-aggressively-cut-equivalence-proof
;;            :in-theory (disable all-<-of-mv-nth-2-of-try-aggressively-cut-equivalence-proof))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;TODO: Consider using a worklist algorithm.
;returns (mv erp nodenums-to-translate ;in decreasing order
;            cut-nodenum-type-alist
;            extra-asserts)
;where cut-nodenum-type-alist gives types for any new vars introduced at the cut
;we will translate nodes that are supporters and are above the cut
;; todo: do guards for functions like this cause expensive checks when we call them from :program mode code?
;; All nodes involved (everything tagged in the depth-array and supporters-tag-array) will be pure nodes.
;; Instead of returning errors,  suppose we could return most-general-type.
(defund gather-nodes-to-translate-up-to-depth (n ;counts down and stops at -1
                                               depth
                                               depth-array
                                               dag-array-name dag-array dag-len ; dag-len is only used for the guard
                                               var-type-alist
                                               supporters-tag-array ;bad name? todo: would the depth-array alone be sufficient (if it only has entries for supporters).  maybe this restricts us to supporters within the depth limit
                                               nodenums-to-translate ;an accumulator, in increasing order
                                               cut-nodenum-type-alist ;an accumulator
                                               extra-asserts ;an accumulator
                                               )
  (declare (xargs :guard (and (integerp n)
                              (<= -1 n)
                              (natp depth)
                              (depth-arrayp 'depth-array depth-array (+ 1 n))
                              (array1p 'depth-array depth-array)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< n dag-len)
                              (array1p 'supporters-tag-array supporters-tag-array)
                              (< n (alen1 'supporters-tag-array supporters-tag-array))
                              (nat-listp nodenums-to-translate)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (var-type-alistp var-type-alist)
                              (string-treep extra-asserts))
                  :measure (nfix (+ 1 n))))
  (if (not (natp n))
      (mv (erp-nil) (reverse-list nodenums-to-translate) cut-nodenum-type-alist extra-asserts)
    (let ((this-depth (aref1 'depth-array depth-array n))
          (supporterp (aref1 'supporters-tag-array supporters-tag-array n)))
      (if (or (not this-depth) ;node isn't needed anywhere is the dag (actually, doesn't support either node being merged?), so skip it
              (not supporterp)) ;fixme why both of these tests?
          (gather-nodes-to-translate-up-to-depth (+ -1 n) depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts)
        (let ((expr (aref1 dag-array-name dag-array n)))
          (if (variablep expr)
              ;;it's a variable.  we always cut:
              (b* ((type (lookup-eq expr var-type-alist))
                   ((when (not type)) ; should not happen (var-type-alist should assign types to all vars in the dag)
                    (cw "ERROR: No type, ~x0, for ~x1 in alist ~x2.~%" type expr var-type-alist)
                    (mv :type-error nil nil extra-asserts)))
                (gather-nodes-to-translate-up-to-depth (+ -1 n) depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array
                                                       nodenums-to-translate
                                                       (acons-fast n type cut-nodenum-type-alist)
                                                       extra-asserts))
            (if (fquotep expr)
                ;;it's a constant: we'll translate it:
                (gather-nodes-to-translate-up-to-depth (+ -1 n) depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array
                                                       (cons n nodenums-to-translate)
                                                       cut-nodenum-type-alist
                                                       extra-asserts)
              ;;expr is a function call.  check the depth to decide whether to translate or cut:
              (let ((translatep (and (<= this-depth depth)
                                     (not (eq 'bvmult (ffn-symb expr))) ;ffffixme new! instead, pass in a list of functions at which to always cut?))
                                     )))
                (if translatep
                    ;;translate it and mark its children (if any) as supporters
                    (gather-nodes-to-translate-up-to-depth (+ -1 n) depth depth-array dag-array-name dag-array dag-len var-type-alist
                                                           (tag-nodenums-with-name (dargs expr) 'supporters-tag-array supporters-tag-array)
                                                           (cons n nodenums-to-translate)
                                                           cut-nodenum-type-alist
                                                           extra-asserts)
                  ;;cut and make it a variable:
                  (let ((extra-asserts (add-assert-if-a-mult n expr dag-array-name dag-array var-type-alist
                                                             nil ;fixme print
                                                             extra-asserts)))
                    (b* ((type (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)))
                         ;; FIXME think about array nodes here
                         ;;fixme what if a hyp gives expr its width/type?
                         ;;do this in the other tagging function?
                         ;;fixme will expr always have a known type?
                         ((when (not (axe-typep type))) ; should not fail (all nodes should be pure)
                          (er hard? 'gather-nodes-to-translate-up-to-depth "ERROR: Bad type, ~x0, for ~x1.~%" type expr)
                          (mv :type-error nil nil extra-asserts)))
                      (gather-nodes-to-translate-up-to-depth (+ -1 n) depth depth-array dag-array-name dag-array dag-len var-type-alist
                                                             supporters-tag-array
                                                             nodenums-to-translate
                                                           (acons-fast n type cut-nodenum-type-alist)
                                                           extra-asserts))))))))))))

(local
  (defthm nat-listp-of-mv-nth-1-of-gather-nodes-to-translate-up-to-depth
    (implies (and (integerp n)
                  (<= -1 n)
                  (natp depth)
                  (depth-arrayp 'depth-array depth-array (+ 1 n))
                  (array1p 'depth-array depth-array)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< n dag-len)
                  (array1p 'supporters-tag-array supporters-tag-array)
                  (< n (alen1 'supporters-tag-array supporters-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist)
                  (string-treep extra-asserts))
             (nat-listp (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

(local
  (defthm no-nodes-are-variablesp-of-mv-nth-1-of-gather-nodes-to-translate-up-to-depth
    (implies (and (NO-NODES-ARE-VARIABLESP NODENUMS-TO-TRANSLATE DAG-ARRAY-NAME DAG-ARRAY DAG-LEN)
                  (integerp n)
                  (<= -1 n)
                  (natp depth)
                  (depth-arrayp 'depth-array depth-array (+ 1 n))
                  (array1p 'depth-array depth-array)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< n dag-len)
                  (array1p 'supporters-tag-array supporters-tag-array)
                  (< n (alen1 'supporters-tag-array supporters-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist)
                  (string-treep extra-asserts))
             (no-nodes-are-variablesp (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))
                                      dag-array-name dag-array dag-len))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

(local
  (defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-up-to-depth
    (implies (and (ALL-< NODENUMS-TO-TRANSLATE DAG-LEN)
                  (integerp n)
                  (<= -1 n)
                  (natp depth)
                  (depth-arrayp 'depth-array depth-array (+ 1 n))
                  (array1p 'depth-array depth-array)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< n dag-len)
                  (array1p 'supporters-tag-array supporters-tag-array)
                  (< n (alen1 'supporters-tag-array supporters-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist)
                  (string-treep extra-asserts))
             (all-< (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))
                    dag-len))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

;todo: may need the ability to return an error
(local
  (defthm nodenum-type-alistp-of-mv-nth-2-of-gather-nodes-to-translate-up-to-depth
    (implies (and (integerp n)
                  (<= -1 n)
                  (natp depth)
                  (depth-arrayp 'depth-array depth-array (+ 1 n))
                  (array1p 'depth-array depth-array)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< n dag-len)
                  (array1p 'supporters-tag-array supporters-tag-array)
                  (< n (alen1 'supporters-tag-array supporters-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist)
                  (string-treep extra-asserts))
             (nodenum-type-alistp (mv-nth 2 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

(local
  (defthm all-<-of-strip-cars-of-mv-nth-2-of-gather-nodes-to-translate-up-to-depth
    (implies (and (ALL-< (STRIP-CARS CUT-NODENUM-TYPE-ALIST) DAG-LEN)
                  (integerp n)
                  (<= -1 n)
                  (natp depth)
                  (depth-arrayp 'depth-array depth-array (+ 1 n))
                  (array1p 'depth-array depth-array)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (< n dag-len)
                  (array1p 'supporters-tag-array supporters-tag-array)
                  (< n (alen1 'supporters-tag-array supporters-tag-array))
                  (nat-listp nodenums-to-translate)
                  (nodenum-type-alistp cut-nodenum-type-alist)
                  (var-type-alistp var-type-alist)
                  (string-treep extra-asserts))
             (all-< (strip-cars (mv-nth 2 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts)))
                    dag-len))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

(local
  (defthm string-treep-of-mv-nth-3-of-gather-nodes-to-translate-up-to-depth
    (implies (string-treep extra-asserts)
             (string-treep (mv-nth 3 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
    :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;binary search to try to find a cut depth at which the goal is valid.
;would like to reuse this for pure constants
;; Returns (mv provedp state).
;; The two nodes must be pure nodes.
(defund try-cut-equivalence-proofs (min-depth
                                    max-depth
                                    depth-array ; depths wrt the set containing smaller-nodenum and larger-nodenum
                                    smaller-nodenum
                                    larger-nodenum
                                    dag-array-name dag-array dag-len
                                    var-type-alist print max-conflicts base-filename state)
  (declare (xargs :guard (and (natp min-depth)
                              (integerp max-depth) ; might go negative
                              (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (depth-arrayp 'depth-array depth-array (+ 1 larger-nodenum))
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (<= smaller-nodenum larger-nodenum)
                              (< larger-nodenum dag-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print) ; tighter?
                              (or (null max-conflicts) (natp max-conflicts))
                              (stringp base-filename))
                  :measure (nfix (+ 1 (- max-depth min-depth)))
                  :stobjs state))
  (if (or (not (and (mbt (natp min-depth))
                    (mbt (integerp max-depth))))
          (< max-depth min-depth))
      (prog2$ (cw "!! We failed to find a cut depth at which STP can prove the goal !!~%")
              (mv nil state))
    (b* (;; todo: drop this supporters-tag-array because the depth-array already tracks supporters (but consider what happens with cutting at bvmult and bvif nodes)
         (supporters-tag-array (make-empty-array 'supporters-tag-array (+ 1 larger-nodenum))) ;fixme drop this and have gather-nodes-to-translate-up-to-depth use a worklist?
         ;;mark the two nodes as supporters:
         (supporters-tag-array (aset1 'supporters-tag-array supporters-tag-array larger-nodenum t))
         (supporters-tag-array (aset1 'supporters-tag-array supporters-tag-array smaller-nodenum t))
         (current-depth (integer-average-round-up min-depth max-depth))
         ;; TODO: Consider a worklist algorithm:
         ((mv erp nodenums-to-translate cut-nodenum-type-alist extra-asserts)
          (gather-nodes-to-translate-up-to-depth larger-nodenum current-depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array
                                                 nil
                                                 nil ;initial cut-nodenum-type-alist
                                                 nil))
         ((when erp)
          (mv nil ; todo: or pass back the error?
              state))
         ((when (not (consp nodenums-to-translate))) ; can this happen?
          (cw "ERROR: No nodes to translate.")
          (mv ;; :no-nodes-to-translate
              nil ; not proved
              ;; nodenums-to-translate
              state))
         ;; Call STP:
         (- (and print (cw "Attempting STP proof at depth ~x0.~%" current-depth)))
         ((mv result state)
          (prove-equality-with-stp smaller-nodenum larger-nodenum
                                         dag-array-name dag-array dag-len
                                         nodenums-to-translate
                                         (string-append base-filename (nat-to-string current-depth))
                                         cut-nodenum-type-alist
                                         extra-asserts
                                         print
                                         max-conflicts
                                         nil ;no counterexample (for now)
                                         nil
                                         state))
         ((when (eq result *error*))
          (er hard? 'try-cut-equivalence-proofs "Error calling STP." nil)
          (mv nil ; did not prove it
              state)))
      (if (eq result *valid*)
          (mv t state) ; proved it
        (if (eq result *timedout*)
            ;;since the current depth timed out, we go shallower
            (try-cut-equivalence-proofs min-depth (+ -1 current-depth)
                                            depth-array smaller-nodenum larger-nodenum dag-array-name dag-array dag-len var-type-alist print max-conflicts base-filename state)
          ;;the goal was invalid, so we go deeper:
          ;;todo: use the counterexample?
          (try-cut-equivalence-proofs (+ 1 current-depth) max-depth
                                          depth-array smaller-nodenum larger-nodenum dag-array-name dag-array dag-len var-type-alist print max-conflicts base-filename state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;this one takes a list of array indices to check
;rename to remove the 2
(defun max-array-elem2 (indices current-max array-name array)
  (declare (xargs :guard (and (nat-listp indices)
                              (array1p array-name array)
                              (all-< indices (alen1 array-name array))
                              (rationalp current-max))))
  (if (endp indices)
      current-max
    (let* ((nodenum (first indices))
           (val (rfix (aref1 array-name array nodenum))) ; the rfix may not be needed in some cases
           )
      (max-array-elem2 (rest indices) (max current-max val) array-name array))))

(defthm natp-of-max-array-elem2-when-depth-arrayp
  (implies (and (nat-listp indices)
                (depth-arrayp array-name array num-valid-indices)
                (all-< indices num-valid-indices)
                (natp current-max))
           (natp (max-array-elem2 indices current-max array-name array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv provedp state).
;; TTODO: pass in assumptions (e.g., bvlt claims) - should we cut the assumptions too?
;; TODO: Return the counterexample, if any.
(defun try-to-prove-pure-nodes-equal-with-stp (smaller-nodenum
                                               larger-nodenum ; could one of these have been replaced by a constant?
                                               miter-array-name miter-array miter-len
                                               var-type-alist
                                               print max-conflicts proof-name state)
  (declare (xargs :guard (and (natp smaller-nodenum)
                              (natp larger-nodenum)
                              (<= smaller-nodenum larger-nodenum)
                              (pseudo-dag-arrayp miter-array-name miter-array miter-len)
                              (< smaller-nodenum miter-len)
                              (< larger-nodenum miter-len)
                              (var-type-alistp var-type-alist)
                              (print-levelp print) ; tighten?
                              (or (null max-conflicts) (natp max-conflicts))
                              (symbolp proof-name))
                  :guard-hints (("Goal"
                                 :use (:instance natp-of-max-array-elem2-when-depth-arrayp
                                                 (indices (MV-NTH 2
                                                                  (TRY-AGGRESSIVELY-CUT-EQUIVALENCE-PROOF
                                                                    SMALLER-NODENUM
                                                                    LARGER-NODENUM MITER-ARRAY-NAME
                                                                    MITER-ARRAY MITER-LEN VAR-TYPE-ALIST
                                                                    PRINT MAX-CONFLICTS PROOF-NAME STATE)))
                                                 (current-max 0)
                                                 (array-name 'DEPTH-ARRAY)
                                                 (array (MV-NTH 0
                                                                (MAKE-DEPTH-ARRAY-FOR-NODES (LIST SMALLER-NODENUM LARGER-NODENUM)
                                                                                            MITER-ARRAY-NAME
                                                                                            MITER-ARRAY MITER-LEN)))
                                                 (NUM-VALID-INDICES (+ 1 LARGER-NODENUM)))
                                 :in-theory (e/d (integerp-when-natp) (natp natp-of-max-array-elem2-when-depth-arrayp))))
                  :stobjs state))
  (b* ((- (cw "(Attempting aggressively cut proof:~%"))
       ;;first try with our proof-cutting heuristic (cuts at shared nodes):
       ;;fixme if we have contexts, how will we cut them (not clear what "shared nodes" means with 3 or more terms)?
       ;;probably best not to use contexts here, since this usually succeeds, and contexts are rarely needed
       ;;aggressive cut that replaces all shared nodes with variables:
       ((mv erp
            provedp
            nodenums-translated ;below we check these to determine the depth of the deepest translated node
            state)
        (try-aggressively-cut-equivalence-proof smaller-nodenum larger-nodenum miter-array-name miter-array miter-len var-type-alist print max-conflicts proof-name state))
       ;; todo: can the aggressively cut proof return a non-spurious counterexample?  if so, don't bother with the rest of this function
       ((when erp)
        (cw "  ERROR.)~%")
        (mv nil state)) ; todo: or pass back an error?
       (- (if provedp
              (cw "  Proved.)~%")
            (cw "  Failed.)~%")))
       ((when provedp) (mv t state))
       ;; The aggressively-cut proof did not work, so try to find a depth that does work:
       ((mv depth-array max-depth)
        (make-depth-array-for-nodes (list smaller-nodenum larger-nodenum) miter-array-name miter-array miter-len) ;todo: any way to avoid rebuilding this?
        )
       ;;deepest node translated when we tried our heuristic: (try-aggressively-cut-equivalence-proof could compute this if we pass it the depth array, but that might be expensive?
       (depth-of-deepest-translated-node (max-array-elem2 nodenums-translated
                                                          0 ;fixme think about the 0..
                                                          'depth-array depth-array))
       ;; todo: maybe the depths here should be measured from the shared-var frontier
       (- (cw "(Attempting cut proofs (min-depth ~x0, max-depth ~x1):~%" depth-of-deepest-translated-node max-depth))
       ((mv success-flg state)
        (try-cut-equivalence-proofs depth-of-deepest-translated-node ; we could add 1 here, but even without that we might get more nodes translated on the first attempt than were trasnalted above (e.g., shallow nodes on the shared node frontier)
                                    ;;(min max-depth ;(+ 1 (safe-min smaller-nodenum-depth larger-nodenum-depth)) ;starting depth (essentially depth 2; depth1 seems almost always useless to try)
                                    ;;                                                              starting-depth
                                    ;;                                                              )
                                    ;;                                                         ;; the min above prevents us form starting out over max depth
                                    max-depth
                                    depth-array
                                    smaller-nodenum
                                    larger-nodenum
                                    miter-array-name
                                    miter-array
                                    miter-len
                                    var-type-alist
                                    print max-conflicts
                                    (n-string-append (symbol-name proof-name)
                                                     "-"
                                                     (nat-to-string smaller-nodenum)
                                                     "="
                                                     (nat-to-string larger-nodenum)
                                                     "-depth-")
                                    state))
       (-  (cw ")")))
    (mv (if success-flg
            t
          (prog2$ (cw "!! STP failed to prove the equality of nodes ~x0 and ~x1. !!~%" smaller-nodenum larger-nodenum)
                  nil))
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
