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
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "supporting-nodes") ;for tag-nodenums-with-name
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
                              (symbol-alistp var-type-alist)
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
                                                              needed-for-node1-tag-array ;initially only node1 is tagged (there are nodes that support node1 and are above the shared nodes)
                                                              needed-for-node2-tag-array ;initially only node2 is tagged (there are nodes that support node2 and are above the shared nodes)
                                                              nodenums-to-translate ;this is an accumulator sorted in increasing order
                                                              cut-nodenum-type-alist ; todo: make this an array?
                                                              extra-asserts ;an accumulator (a string-tree)
                                                              print var-type-alist)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (integerp n)
                              (<= -1 n)
                              (< n dag-len)
                              (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                              (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                              (array1p 'needed-for-node2-tag-array needed-for-node2-tag-array)
                              (< n (alen1 'needed-for-node2-tag-array needed-for-node2-tag-array))
                              (symbol-alistp var-type-alist) ; the cdrs should be axe-types?
                              (nat-listp nodenums-to-translate)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (string-treep extra-asserts))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))))
  (if (not (natp n))
      (mv (erp-nil) (reverse-list nodenums-to-translate) cut-nodenum-type-alist extra-asserts)
    (let* ((needed-for-node1p (aref1 'needed-for-node1-tag-array needed-for-node1-tag-array n))
           (needed-for-node2p (aref1 'needed-for-node2-tag-array needed-for-node2-tag-array n)))
      (if (and (not needed-for-node1p)
               (not needed-for-node2p))
          ;; Node n is not needed for either node, so skip it:
          (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array nodenums-to-translate
                                                                cut-nodenum-type-alist extra-asserts print var-type-alist)
        ;; Node n is needed for at least one of node1 and node2:
        ;;fixme move these tests down?  constants and variables are rare?
        (let ((expr (aref1 dag-array-name dag-array n)))
          (if (variablep expr)
              ;; if it's a variable, we will cut (the variable generated in STP will be named NODEXXX, so we don't have to worry about the actual name of expr clashing with something) and add info about its type to cut-nodenum-type-alist:
              (b* ((type (lookup-eq-safe expr var-type-alist))
                   ((when (not (axe-typep type)))
                    (cw "ERROR: Bad type for ~x0 in alist ~x1.~%" expr var-type-alist)
                    (mv :type-error nil nil extra-asserts)))
                (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                      nodenums-to-translate ;not adding n
                                                                      (acons-fast n type cut-nodenum-type-alist)
                                                                      extra-asserts print var-type-alist))
            (if (fquotep expr)
                ;; it's a constant; we'll always translate it:
                ;; fixme can this happen?  or when we merge a node with a constant, does the value get changed in each parent?
                (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                      (cons n nodenums-to-translate) ;translate it
                                                                      cut-nodenum-type-alist
                                                                      extra-asserts print var-type-alist)
              ;; expr must be a function call:
              (if needed-for-node1p
                  (if needed-for-node2p
                      ;; needed for both nodes; we'll cut here (refrain adding it to the list of nodenums to translate and add its type info to cut-nodenum-type-alist)
                      ;; note: before april 2010, this code always translated any bvnth (not sure why, and what about bv-array-read?)
                      (b* ((- (and print (cw "~%  (Cutting at shared node ~x0" n)))
                           (type (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)))
                           ((when (not (axe-typep type)))
                            (cw "ERROR: Bad type for ~x0.~%" expr)
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
                        (gather-nodes-to-translate-for-aggressively-cut-proof (+ -1 n) dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                              nodenums-to-translate ;don't translate
                                                                              ;;fixme will expr always have a known type? ;;FIXME think about arrays here?
                                                                              (acons-fast n type cut-nodenum-type-alist)
                                                                              extra-asserts print var-type-alist))
                    ;;needed for node1 but not node2
                    ;; translate it and mark its children as being needed for node1
                    (gather-nodes-to-translate-for-aggressively-cut-proof
                      (+ -1 n) dag-array-name dag-array dag-len
                      (tag-nodenums-with-name (dargs expr) 'needed-for-node1-tag-array needed-for-node1-tag-array)
                      needed-for-node2-tag-array
                      (cons n nodenums-to-translate)
                      cut-nodenum-type-alist extra-asserts print var-type-alist))
                ;; needed for node2 but not node1
                ;; translate it and mark its children as being needed for node2
                (gather-nodes-to-translate-for-aggressively-cut-proof
                  (+ -1 n) dag-array-name dag-array dag-len
                  needed-for-node1-tag-array
                  (tag-nodenums-with-name (dargs expr) 'needed-for-node2-tag-array needed-for-node2-tag-array)
                  (cons n nodenums-to-translate)
                  cut-nodenum-type-alist extra-asserts print var-type-alist)))))))))

(defthm nat-listp-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (nat-listp nodenums-to-translate))
           (nat-listp (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                      nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

(defthm no-nodes-are-variablesp-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (nat-listp nodenums-to-translate)
                (no-nodes-are-variablesp nodenums-to-translate
                                         dag-array-name dag-array dag-len))
           (no-nodes-are-variablesp (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                                    nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))
                                    dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

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

(defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (< n dag-len)
                (nat-listp nodenums-to-translate)
                (all-< nodenums-to-translate bound)
                (<= (+ 1 n) bound)
                (all-< nodenums-to-translate dag-len))
           (all-< (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                  nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))
                  bound))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

(defthm all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new-special
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (< n dag-len)
                (nat-listp nodenums-to-translate)
                (all-< nodenums-to-translate (+ 1 n))
                (all-< nodenums-to-translate dag-len))
           (all-< (mv-nth 1 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                   nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))
                  (+ 1 n)))
  :hints (("Goal" :use (:instance all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new (bound (+ 1 n)))
           :in-theory (disable all-<-of-mv-nth-1-of-gather-nodes-to-translate-for-aggressively-cut-proof-new))))

;todo: may need the ability to return an error
(defthm nodenum-type-alistp-of-mv-nth-2-of-gather-nodes-to-translate-for-aggressively-cut-proof
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (nat-listp nodenums-to-translate)
                (nodenum-type-alistp cut-nodenum-type-alist))
           (nodenum-type-alistp (mv-nth 2 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                                nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

(defthm all-<-of-strip-cars-of-mv-nth-2-of-gather-nodes-to-translate-for-aggressively-cut-proof
  (implies (and (all-< (strip-cars cut-nodenum-type-alist) dag-len)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (< n dag-len)
                (nat-listp nodenums-to-translate)
                (all-< nodenums-to-translate dag-len))
           (all-< (strip-cars (mv-nth 2 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                              nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist)))
                  dag-len))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

(defthm string-treep-of-mv-nth-3-of-gather-nodes-to-translate-for-aggressively-cut-proof
  (implies (string-treep extra-asserts)
           (string-treep (mv-nth 3 (gather-nodes-to-translate-for-aggressively-cut-proof n dag-array-name dag-array dag-len needed-for-node1-tag-array needed-for-node2-tag-array
                                                                                         nodenums-to-translate cut-nodenum-type-alist extra-asserts print var-type-alist))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-for-aggressively-cut-proof))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This assumes the miter is pure.
;; Only used by the equivalence-checker.
;;only used for probably-constant nodes
;;only cuts at variables
;FIXME can we clean this up?
;; Only used by the equivalence-checker.
;returns (mv nodenums-to-translate ;decreasing order
;            cut-nodenum-type-alist)
;fixme implement increasingly aggressive cuts?
; TODO: Considing using a worklist.
;todo: compare to gather-nodes-to-translate-up-to-depth
;todo: generate extra asserts for bvmults?
(defund gather-nodes-for-translation (n ;counts down and stops at -1
                                      dag-array-name dag-array dag-len ; dag-len is only used for the guard
                                      var-type-alist ;; todo: what about types we can't handle?
                                      needed-for-node1-tag-array ; todo: rename this array, since there is only one node
                                      nodenums-to-translate ;gets extended, in increasing order
                                      cut-nodenum-type-alist ; gets extended
                                      )
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (integerp n)
                              (<= -1 n)
                              (< n dag-len)
                              (symbol-alistp var-type-alist) ; the cdrs should be axe-types?
                              ;; (nodenum-type-alistp cut-nodenum-type-alist) ; todo
                              (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
                              (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
                              (nat-listp nodenums-to-translate)
                              )
                  :measure (nfix (+ 1 n))))
  (if (not (natp n))
      (mv (reverse-list nodenums-to-translate) cut-nodenum-type-alist)
    (let* ((needed-for-node1 (aref1 'needed-for-node1-tag-array needed-for-node1-tag-array n)))
      (if needed-for-node1
          (let ((expr (aref1 dag-array-name dag-array n)))
            (if (variablep expr)
                ;; variable; we'll cut:
                (gather-nodes-for-translation (+ -1 n) dag-array-name dag-array dag-len var-type-alist
                                              needed-for-node1-tag-array
                                              nodenums-to-translate
                                              (acons-fast n (lookup-eq-safe expr var-type-alist) cut-nodenum-type-alist))
              (if (fquotep expr)
                  ;; constant; we'll translate it:
                  (gather-nodes-for-translation (+ -1 n) dag-array-name dag-array dag-len var-type-alist
                                                needed-for-node1-tag-array
                                                (cons n nodenums-to-translate)
                                                cut-nodenum-type-alist)
                ;; function call (we'll translate it and mark its children as being needed)
                (let ((translatep t)) ; todo: simplify
                  (gather-nodes-for-translation (+ -1 n) dag-array-name dag-array dag-len var-type-alist
                                                (if translatep
                                                    (tag-nodenums-with-name (dargs expr) 'needed-for-node1-tag-array needed-for-node1-tag-array)
                                                  needed-for-node1-tag-array)
                                                (if translatep
                                                    (cons n nodenums-to-translate)
                                                  nodenums-to-translate)
                                                (if translatep
                                                    cut-nodenum-type-alist
                                                  (acons-fast n (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr)) cut-nodenum-type-alist)))))))
        ;; not needed, so skip it
        (gather-nodes-for-translation (+ -1 n) dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist)))))

;; todo issue with lookup-eq-safe -- allow returning an error?
;; (thm
;;   (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (integerp n)
;;                 (<= -1 n)
;;                 (< n dag-len)
;;                 (var-type-alistp var-type-alist)
;;                 (array1p 'needed-for-node1-tag-array needed-for-node1-tag-array)
;;                 (< n (alen1 'needed-for-node1-tag-array needed-for-node1-tag-array))
;;                 (nat-listp nodenums-to-translate)
;;                 (nodenum-type-alistp cut-nodenum-type-alist)
;;                 )
;;            (nodenum-type-alistp (mv-nth 1 (gather-nodes-for-translation n dag-array-name dag-array dag-len var-type-alist needed-for-node1-tag-array nodenums-to-translate cut-nodenum-type-alist))))
;;   :hints (("Goal" :in-theory (enable gather-nodes-for-translation))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Used in equivalence-checker.lisp
;TODO: Consider using a worklist algorithm.
;returns (mv erp nodenums-to-translate ;in decreasing order
;            cut-nodenum-type-alist
;            extra-asserts)
;where cut-nodenum-type-alist gives types for any new vars introduced at the cut
;we will translate nodes that are supporters and are above the cut
;; todo: do guards for functions like this cause expensive checks when we call them from :program mode code?
;; All nodes involved (everything tagged in the depth-array and supporters-tag-array) will be pure nodes.
;; Instead of returning errors,  suppose we could return most-general-type.
(defund gather-nodes-to-translate-up-to-depth (n
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
                              (symbol-alistp var-type-alist) ; the cdrs should be axe-types?
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
              (b* ((type (lookup-eq-safe expr var-type-alist))
                   ((when (not (axe-typep type))) ; should not fail (var-type-alist should assign types to all vars in the dag)
                    (cw "ERROR: Bad type, ~x0, for ~x1 in alist ~x2.~%" type expr var-type-alist)
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
                (symbol-alistp var-type-alist)
                (string-treep extra-asserts))
           (nat-listp (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))

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
                (symbol-alistp var-type-alist)
                (string-treep extra-asserts))
           (no-nodes-are-variablesp (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))
                                    dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))

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
                (symbol-alistp var-type-alist)
                (string-treep extra-asserts))
           (all-< (mv-nth 1 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))
                  dag-len))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))

;todo: may need the ability to return an error
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
                (symbol-alistp var-type-alist)
                (string-treep extra-asserts))
           (nodenum-type-alistp (mv-nth 2 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))

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
                (symbol-alistp var-type-alist)
                (string-treep extra-asserts))
           (all-< (strip-cars (mv-nth 2 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts)))
                  dag-len))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))

(defthm string-treep-of-mv-nth-3-of-gather-nodes-to-translate-up-to-depth
  (implies (string-treep extra-asserts)
           (string-treep (mv-nth 3 (gather-nodes-to-translate-up-to-depth n depth depth-array dag-array-name dag-array dag-len var-type-alist supporters-tag-array nodenums-to-translate cut-nodenum-type-alist extra-asserts))))
  :hints (("Goal" :in-theory (enable gather-nodes-to-translate-up-to-depth))))
