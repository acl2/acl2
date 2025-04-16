; A stobj to gather (non-read-only) parameters used in rewriting
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Unlike rewrite-stobj, this includes values that change during rewriting
;; (such as the DAG).  So rewrite-stobj2 has to be returned by the functions in
;; the main rewriter clique.

;; TODO: Consider adding more things to this, like the memoization, hit-counts,
;; tries, and limits.

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "wf-dagp")
(include-book "std/util/defaggregate" :dir :system)
(local (include-book "rational-lists"))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/acl2-arrays/aref1" :dir :system))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local (in-theory (e/d (integerp-when-natp
                        rationalp-when-natp
                        consp-of-cdr)
                       (natp))))

(local
  (defthm natp-of-+  ; move to natp.lisp
    (implies (and (natp x)
                  (natp y))
             (natp (+ x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes the "signature" of a bitxor/bvxor node.  Different nodes usually
;; (but not always) have different signatures).
(std::defaggregate xor-signature
  (;; (unquoted-size-arg natp)
   (nodenum-leaf-count natp)
   (min-nodenum-leaf natp)
   (max-nodenum-leaf natp)
   (combined-constant natp))
  :hons t ; since we use these as keys of a hons-equal hash-table
  )

(defconst *default-xor-signature*
  (xor-signature 0 0 0 0))

(thm (xor-signature-p *default-xor-signature*)) ; sanity check

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A stobj that gathers the 5 components of the DAG and the xor-signature information.
(defstobj+ rewrite-stobj2
  (dag-array :type t :initially nil) ; todo: strengthen pred? will always be named 'dag-array
  (dag-len :type (satisfies natp) ; using (integer 0 *) led to guards and theorems that didn't mention natp
           :initially 0)
  ;; we add "the-" to the names to avoid name clashes:
  (the-dag-parent-array :type t :initially nil) ; todo: strengthen pred? will always be named 'dag-parent-array
  (the-dag-constant-alist :type (satisfies dag-constant-alistp) :initially nil)
  (the-dag-variable-alist :type (satisfies dag-variable-alistp) :initially nil)
  ;; map from nodenums to xor-signatures (the size of 1000 is just a hint):
  (nodenum-to-xor-signature-map :type (hash-table eql 1000 (satisfies xor-signature-p))
                                :initially ;;*default-xor-signature* ; todo: better way to specify the initial value?
                                ((nodenum-leaf-count . 0)
                                 (min-nodenum-leaf . 0)
                                 (max-nodenum-leaf . 0)
                                 (combined-constant . 0)))
  (xor-signature-to-nodenums-map :type (hash-table hons-equal 1000 (satisfies nat-listp))) ; the size of 1000 is just a hint
  :inline t
  :renaming ((dag-array get-dag-array)
             (update-dag-array put-dag-array)

             (dag-len get-dag-len)
             (update-dag-len put-dag-len)

             (the-dag-parent-array get-dag-parent-array)
             (update-the-dag-parent-array put-dag-parent-array)

             (the-dag-constant-alist get-dag-constant-alist)
             (update-the-dag-constant-alist put-dag-constant-alist)

             (the-dag-variable-alist get-dag-variable-alist)
             (update-the-dag-variable-alist put-dag-variable-alist)))

(defthm rewrite-stobj2p-of-xor-signature-to-nodenums-map-put
  (implies (and (rewrite-stobj2p rewrite-stobj2)
                (nat-listp v))
           (rewrite-stobj2p (xor-signature-to-nodenums-map-put k v rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable rewrite-stobj2p
                                     xor-signature-to-nodenums-map-put
                                     xor-signature-to-nodenums-mapp))))

(defthm rewrite-stobj2p-of-nodenum-to-xor-signature-map-put
  (implies (and (rewrite-stobj2p rewrite-stobj2)
                (xor-signature-p v))
           (rewrite-stobj2p (nodenum-to-xor-signature-map-put k v rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable rewrite-stobj2p
                                     nodenum-to-xor-signature-map-put
                                     nodenum-to-xor-signature-mapp))))

(defthm nat-listp-of-cdr-of-hons-assoc-equal-when-xor-signature-to-nodenums-mapp
  (implies (xor-signature-to-nodenums-mapp map)
           (nat-listp (cdr (hons-assoc-equal sig map))))
  :hints (("Goal" :in-theory (enable hons-assoc-equal xor-signature-to-nodenums-mapp))))

(defthm nat-listp-of-xor-signature-to-nodenums-map-get
  (implies (rewrite-stobj2p rewrite-stobj2)
           (nat-listp (xor-signature-to-nodenums-map-get sig rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-get
                                     rewrite-stobj2p
                                     xor-signature-to-nodenums-mapp))))

(defthm xor-signature-p-of-cdr-of-hons-assoc-equal-when-xor-signature-to-nodenums-mapp
  (implies (and (nodenum-to-xor-signature-mapp map)
                (hons-assoc-equal sig map))
           (xor-signature-p (cdr (hons-assoc-equal sig map))))
  :hints (("Goal" :in-theory (enable hons-assoc-equal nodenum-to-xor-signature-mapp))))

(defthm xor-signature-p-of-nodenum-to-xor-signature-map-get
  (implies (and (rewrite-stobj2p rewrite-stobj2)
               ; (hons-assoc-equal sig map) ; drop?
                )
           (xor-signature-p (nodenum-to-xor-signature-map-get nodenum rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-get
                                     rewrite-stobj2p))))

(defthm get-dag-len-of-xor-signature-to-nodenums-map-put
  (equal (get-dag-len (xor-signature-to-nodenums-map-put k v rewrite-stobj2))
         (get-dag-len rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-put get-dag-len))))

(defthm get-dag-len-of-nodenum-to-xor-signature-map-put
  (equal (get-dag-len (nodenum-to-xor-signature-map-put k v rewrite-stobj2))
         (get-dag-len rewrite-stobj2))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-put get-dag-len))))

(defthm get-dag-array-of-nodenum-to-xor-signature-map-put
  (equal (get-dag-array (nodenum-to-xor-signature-map-put k v rewrite-stobj2))
         (get-dag-array rewrite-stobj2))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-put get-dag-array))))

(defthm get-dag-array-of-xor-signature-to-nodenums-map-put
  (equal (get-dag-array (xor-signature-to-nodenums-map-put k v rewrite-stobj2))
         (get-dag-array rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-put get-dag-array))))

(defthm get-dag-parent-array-of-nodenum-to-xor-signature-map-put
  (equal (get-dag-parent-array (nodenum-to-xor-signature-map-put k v rewrite-stobj2))
         (get-dag-parent-array rewrite-stobj2))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-put get-dag-parent-array))))

(defthm get-dag-parent-array-of-xor-signature-to-nodenums-map-put
  (equal (get-dag-parent-array (xor-signature-to-nodenums-map-put k v rewrite-stobj2))
         (get-dag-parent-array rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-put get-dag-parent-array))))

(defthm get-dag-variable-alist-of-nodenum-to-xor-signature-map-put
  (equal (get-dag-variable-alist (nodenum-to-xor-signature-map-put k v rewrite-stobj2))
         (get-dag-variable-alist rewrite-stobj2))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-put get-dag-variable-alist))))

(defthm get-dag-variable-alist-of-xor-signature-to-nodenums-map-put
  (equal (get-dag-variable-alist (xor-signature-to-nodenums-map-put k v rewrite-stobj2))
         (get-dag-variable-alist rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-put get-dag-variable-alist))))

(defthm get-dag-constant-alist-of-nodenum-to-xor-signature-map-put
  (equal (get-dag-constant-alist (nodenum-to-xor-signature-map-put k v rewrite-stobj2))
         (get-dag-constant-alist rewrite-stobj2))
  :hints (("Goal" :in-theory (enable nodenum-to-xor-signature-map-put get-dag-constant-alist))))

(defthm get-dag-constant-alist-of-xor-signature-to-nodenums-map-put
  (equal (get-dag-constant-alist (xor-signature-to-nodenums-map-put k v rewrite-stobj2))
         (get-dag-constant-alist rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-put get-dag-constant-alist))))

(defthm xor-signature-to-nodenums-map-get-of-nodenum-to-xor-signature-map-put
  (equal (xor-signature-to-nodenums-map-get k1 (nodenum-to-xor-signature-map-put k2 v rewrite-stobj2))
         (xor-signature-to-nodenums-map-get k1 rewrite-stobj2))
  :hints (("Goal" :in-theory (enable xor-signature-to-nodenums-map-get nodenum-to-xor-signature-map-put))))

;; todo: defstobj+ should do this, and prove rules:
(in-theory (disable nodenum-to-xor-signature-map-get
                    nodenum-to-xor-signature-map-put
                    xor-signature-to-nodenums-map-get
                    xor-signature-to-nodenums-map-put))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: use this more?
(defund wf-rewrite-stobj2p (rewrite-stobj2)
  (declare (xargs :stobjs rewrite-stobj2))
  (wf-dagp 'dag-array (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) 'dag-parent-array (get-dag-parent-array rewrite-stobj2) (get-dag-constant-alist rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2)))

(defthm wf-rewrite-stobj2p-conjuncts
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                ;; (rewrite-stobj2p rewrite-stobj2)
                )
           (and (pseudo-dag-arrayp 'dag-array (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2))
                (array1p 'dag-array (get-dag-array rewrite-stobj2)) ; follows from pseudo-dag-arrayp
                (natp (get-dag-len rewrite-stobj2))
                (integerp (get-dag-len rewrite-stobj2))
                (dag-parent-arrayp 'dag-parent-array (get-dag-parent-array rewrite-stobj2))
                (bounded-dag-parent-arrayp 'dag-parent-array (get-dag-parent-array rewrite-stobj2)  (get-dag-len rewrite-stobj2))
                (equal (alen1 'dag-parent-array (get-dag-parent-array rewrite-stobj2))
                       (alen1 'dag-array (get-dag-array rewrite-stobj2)))
                (dag-variable-alistp (get-dag-variable-alist rewrite-stobj2))
                (bounded-dag-variable-alistp (get-dag-variable-alist rewrite-stobj2)
                                             (get-dag-len rewrite-stobj2))
                (dag-constant-alistp (get-dag-constant-alist rewrite-stobj2))
                (bounded-dag-constant-alistp (get-dag-constant-alist rewrite-stobj2)
                                             (get-dag-len rewrite-stobj2))))
  :hints (("Goal" :in-theory (enable wf-rewrite-stobj2p))))

(defthm wf-rewrite-stobj2p-conjuncts-linear
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                ;; (rewrite-stobj2p rewrite-stobj2)
                )
           (<= (get-dag-len rewrite-stobj2) (alen1 'dag-array (get-dag-array rewrite-stobj2))))
           :rule-classes :linear
  :hints (("Goal" :in-theory (enable wf-rewrite-stobj2p))))

(defthm wf-rewrite-stobj2p-of-xor-signature-to-nodenums-map-put
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                (nat-listp v))
           (wf-rewrite-stobj2p (xor-signature-to-nodenums-map-put k v rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable wf-rewrite-stobj2p))))

(defthm wf-rewrite-stobj2p-of-nodenum-to-xor-signature-map-put
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                (xor-signature-p v))
           (wf-rewrite-stobj2p (nodenum-to-xor-signature-map-put k v rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable wf-rewrite-stobj2p))))

(defthm wf-rewrite-stobj2p-conjuncts2
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                ;(rewrite-stobj2p rewrite-stobj2)
                )
           (and (<= (get-dag-len rewrite-stobj2) 1152921504606846974)
                (<= 0 (get-dag-len rewrite-stobj2))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (wf-rewrite-stobj2p) (wf-rewrite-stobj2p-conjuncts)))))

(theory-invariant (incompatible (:rewrite wf-rewrite-stobj2p-conjuncts) (:definition wf-rewrite-stobj2p)))

(defthm pseudo-dag-arrayp-of-get-dag-array-when-wf-rewrite-stobj2p-gen
  (implies (and (wf-rewrite-stobj2p rewrite-stobj2)
                ;(rewrite-stobj2p rewrite-stobj2)
                (<= n (get-dag-len rewrite-stobj2))
                (natp n))
           (pseudo-dag-arrayp 'dag-array (get-dag-array rewrite-stobj2) n))
  :hints (("Goal" :use (wf-rewrite-stobj2p-conjuncts)
           :in-theory (disable wf-rewrite-stobj2p-conjuncts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "dag-array-builders")

;; returns (mv erp nodenum rewrite-stobj2)
(defund add-variable-to-dag-array-in-stobj (var rewrite-stobj2)
  (declare (xargs :guard (and (symbolp var)
                              (wf-rewrite-stobj2p rewrite-stobj2))
                  :stobjs rewrite-stobj2))
  (mv-let (erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
    (add-variable-to-dag-array var (get-dag-array rewrite-stobj2) (get-dag-len rewrite-stobj2) (get-dag-parent-array rewrite-stobj2) (get-dag-variable-alist rewrite-stobj2))
    (if erp
        (mv erp 0 rewrite-stobj2)
      (let* ((rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2)) ; abstract out this pattern?
             (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
             (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
           ;; (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2))
             (rewrite-stobj2 (put-dag-variable-alist dag-variable-alist rewrite-stobj2)))
        (mv nil nodenum rewrite-stobj2)))))

(defthm add-variable-to-dag-array-in-stobj-return-type
  (implies (and (not (mv-nth 0 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))) ; no error
                (symbolp var)
                (wf-rewrite-stobj2p rewrite-stobj2))
           (and (natp (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (wf-rewrite-stobj2p (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))
                (< (mv-nth 1 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))
                   (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))
                (<= (get-dag-len rewrite-stobj2)
                    (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2p)
                                  (natp wf-rewrite-stobj2p-conjuncts)))))

(defthm add-variable-to-dag-array-in-stobj-return-type-2
  (implies (and; (not (mv-nth 0 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))) ; no error
                (symbolp var)
                ; (wf-rewrite-stobj2p rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2))
           (rewrite-stobj2p (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2p) (natp wf-rewrite-stobj2p-conjuncts)))))

;; a bit gross, as it makes a claim about a single component of the stobj.
;; but this helps to support some rewriter rules with very few hyps.
(defthm add-variable-to-dag-array-in-stobj-return-type-3
  (implies (natp (get-dag-len rewrite-stobj2))
           (natp (get-dag-len (mv-nth 2 (add-variable-to-dag-array-in-stobj var rewrite-stobj2)))))
  :hints (("Goal" :in-theory (e/d (add-variable-to-dag-array-in-stobj wf-rewrite-stobj2p) (natp wf-rewrite-stobj2p-conjuncts)))))

;; rule for (WF-DAGP 'DAG-ARRAY (GET-DAG-ARRAY REWRITE-STOBJ2) (GET-DAG-LEN REWRITE-STOBJ2) 'DAG-PARENT-ARRAY (GET-DAG-PARENT-ARRAY REWRITE-STOBJ2) (GET-DAG-CONSTANT-ALIST REWRITE-STOBJ2) (GET-DAG-VARIABLE-ALIST REWRITE-STOBJ2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the signature for the bitxor nest that would result from bitxoring X and Y
;; TODO: Consider cancelling duplicates between X and Y:
;; KEEP IN SYNC WITH BVXOR-SIGNATURE.
(defund bitxor-signature (x y rewrite-stobj2)
  (declare (xargs :guard (and (dargp-less-than x (get-dag-len rewrite-stobj2))
                              (dargp-less-than y (get-dag-len rewrite-stobj2))
                              (wf-rewrite-stobj2p rewrite-stobj2))
                  :stobjs rewrite-stobj2))
  (b* ((dag-array (get-dag-array rewrite-stobj2))
       (x-type (if (consp x) ; tests for quotep
                   :constant
                 (if (call-of 'bitxor (aref1 'dag-array dag-array x))
                     :non-leaf
                   :leaf)))
       (y-type (if (consp y) ; tests for quotep
                   :constant
                 (if (call-of 'bitxor (aref1 'dag-array dag-array y))
                     :non-leaf
                   :leaf)))
       (sig (if (eq :constant x-type)
                (if (eq :constant y-type)
                    ;; can't handle this, because the min and max nodenums would be undefined
                    (prog2$ (er hard? 'bitxor-signature "xor node with both arguments (~x0 and ~x1) constant." x y)
                            (xor-signature 0 0 0 0))
                  (if (eq :leaf y-type)
                      ;; x is a constant, y is a leaf:
                      (xor-signature 1 y y (bvchop 1 (ifix (unquote x))))
                    ;; x is a constant, y is a non-leaf:
                    (let ((y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                      (xor-signature (xor-signature->nodenum-leaf-count y-sig)
                                     (xor-signature->min-nodenum-leaf y-sig)
                                     (xor-signature->max-nodenum-leaf y-sig)
                                     (bitxor (ifix (unquote x))
                                             (ifix (xor-signature->combined-constant y-sig)))))))
              (if (eq :leaf x-type)
                  (if (eq :constant y-type)
                      ;; x is a leaf, y is a constant:
                      (xor-signature 1 x x (bvchop 1 (ifix (unquote y))))
                    (if (eq :leaf y-type)
                        ;; x and y are both leaves:
                        (xor-signature 2 (min x y) (max x y) 0)
                      ;; x is a leaf, y is a non-leaf:
                      (let ((y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                        (xor-signature (+ 1 (xor-signature->nodenum-leaf-count y-sig))
                                       (min x (xor-signature->min-nodenum-leaf y-sig))
                                       (max x (xor-signature->max-nodenum-leaf y-sig))
                                       (xor-signature->combined-constant y-sig)))))
                ;; x is a non-leaf:
                (if (eq :constant y-type)
                    ;; x is a non-leaf, y is a constant:
                    (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2)))
                      (xor-signature (xor-signature->nodenum-leaf-count x-sig)
                                     (xor-signature->min-nodenum-leaf x-sig)
                                     (xor-signature->max-nodenum-leaf x-sig)
                                     (bitxor (ifix (unquote y))
                                             (ifix (xor-signature->combined-constant x-sig)))))
                  (if (eq :leaf y-type)
                      ;; x is a non-leaf, y is a leaf:
                      (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2)))
                        (xor-signature (+ 1 (xor-signature->nodenum-leaf-count x-sig))
                                       (min y (xor-signature->min-nodenum-leaf x-sig))
                                       (max y (xor-signature->max-nodenum-leaf x-sig))
                                       (xor-signature->combined-constant x-sig)))
                    ;; both x and y are non-leaves:
                    (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2))
                          (y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                      (xor-signature (+ (xor-signature->nodenum-leaf-count x-sig) (xor-signature->nodenum-leaf-count y-sig))
                                     (min (xor-signature->min-nodenum-leaf x-sig) (xor-signature->min-nodenum-leaf y-sig))
                                     (max (xor-signature->max-nodenum-leaf x-sig) (xor-signature->max-nodenum-leaf y-sig))
                                     (bitxor (xor-signature->combined-constant x-sig) (xor-signature->combined-constant y-sig))))))))))
    sig))

(defthm xor-signature-p-of-bitxor-signature
  (implies (and (dargp-less-than x (get-dag-len rewrite-stobj2))
                (dargp-less-than y (get-dag-len rewrite-stobj2))
                (wf-rewrite-stobj2p rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2))
           (xor-signature-p (bitxor-signature x y rewrite-stobj2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bitxor-signature xor-signature-p) (aref1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the signature for the bvxor nest that would result from bvxoring X and Y (using SIZE as the first arg to bvxor).
;; TODO: Consider cancelling duplicates between X and Y:
;; KEEP IN SYNC WITH BITXOR-SIGNATURE.
(defund bvxor-signature (size x y rewrite-stobj2)
  (declare (xargs :guard (and (natp size)
                              (dargp-less-than x (get-dag-len rewrite-stobj2))
                              (dargp-less-than y (get-dag-len rewrite-stobj2))
                              (wf-rewrite-stobj2p rewrite-stobj2))
                  :stobjs rewrite-stobj2
                  :guard-hints (("Goal" :in-theory (enable <-of-+-of-1-strengthen-2)))))
  (b* ((dag-array (get-dag-array rewrite-stobj2))
       (x-type (if (consp x)
                   :constant
                 (if (let ((x-expr (aref1 'dag-array dag-array x)))
                       (and (call-of 'bvxor x-expr)
                            (consp (dargs x-expr)) ; for guards
                            (consp (darg1 x-expr)) ; checks for quotep
                            (equal (unquote (darg1 x-expr)) size)))
                     :non-leaf
                   :leaf)))
       (y-type (if (consp y)
                   :constant
                 (if (let ((y-expr (aref1 'dag-array dag-array y)))
                       (and (call-of 'bvxor y-expr)
                            (consp (dargs y-expr)) ; for guards
                            (consp (darg1 y-expr)) ; checks for quotep
                            (equal (unquote (darg1 y-expr)) size)))
                     :non-leaf
                   :leaf)))
       (sig (if (eq :constant x-type)
                (if (eq :constant y-type)
                    ;; can't handle this, because the min and max nodenums would be undefined
                    (prog2$ (er hard? 'bvxor-signature "xor node of size ~x0 with both arguments (~x1 and ~x2) constant." size x y)
                            (xor-signature 0 0 0 0))
                  (if (eq :leaf y-type)
                      (xor-signature 1 y y (bvchop size (ifix (unquote x))))
                    ;; y is a non-leaf:
                    (let ((y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                      (xor-signature (xor-signature->nodenum-leaf-count y-sig)
                                     (xor-signature->min-nodenum-leaf y-sig)
                                     (xor-signature->max-nodenum-leaf y-sig)
                                     (bvxor size
                                            (ifix (unquote x))
                                            (ifix (xor-signature->combined-constant y-sig)))))))
              (if (eq :leaf x-type)
                  (if (eq :constant y-type)
                      (xor-signature 1 x x (bvchop size (ifix (unquote y))))
                    (if (eq :leaf y-type)
                        (xor-signature 2 (min x y) (max x y) 0)
                      ;; y is a non-leaf:
                      (let ((y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                        (xor-signature (+ 1 (xor-signature->nodenum-leaf-count y-sig))
                                       (min x (xor-signature->min-nodenum-leaf y-sig))
                                       (max x (xor-signature->max-nodenum-leaf y-sig))
                                       (xor-signature->combined-constant y-sig)))))
                ;; x is a non-leaf:
                (if (eq :constant y-type)
                    (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2)))
                      (xor-signature (xor-signature->nodenum-leaf-count x-sig)
                                     (xor-signature->min-nodenum-leaf x-sig)
                                     (xor-signature->max-nodenum-leaf x-sig)
                                     (bvxor size
                                            (ifix (unquote y))
                                            (ifix (xor-signature->combined-constant x-sig)))))
                  (if (eq :leaf y-type)
                      (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2)))
                        (xor-signature (+ 1 (xor-signature->nodenum-leaf-count x-sig))
                                       (min y (xor-signature->min-nodenum-leaf x-sig))
                                       (max y (xor-signature->max-nodenum-leaf x-sig))
                                       (xor-signature->combined-constant x-sig)))
                    ;; y is a non-leaf:
                    (let ((x-sig (nodenum-to-xor-signature-map-get x rewrite-stobj2))
                          (y-sig (nodenum-to-xor-signature-map-get y rewrite-stobj2)))
                      (xor-signature (+ (xor-signature->nodenum-leaf-count x-sig) (xor-signature->nodenum-leaf-count y-sig))
                                     (min (xor-signature->min-nodenum-leaf x-sig) (xor-signature->min-nodenum-leaf y-sig))
                                     (max (xor-signature->max-nodenum-leaf x-sig) (xor-signature->max-nodenum-leaf y-sig))
                                     (bvxor size
                                            (xor-signature->combined-constant x-sig)
                                            (xor-signature->combined-constant y-sig))))))))))
    sig))

(defthm xor-signature-p-of-bvxor-signature
  (implies (and (natp size)
                (dargp-less-than x (get-dag-len rewrite-stobj2))
                (dargp-less-than y (get-dag-len rewrite-stobj2))
                (wf-rewrite-stobj2p rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2))
           (xor-signature-p (bvxor-signature size x y rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable bvxor-signature nodenum-to-xor-signature-mapp xor-signature xor-signature-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Populates the 2 fields of the stobj related to xor signatures
;; Every relevant node below index should already have info stored.
;; TODO: What about removing duplicates, since x XOR x = 0?
(defund set-xor-signature-fields (nodenum rewrite-stobj2)
  (declare (xargs :guard (and (natp nodenum)
                              (wf-rewrite-stobj2p rewrite-stobj2))
                  :stobjs rewrite-stobj2
                  :measure (+ 1 (nfix (- (nfix (get-dag-len rewrite-stobj2)) (nfix nodenum))))
                  :guard-hints (("Goal" :in-theory (e/d (wf-rewrite-stobj2p
                                                         wf-dagp
                                                         ;; todo:
                                                         bvxor-signature
                                                         bitxor-signature)
                                                        (wf-rewrite-stobj2p-conjuncts))))))
  (if (or (not (mbt (and (natp nodenum) ; for termination
                         (natp (get-dag-len rewrite-stobj2)))))
          (>= nodenum (get-dag-len rewrite-stobj2)))
      rewrite-stobj2
    (let* ((dag-array (get-dag-array rewrite-stobj2))
           (expr (aref1 'dag-array dag-array nodenum)))
      (if (not (and (consp expr)
                    (not (eq 'quote (car expr)))))
          (set-xor-signature-fields (+ 1 nodenum) rewrite-stobj2)
        ;; expr is a function call:
        (let* ((fn (ffn-symb expr)))
          (if (and (eq 'bitxor fn) ; (bitxor x y)
                   (consp (cdr (dargs expr))))
              (let* ((sig (bitxor-signature (darg1 expr) (darg2 expr) rewrite-stobj2))
                     ;; Set the signature for this node:
                     (rewrite-stobj2 (nodenum-to-xor-signature-map-put nodenum sig rewrite-stobj2))
                     ;; Add this node to the list of nodes that have this signature:
                     (rewrite-stobj2 (xor-signature-to-nodenums-map-put sig (cons nodenum (xor-signature-to-nodenums-map-get sig rewrite-stobj2)) rewrite-stobj2)))
                (set-xor-signature-fields (+ 1 nodenum) rewrite-stobj2))
            (if (and (eq 'bvxor fn) ; (bvxor size x y)
                     (consp (cddr (dargs expr)))
                     (consp (darg1 expr)) ; checks for quotep
                     (natp (unquote (darg1 expr))))
                (b* ((quoted-size (darg1 expr))
                     (size (unquote quoted-size))
                     (sig (bvxor-signature size (darg2 expr) (darg3 expr) rewrite-stobj2))
                     ;; Set the signature for this node:
                     (rewrite-stobj2 (nodenum-to-xor-signature-map-put nodenum sig rewrite-stobj2))
                     ;; Add this node to the list of nodes that have this signature: -- todo: this mixes bvxor (of all sizes) and bitxor (may be ok)
                     (rewrite-stobj2 (xor-signature-to-nodenums-map-put sig (cons nodenum (xor-signature-to-nodenums-map-get sig rewrite-stobj2)) rewrite-stobj2)))
                  (set-xor-signature-fields (+ 1 nodenum) rewrite-stobj2))
              ;; not an xor (that we can handle):
              (set-xor-signature-fields (+ 1 nodenum) rewrite-stobj2))))))))

(defthm set-xor-signature-fields-return-type
  (implies (and (natp nodenum)
                (wf-rewrite-stobj2p rewrite-stobj2)
                (rewrite-stobj2p rewrite-stobj2))
           (and (rewrite-stobj2p (set-xor-signature-fields nodenum rewrite-stobj2))
                (wf-rewrite-stobj2p (set-xor-signature-fields nodenum rewrite-stobj2))))
  :hints (("Goal" :induct t
           :in-theory (e/d (set-xor-signature-fields
                            ;;rewrite-stobj2p
                            wf-rewrite-stobj2p)
                           (wf-rewrite-stobj2p-conjuncts)))))

(defthm set-xor-signature-fields-get-other-fields
  (and (equal (get-dag-len (set-xor-signature-fields nodenum rewrite-stobj2)) (get-dag-len rewrite-stobj2))
       (equal (get-dag-array (set-xor-signature-fields nodenum rewrite-stobj2)) (get-dag-array rewrite-stobj2))
       (equal (get-dag-parent-array (set-xor-signature-fields nodenum rewrite-stobj2)) (get-dag-parent-array rewrite-stobj2))
       (equal (get-dag-constant-alist (set-xor-signature-fields nodenum rewrite-stobj2)) (get-dag-constant-alist rewrite-stobj2))
       (equal (get-dag-variable-alist (set-xor-signature-fields nodenum rewrite-stobj2)) (get-dag-variable-alist rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable set-xor-signature-fields))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund load-dag (dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)
  (declare (xargs :guard (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                  :stobjs rewrite-stobj2))
  (b* ((rewrite-stobj2 (put-dag-array dag-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-len dag-len rewrite-stobj2))
       (rewrite-stobj2 (put-dag-parent-array dag-parent-array rewrite-stobj2))
       (rewrite-stobj2 (put-dag-constant-alist dag-constant-alist rewrite-stobj2))
       (rewrite-stobj2 (put-dag-variable-alist dag-variable-alist rewrite-stobj2)))
    rewrite-stobj2))

(defthm rewrite-stobj2p-of-load-dag
  (implies (and (rewrite-stobj2p rewrite-stobj2)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;(natp dag-len)
                )
           (rewrite-stobj2p (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)))
  :hints (("Goal" :in-theory (enable load-dag))))

(defthm wf-rewrite-stobj2p-of-load-dag
  (implies (and (rewrite-stobj2p rewrite-stobj2)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;(natp dag-len)
                )
           (wf-rewrite-stobj2p (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)))
  :hints (("Goal" :in-theory (e/d (load-dag wf-rewrite-stobj2p) (wf-rewrite-stobj2p-conjuncts)))))

(defthm get-xxx-of-load-dag
  (and (equal (get-dag-len (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)) dag-len)
       (equal (get-dag-array (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)) dag-array)
       (equal (get-dag-parent-array (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)) dag-parent-array)
       (equal (get-dag-constant-alist (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)) dag-constant-alist)
       (equal (get-dag-variable-alist (load-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist rewrite-stobj2)) dag-variable-alist))
  :hints (("Goal" :in-theory (enable load-dag))))
