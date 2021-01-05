; Converting a dag to a term using lets.
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

;; See also dag-to-term-with-lets-simple.lisp.

(include-book "dag-parent-array-with-name")
(include-book "supporting-nodes")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; TODO: Consider not lifting let-bound variables up through IFs (can cause problems with guards).
;; TODO: Consider splitting the result into several functions if a single function would be too large.
;; TODO: Consider, for nodes that are vars, omitting them and simplify replacing mentions of each with its var.

;; the supporters array maps nodenums to lists of nodenums that support them (including each node itself)
(def-typed-acl2-array supporters-arrayp (and (nat-listp val)
                                             (all-<= val index)))

;; (defun supporters-arrayp (array-name array max)
;;   (declare (xargs :guard (integerp max)))
;;   (and (array1p array-name array)
;;        (< max (alen1 array-name array))
;;        (all-dag-parent-entriesp max array-name array) ;todo rename this
;;        ))

;move?
(defthm <-of-largest-non-quotep-of-dargs-of-aref1
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array nodenum)
                (natp nodenum)
                (not (equal 'quote (car (aref1 dag-array-name dag-array nodenum)))))
           (< (largest-non-quotep (dargs (aref1 dag-array-name dag-array nodenum)))
              nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance <-of-largest-non-quotep-of-dargs (expr (aref1 dag-array-name dag-array nodenum))))))

(defun supporters-of-args (items supporters-array acc)
  (declare (xargs :guard (and (true-listp items)
                              (all-dargp items)
                              (supporters-arrayp 'supporters-array supporters-array (+ 1 (largest-non-quotep items)))
                              (all-dargp-less-than items (alen1 'supporters-array supporters-array)) ; a bit redundant
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable true-listp-when-nat-listp-rewrite
                                                           eqlable-listp-when-nat-listp)))))
  (if (atom items)
      acc
    (let ((item (first items)))
      (if (consp item) ;tests for quotep
          (supporters-of-args (rest items) supporters-array acc)
        ;; consider union-eql-tail here:
        (supporters-of-args (rest items) supporters-array (union$ (aref1 'supporters-array supporters-array item) acc))))))

(defthm true-listp-of-supporters-of-args
  (implies (true-listp acc)
           (true-listp (supporters-of-args items supporters-array acc))))

(defthm nat-listp-of-supporters-of-args
  (implies (and (nat-listp acc)
                (all-dargp items)
                (supporters-arrayp 'supporters-array supporters-array (+ 1 (largest-non-quotep items))))
           (nat-listp (supporters-of-args items supporters-array acc)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm all-<=-of-supporters-of-args
  (implies (and (all-dargp-less-than args n)
                (supporters-arrayp 'supporters-array supporters-array (+ 1 (largest-non-quotep args)))
                (all-<= acc n))
           (all-<= (supporters-of-args args supporters-array acc)
                   n))
  :hints (("subGoal *1/7" :use ((:instance TYPE-OF-AREF1-WHEN-SUPPORTERS-ARRAYP
                                           (array-name 'supporters-array)
                                           (array supporters-array)
                                           (index (CAR ARGS))
                                           (num-valid-nodes (+ 1 (LARGEST-NON-QUOTEP ARGS)))
                                           ))
           :in-theory (e/d (<-of-car-when-all-dargp-less-than)
                           (TYPE-OF-AREF1-WHEN-SUPPORTERS-ARRAYP)))))


;; Fill in the supporters for nodes N through MAX-NODENUM.
;i'm going to say a node counts as its own supporter
(defun make-supporters-array-aux (n max-nodenum dag-array-name dag-array supporters-array)
  (declare (xargs :measure (nfix (+ 1 (- max-nodenum n)))
                  :hints (("Goal" :in-theory (enable natp)))
                  :guard (and (natp n)
                              (natp max-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 max-nodenum))
                              (supporters-arrayp 'supporters-array supporters-array (+ 1 max-nodenum))
                              ;; (ARRAY1P 'supporters-array supporters-array)
                              ;; (NATP max-nodenum)
                              ;; (< max-nodenum (alen1 'supporters-array supporters-array))
                              ;; (<= n max-nodenum)
                              ;; (SUPPORTERS-ARRAYP-AUX 'supporters-array supporters-array n)
                              ;;(array1p 'supporters-array supporters-array)
                              ;;(< max-nodenum (alen1 'supporters-array supporters-array))
                              )
                  :guard-hints (("Goal"
                                 :use (:instance SUPPORTERS-ARRAYP-AUX-OF-ASET1
                                                 (INDEX MAX-NODENUM)
                                                 (VAL (CONS N
                                                            (SUPPORTERS-OF-ARGS
                                                             (DARGS (AREF1 DAG-ARRAY-NAME DAG-ARRAY N))
                                                             SUPPORTERS-ARRAY NIL)))
                                                 (INDEX2 N)
                                                 (ARRAY SUPPORTERS-ARRAY)
                                                 (ARRAY-NAME 'SUPPORTERS-ARRAY))
                                 :in-theory (e/d (SUPPORTERS-ARRAYP) (SUPPORTERS-ARRAYP-AUX-OF-ASET1))))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp max-nodenum)))
          (> n max-nodenum))
      supporters-array
    (let* ((expr (aref1 dag-array-name dag-array n)))
      (if (or (variablep expr)
              (fquotep expr))
          ;; no supporters (so nil is right)
          (make-supporters-array-aux (+ 1 n) max-nodenum dag-array-name dag-array supporters-array)
        (make-supporters-array-aux (+ 1 n) max-nodenum dag-array-name dag-array
                                   (aset1 'supporters-array
                                          supporters-array
                                          n
                                          (cons n (supporters-of-args (dargs expr) supporters-array nil))))))))

(defthm alen1-of-make-supporters-array-aux
  (implies (and (natp n)
                (natp max-nodenum)
                (< max-nodenum (alen1 'SUPPORTERS-ARRAY SUPPORTERS-ARRAY)))
           (equal (alen1 'supporters-array (make-supporters-array-aux n max-nodenum dag-array-name dag-array supporters-array))
                  (alen1 'supporters-array supporters-array))))

;move
(defthm not-<-of-one-less-and-largest-non-quotep-of-dargs
  (implies (and (bounded-dag-exprp n expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (natp n))
           (not (< (+ -1 n) (largest-non-quotep (dargs$inline expr)))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

(defthm not-<-of-one-more-than-largest-non-quotep-of-dargs
  (implies (and (bounded-dag-exprp n expr)
                (consp expr)
                (not (equal 'quote (car expr)))
                (natp n))
           (not (< n (+ 1 (largest-non-quotep (dargs$inline expr))))))
  :hints (("Goal" :in-theory (enable bounded-dag-exprp))))

;; (defthm not-<-of-one-less-and-largest-non-quotep-of-dargs-of-aref1
;;   (implies (and (consp expr)
;;                 (not (equal 'quote (car expr)))
;;                 (natp n)
;;                 (pseudo-dag-arrayp
;;                 )
;;            (not (< (+ -1 n) (largest-non-quotep (dargs (aref1 dag-array-name dag-array n))))))

(defthm bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux-gen
  (implies (and (pseudo-dag-arrayp-aux dag-array-name dag-array n)
                (natp m)
                (<= m n)
                (natp m2)
                (<= m m2)
                (natp n))
           (bounded-dag-exprp m2 (aref1 dag-array-name dag-array m)))
  :hints (("Goal" :use (:instance bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux)
           :in-theory (disable bounded-dag-exprp-of-aref1-when-pseudo-dag-arrayp-aux))))

(defthm all-myquotep-of-dargs-of-aref1-of-0
  (implies (and (consp (aref1 dag-array-name dag-array 0))
                (not (equal (car (aref1 dag-array-name dag-array 0))
                            'quote))
                (pseudo-dag-arrayp-aux dag-array-name dag-array 0)
                (natp n))
           (all-myquotep (dargs (aref1 dag-array-name dag-array 0))))
  :hints (("Goal" :expand ((pseudo-dag-arrayp-aux dag-array-name dag-array 0))
           :in-theory (enable bounded-dag-exprp))))

(defthm supporters-of-args-when-all-myquotep
  (implies (all-myquotep items)
           (equal (supporters-of-args items supporters-array acc)
                  acc)))

;may need to say it's the supporters array for that particular dag...
(defthm supporters-arrayp-aux-of-make-supporters-array-aux
  (implies (and (natp n)
                (natp index)
                (<= index max-nodenum)
                (natp max-nodenum)
                ;(<= n max-nodenum)
                (< max-nodenum (alen1 'supporters-array supporters-array))
                (< index (alen1 'supporters-array supporters-array))
                (supporters-arrayp-aux 'supporters-array supporters-array index) ;some items may be left (at nil)
                (array1p 'supporters-array supporters-array)
                (equal nil (default 'supporters-array supporters-array))
                (pseudo-dag-arrayp-aux dag-array-name dag-array max-nodenum))
           (supporters-arrayp-aux 'supporters-array (make-supporters-array-aux n max-nodenum dag-array-name dag-array supporters-array) index))
  :hints (("Subgoal *1/9" :cases ((< index n)))
          ("Goal" :expand ((:free (arr)
                                  (SUPPORTERS-ARRAYP-AUX 'SUPPORTERS-ARRAY arr 0))
                           (MAKE-SUPPORTERS-ARRAY-AUX 0 0 DAG-ARRAY-NAME
                                                      DAG-ARRAY SUPPORTERS-ARRAY)
                           (MAKE-SUPPORTERS-ARRAY-AUX MAX-NODENUM MAX-NODENUM DAG-ARRAY-NAME
                                                      DAG-ARRAY SUPPORTERS-ARRAY)
                           (supporters-arrayp-aux 'supporters-array
                                                  supporters-array (+ -1 n)))
;           :induct (make-supporters-array-aux n max-nodenum dag-array-name dag-array supporters-array)
           :in-theory (enable supporters-arrayp-aux
                              supporters-arrayp
                              make-supporters-array-aux))))

(defthm array1p-aux-of-make-supporters-array-aux
  (implies (and (natp n)
                (natp max-nodenum)
                (< max-nodenum (alen1 'supporters-array supporters-array))
                (array1p 'supporters-array supporters-array))
           (array1p 'supporters-array (make-supporters-array-aux n max-nodenum dag-array-name dag-array supporters-array))))

(defthm default-of-make-supporters-array-aux
  (equal (default 'supporters-array (make-supporters-array-aux n max-nodenum dag-array-name dag-array supporters-array))
         (default 'supporters-array supporters-array)))

;returns an array named 'supporters-array
(defund make-supporters-array (dag-len dag-array-name dag-array)
  (declare (xargs :guard (and (posp dag-len)
                              (<= dag-len 2147483646)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len))))
  (make-supporters-array-aux 0 (+ -1 dag-len) dag-array-name dag-array (make-empty-array 'supporters-array dag-len)))

(defthm alen1-of-make-supporters-array
  (implies (and (posp dag-len)
                (<= dag-len 2147483646))
           (equal (alen1 'supporters-array (make-supporters-array dag-len dag-array-name dag-array))
                  dag-len))
  :hints (("Goal" :in-theory (enable make-supporters-array))))

(defthm supporters-arrayp-aux-of-make-empty-array
  (implies (and (natp n)
                (<= n dag-len)
                (natp dag-len)
                (posp dag-len)
                (< dag-len 2147483647))
           (supporters-arrayp-aux 'supporters-array
                                  (make-empty-array 'supporters-array dag-len)
                                  n))
  :hints (("Goal" :in-theory (enable supporters-arrayp-aux))))

(defthm supporters-arrayp-of-make-supporters-array
  (implies (and (posp dag-len)
                (<= DAG-LEN 2147483646)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len))
           (supporters-arrayp 'supporters-array (make-supporters-array dag-len dag-array-name dag-array) dag-len))
  :hints (("Goal" :in-theory (enable SUPPORTERS-ARRAYP make-supporters-array pseudo-dag-arrayp))))

;;Return the members of ITEMS that are nodes whose supporters include target-nodenum.
(defun nodenums-supported-by-target (items target-nodenum supporters-array)
  (declare (xargs :guard (and (true-listp items)
                              (all-dargp items)
                              (supporters-arrayp 'supporters-array supporters-array (+ 1 (largest-non-quotep items)))
                              (all-dargp-less-than items (alen1 'supporters-array supporters-array)) ; a bit redundant
                              (natp target-nodenum))
                  :guard-hints (("Goal" :in-theory (enable TRUE-LISTP-WHEN-NAT-LISTP-rewrite)))
                  ))
  (if (endp items)
      nil
    (let ((item (first items)))
      (if (consp item) ;quotep
          (nodenums-supported-by-target (rest items) target-nodenum supporters-array)
        (if (member target-nodenum (aref1 'supporters-array supporters-array item))
            (cons item (nodenums-supported-by-target (rest items) target-nodenum supporters-array))
          (nodenums-supported-by-target (rest items) target-nodenum supporters-array))))))

(defthm all-natp-of-nodenums-supported-by-target
  (implies (all-dargp items)
           (all-natp (nodenums-supported-by-target items target-nodenum supporters-array))))

(defthm all-<-of-nodenums-supported-by-target
  (implies (all-dargp-less-than items bound)
           (all-< (nodenums-supported-by-target items target-nodenum supporters-array) bound)))

(defthmd not-<-of-0-of-car-when-all-natp
  (implies (all-natp lst)
           (not (< (car lst) 0))))

(defthmd integerp-of-car-when-all-natp
  (implies (and (all-natp lst)
                (consp lst))
           (integerp (car lst)))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthmd <=-of-+-1-of-car-when-all-<
  (implies (and (all-< lst bound)
                (consp lst)
                (all-natp lst)
                (integerp bound))
           (not (< bound (+ 1 (CAR lst)))))
  :hints (("Goal" :in-theory (enable all-< all-natp))))

(defthmd not-<-of-+-1-of-car-and-0
  (implies (and (consp lst)
                (all-natp lst)
                )
           (not (< (+ 1 (CAR lst)) 0)))
  :hints (("Goal" :in-theory (enable all-< all-natp))))

(local
 (defthm bound-hack
  (implies (<= 0 x)
           (<= 0 (+ 1 x)))))

(local
 (defthm integerp-of-if
   (equal (integerp (if test tp ep))
          (if test
              (integerp tp)
            (integerp ep)))))

(defthm supporters-arrayp-forward
  (implies (supporters-arrayp array-name array array-len)
           (<= array-len (alen1 array-name array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable supporters-arrayp))))

(defthm supporters-arrayp-forward2
  (implies (supporters-arrayp array-name array array-len)
           (integerp (alen1 array-name array)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable supporters-arrayp))))

;todo: better name?
;; Nodenum must be supported by target-nodenum.  We find the smallest node that
;; appears on every path through which target-nodenum supports nodenum.  If
;; nodenum has only one child supported by target-nodenum, we can, without loss
;; of generality, recur on that child.  And so on.  Once we find a node with
;; more than one child supported by target-nodenum, we stop.  The result is
;; unique.
(defund smallest-common-ancestor (nodenum target-nodenum dag-array-name dag-array supporters-array)
  (declare (xargs :measure (+ 1 (nfix (+ 1 nodenum)))
                  :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                              (natp target-nodenum))
                  :guard-hints (("Goal" :in-theory (enable not-<-of-0-of-car-when-all-natp
                                                           <=-of-+-1-of-car-when-all-<
                                                           bound-hack
                                                           integerp-of-car-when-all-natp)))))
  (if (eql nodenum target-nodenum)
      nodenum
    (let* ((expr (aref1 dag-array-name dag-array nodenum)))
      (if (not (and (consp expr)
                    (not (eq 'quote (ffn-symb expr)))))
          ;; todo: drop this whole check: expr must be a fn call since it has a supporter
          (prog2$ (er hard? 'smallest-common-ancestor "Unexpected expr.")
                  nodenum)
        (let ((children-supported-by-target (nodenums-supported-by-target (dargs expr) target-nodenum supporters-array)))
          (if (endp children-supported-by-target)
              (prog2$ (er hard? 'smallest-common-ancestor "Unexpected expr.")
                      nodenum)
            (if (endp (cdr children-supported-by-target))
                ;;exactly one child is supported
                (if (not (mbt (and (natp nodenum)
                                   (< (first children-supported-by-target) nodenum))))
                    :error ;cannot happen
                  (smallest-common-ancestor (first children-supported-by-target) target-nodenum dag-array-name dag-array supporters-array))
              ;;more than one child is supported, so this node is the common ancestor
              nodenum)))))))

(defthm natp-of-smallest-common-ancestor
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                (natp target-nodenum))
           (natp (smallest-common-ancestor nodenum target-nodenum dag-array-name dag-array supporters-array)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable smallest-common-ancestor
                                     not-<-of-+-1-of-car-and-0
                                     <=-of-+-1-of-car-when-all-<
                                     integerp-of-car-when-all-natp))))

(defthm integerp-of-smallest-common-ancestor
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                (natp target-nodenum))
           (integerp (smallest-common-ancestor nodenum target-nodenum dag-array-name dag-array supporters-array))))

(defthm <=-of-0-and-smallest-common-ancestor
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                (natp target-nodenum))
           (<= 0 (smallest-common-ancestor nodenum target-nodenum dag-array-name dag-array supporters-array))))

(defthm not-equal-header-of-smallest-common-ancestor
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                (natp target-nodenum))
           (not (equal :header (smallest-common-ancestor nodenum target-nodenum dag-array-name dag-array supporters-array)))))

;nested induction
(defthm smallest-common-ancestor-bound
  (implies (and (natp nodenum)
;                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                (supporters-arrayp 'supporters-array supporters-array (+ 1 nodenum))
                (natp target-nodenum))
           (<= (smallest-common-ancestor nodenum target-nodenum dag-array-name dag-array supporters-array)
               nodenum))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable smallest-common-ancestor))))

;; (defun make-let-bindings (nodenum args binding-array acc)
;;   (if (endp args)
;;       (mv acc binding-array)
;;     (let ((arg (first args)))
;;       (if (consp arg) ;quotep
;;           (make-let-bindings nodenum (rest args) binding-array acc)
;;         (let ((binding-entry (aref1 'binding-array binding-array arg)))
;;           (if (not binding-entry)
;;               (make-let-bindings nodenum(rest args) binding-array acc)
;;             (let ((nodenum-around-which-to-make-binding (car binding-entry)))
;;               (if (not (eql nodenum nodenum-around-which-to-make-binding))
;;                   (make-let-bindings nodenum (rest args) binding-array acc)
;;                 (make-let-bindings nodenum (rest args)
;;                                    binding-array ;(aset1 'binding-array binding-array arg nil) ;don't bother to clear since this is the largest parent
;;                                    (add-to-set-equal (list (pack$ 'var-for-let arg) ;fixme watch out for clashes
;;                                                            (cdr binding-entry))
;;                                                      acc))))))))))

;todo: is the typedness of this overkill?
;; these are not pseudo-terms because they can contain let*
(def-typed-acl2-array term-arrayp (or (consp val)
                                      (symbolp val)))

(def-typed-acl2-array binding-arrayp
  (true-listp val) ;for now (it's a list of let bindings)
  )

;; Look up the ARGS that are nodenums to get their terms from TERM-ARRAY.  Pass
;; quoted constants through unchanged.
(defun terms-for-nodenums (args term-array-name term-array array-len)
  (declare (xargs :guard (and (term-arrayp term-array-name term-array array-len)
                              (true-listp args)
                              (all-dargp-less-than args (alen1 term-array-name term-array)))))
  (if (endp args)
      nil
    (let* ((arg (first args)))
      (cons (if (consp arg)
                ;;quoted constant, do nothing:
                arg
              ;;nodenum to fixup:
              (aref1 term-array-name term-array arg))
            (terms-for-nodenums (rest args) term-array-name term-array array-len)))))

(defun dag-array-to-term-with-lets-aux (nodenum top-nodenum dag-array-name dag-array parent-array term-array binding-array supporters-array)
  (declare (xargs :measure (nfix (+ 1 (- top-nodenum nodenum)))
                  :guard (and (natp nodenum)
                              (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 top-nodenum))
                              (<= (+ 1 top-nodenum)
                                  (alen1 dag-array-name dag-array))
                              (supporters-arrayp 'supporters-array supporters-array (+ 1 top-nodenum))
                              (equal (alen1 'supporters-array supporters-array)
                                     (+ 1 top-nodenum))
                              (term-arrayp 'term-array term-array (+ 1 top-nodenum))
                              (equal (alen1 'term-array term-array)
                                     (+ 1 top-nodenum))
                              ;; maps nodenums to list of (var expr) let-bindings:
                              (binding-arrayp 'binding-array binding-array (+ 1 top-nodenum))
                              (equal (alen1 'binding-array binding-array)
                                     (+ 1 top-nodenum))
                              (dag-parent-arrayp 'parent-array-temp parent-array)
                              (equal (alen1 'parent-array-temp parent-array)
                                     (+ 1 top-nodenum)))))
  (if (or (not (mbt (natp nodenum)))
          (not (mbt (natp top-nodenum)))
          (> nodenum top-nodenum)) ;final iteration (we've already built the term for the top nodenum, just like any other term
      (aref1 'term-array term-array top-nodenum)
    (let* ((expr (aref1 dag-array-name dag-array nodenum))
           (simplep (or (variablep expr)
                        (quotep expr))))
      (mv-let (new-expr let-bindings)
        (if simplep
            (mv expr nil)
          ;;it's a function call:
          (let ((args (dargs expr))
                (let-bindings (aref1 'binding-array binding-array nodenum)))
            (mv (cons (ffn-symb expr)
                      (terms-for-nodenums args 'term-array term-array (+ 1 top-nodenum)))
                let-bindings)))
        (let* ((new-expr (if let-bindings
                             `(let* ,(reverse-list let-bindings) ;; TODO: Use plain let if just one binding?
                                ,new-expr)
                           new-expr))
               (make-let-bindingp (and (not simplep)
                                       ;; Check whether the node has more than 1 parent:
                                       (consp (cdr (aref1 'parent-array-temp parent-array nodenum)))))
               (term (if make-let-bindingp
                         (pack$ 'var-for-let nodenum) ;fixme watch out for clashes, keep consistent with the var generated above
                       new-expr)))
          (dag-array-to-term-with-lets-aux (+ 1 nodenum) top-nodenum dag-array-name dag-array parent-array
                                           (aset1 'term-array term-array nodenum term)
                                           (if make-let-bindingp
                                               (let ((nodenum-to-wrap-with-binding (smallest-common-ancestor top-nodenum nodenum dag-array-name dag-array supporters-array)))
                                                 ;;we'll make the binding around the expression for the smallest common ancestor
                                                 (aset1 'binding-array binding-array nodenum-to-wrap-with-binding
                                                        (cons (list (pack$ 'var-for-let nodenum) ;fixme watch out for clashes
                                                                    new-expr)
                                                              (aref1 'binding-array binding-array nodenum-to-wrap-with-binding))))
                                             binding-array)
                                           supporters-array))))))

(defun dag-array-to-term-with-lets (dag-len dag-array-name dag-array)
  (declare (xargs :guard (and (posp dag-len)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len))))
  (let ((parent-array (make-dag-parent-array-with-name dag-len dag-array-name dag-array 'parent-array-temp))
        (term-array (make-empty-array 'term-array dag-len))
        (binding-array (make-empty-array 'binding-array dag-len))
        (supporters-array (make-supporters-array dag-len dag-array-name dag-array)))
    (dag-array-to-term-with-lets-aux 0 (+ -1 dag-len) dag-array-name dag-array parent-array term-array binding-array supporters-array)))

;; Returns an untranslated term (since it can contain let/let*).
(defun dag-to-term-with-lets (dag)
  (declare (xargs :guard (or (myquotep dag)
                             (and (pseudo-dagp dag)
                                  (<= (car (car dag)) 2147483645)))
                  :guard-hints (("Goal" :in-theory (enable pseudo-dagp)))))
  (if (quotep dag)
      dag
    (let* ((dag (drop-non-supporters dag)) ;prevents crashes if there are unreferenced nodes -- drop this?
           (dag-array-name 'dag-array-temp))
      (dag-array-to-term-with-lets (len dag) dag-array-name (make-into-array dag-array-name dag)))))

;; Example: (dag-to-term-with-lets (dagify-term '(+ (bar (baz x)) (foo (bar (baz x))))))
;; Example: (dag-to-term-with-lets (dagify-term! '(f (g (h (foo y x '3 (bar z))) (h (foo y x '3 (bar z)))))))
