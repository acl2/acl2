; Finding likely facts to break down a proof
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

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "bounded-darg-listp")
(include-book "test-cases")
(include-book "dag-arrays")
(include-book "evaluator-basic")
;(include-book "evaluate-test-case-common")
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove
(include-book "kestrel/bv/bvif" :dir :system) ; do not remove
(include-book "kestrel/booleans/bool-fix" :dir :system) ; do not remove
(local (include-book "rational-lists"))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
;(local (include-book "numeric-lists"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;; A simpler version of evaluate-test-case.lisp.  This uses the basic-evaluator.

;; A stobj for storing the value of each node in a DAG, as when evaluating a test case.
;; We could even copy the DAG into an array in this stobj, for faster lookups into it.
(defstobj+ test-case-stobj
  (node-val-array :type (array t (100)) :initially nil :resizable t)
  (done-node-array :type (array t (100)) :initially nil :resizable t)
  :inline t)

(defun set-done-vals-to-nil (i test-case-stobj)
  (declare (xargs :guard (and (integerp i)
                              (< i (done-node-array-length test-case-stobj)))
                  :stobjs test-case-stobj
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      test-case-stobj
    (let ((test-case-stobj (update-done-node-arrayi i nil test-case-stobj)))
      (set-done-vals-to-nil (+ -1 i) test-case-stobj))))

(defthm done-node-array-length-of-set-done-vals-to-nil
  (implies (and ; (integerp i)
                (< i (done-node-array-length test-case-stobj)))
           (equal (done-node-array-length (set-done-vals-to-nil i test-case-stobj))
                  (done-node-array-length test-case-stobj))))

;; (defthm test-case-stobjp-of-set-done-vals-to-nil
;;   (implies (test-case-stobjp test-case-stobj)
;;            (test-case-stobjp (set-done-vals-to-nil i test-case-stobj))))

;args are nodenums with values in the array, or quoteps
;looks up the nodenums and unquotes the constants
;does similar functionality exist elsewhere (array names might differ)?
(defund get-vals-of-dargs-in-test-case-stobj (dargs test-case-stobj)
  (declare (xargs :guard (bounded-darg-listp dargs (node-val-array-length test-case-stobj))
                  :stobjs test-case-stobj
                  ))
  (if (endp dargs)
      nil
    (let ((darg (first dargs)))
      (cons (if (consp darg) ; check for quoted constant
                (unquote darg)
              ;;otherwise it's a nodenum:
              (node-val-arrayi darg test-case-stobj))
            (get-vals-of-dargs-in-test-case-stobj (rest dargs) test-case-stobj)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;args are nodenums and/or quoteps
;;returns (mv worklist worklist-extendedp) where nodenum-worklist has been extended by any args to compute (non quoteps not marked done)
;; and worklist-extendedp indicates whether there were any such args
;rename?
;; Could combine with get-args-not-done-array?  But this one has the array name baked in.
(defund add-args-not-done-in-test-case-stobj (dargs worklist worklist-extendedp test-case-stobj)
  (declare (xargs :guard (and (bounded-darg-listp dargs (done-node-array-length test-case-stobj))
                              (true-listp worklist)
                              (booleanp worklist-extendedp))
                  :stobjs test-case-stobj))
  (if (endp dargs)
      (mv worklist worklist-extendedp)
    (let ((darg (first dargs)))
      (if (or (consp darg) ; skip quoted constants
              (done-node-arrayi darg test-case-stobj) ;;skip dargs that are marked as done
              )
          (add-args-not-done-in-test-case-stobj (rest dargs) worklist worklist-extendedp test-case-stobj)
        (add-args-not-done-in-test-case-stobj (rest dargs) (cons darg worklist) t test-case-stobj ;we've extended the worklist
                                              )))))

(defthm add-args-not-done-in-test-case-stobj-of-nil-arg1
  (equal (add-args-not-done-in-test-case-stobj nil worklist worklist-extendedp test-case-stobj)
         (mv worklist worklist-extendedp))
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

(defthm nat-listp-of-mv-nth-0-of-add-args-not-done-in-test-case-stobj
  (implies (and ;(array1p 'test-case-stobj test-case-stobj)
             (darg-listp args) ; (bounded-darg-listp args (alen1 'test-case-stobj test-case-stobj))
             (NAT-LISTP WORKLIST))
           (nat-listp (mv-nth 0 (add-args-not-done-in-test-case-stobj args worklist worklist-extendedp test-case-stobj))))
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

(defthm all-<-of-mv-nth-0-of-add-args-not-done-in-test-case-stobj
  (implies (and ;(array1p 'test-case-stobj test-case-stobj)
             (bounded-darg-listp args bound)
             (all-< WORKLIST bound))
           (all-< (mv-nth 0 (add-args-not-done-in-test-case-stobj args worklist worklist-extendedp test-case-stobj))
                  bound))
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

(defthm true-listp-of-mv-nth-0-of-add-args-not-done-in-test-case-stobj
  (implies (true-listp worklist)
           (true-listp (mv-nth 0 (add-args-not-done-in-test-case-stobj args worklist worklist-extendedp test-case-stobj))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

;; once it's true, it stays true
(defthm mv-nth-1-of-add-args-not-done-in-test-case-stobj-of-t
  (mv-nth 1 (add-args-not-done-in-test-case-stobj args worklist t test-case-stobj))
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

(defthm mv-nth-0-of-add-args-not-done-in-test-case-stobj-when-not-mv-nth-1-of-add-args-not-done-in-test-case-stobj
  (implies (not (mv-nth 1 (add-args-not-done-in-test-case-stobj args worklist worklist-extendedp test-case-stobj)))
           (equal (mv-nth 0 (add-args-not-done-in-test-case-stobj args worklist worklist-extendedp test-case-stobj))
                  worklist))
  :hints (("Goal" :in-theory (enable add-args-not-done-in-test-case-stobj))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Returns (mv erp test-case-stobj), where TEST-CASE-STOBJ will have values for each node that is relevant (supports the nodes in the initial work-list) on this test case (note that because of ifs, the set of relevant nodes can differ between test cases).  nodes that have had their values set in TEST-CASE-STOBJ will be associated with t in the DONE NODES ARRAY.
;; TODO: If there are no ifs (of any kind) in the dag, it would probably be faster (and safe) to just evaluate every node in order.
;; TODO: Consider adding short-circuit evaluation for booland and boolor (I guess always evaluate the first argument and sometimes evaluate the second argument).
(defund evaluate-test-case-simple-aux (count ; forces termination (todo: try having two kinds of :examined status for IF nodes (whether the test has been pushed, whether the relevant branch has been pushed), and base a measure on that
                                       nodenum-worklist
                                       dag-array-name dag-array dag-len
                                       test-case ; gives values for variables
                                       interpreted-function-alist
                                       test-case-stobj)
  (declare (xargs ;; :measure (make-ord 1 (+ 1 (- (nfix (alen1 'done-nodes-array done-nodes-array))
             ;;                              (num-true-nodes (+ -1 (alen1 'done-nodes-array done-nodes-array))
             ;;                                              'done-nodes-array done-nodes-array)))
             ;;                    (len nodenum-worklist))
             :guard (and (natp count)
                         (nat-listp nodenum-worklist)
                         (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                         (all-< nodenum-worklist dag-len)
                         (equal (node-val-array-length test-case-stobj) dag-len)
                         (equal (done-node-array-length test-case-stobj) dag-len)
                         (test-casep test-case)
                         (interpreted-function-alistp interpreted-function-alist))
             :guard-hints (("Goal" :in-theory (e/d (cadr-becomes-nth-of-1
                                                    consp-of-cdr test-casep)
                                                   (natp))))
             :stobjs test-case-stobj))
  (if (zp count)
      (prog2$ (er hard? 'evaluate-test-case-simple-aux "Limit reached.")
              (mv :limit-reached test-case-stobj))
    (if (endp nodenum-worklist)
        (mv (erp-nil) test-case-stobj)
      (let ((nodenum (first nodenum-worklist)))
        (if (done-node-arrayi nodenum test-case-stobj)
            ;;it's possible that the node became done while this copy of its nodenum was sitting on the worklist (it was pushed again and processed, while this copy of it was still sitting there)
            (evaluate-test-case-simple-aux (+ -1 count) (rest nodenum-worklist) dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)
          ;;the node is not yet done:
          (let ((expr (aref1 dag-array-name dag-array nodenum)))
            (if (variablep expr)
                (b* ((entry (assoc-eq expr test-case))
                     (- (if (not entry)
                            (cw "WARNING: No entry for ~x0 in alist.~%" expr) ;previously this was an error
                          nil))
                     (value (cdr entry))
                     (test-case-stobj (update-node-val-arrayi nodenum value test-case-stobj))
                     (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                  (evaluate-test-case-simple-aux (+ -1 count)
                                          (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                          interpreted-function-alist test-case-stobj))
              (let ((fn (ffn-symb expr)))
                (if (eq 'quote fn)
                    (let* ((value (unquote expr))
                           (test-case-stobj (update-node-val-arrayi nodenum value test-case-stobj))
                           (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                      (evaluate-test-case-simple-aux (+ -1 count)
                                              (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                              interpreted-function-alist test-case-stobj))
                  ;;function call or if (clean this up?)
                  (let ((dargs (dargs expr)))
                    (if (or (eq 'if fn)
                            (eq 'myif fn))
                        (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                      :logic (<= 3 (len dargs)))) ; for guard proof
                            (prog2$ (er hard? 'evaluate-test-case-simple-aux "Arity mismatch: ~x0" expr)
                                    (mv :arity-mismatch test-case-stobj))
                          ;; It's an IF/MYIF, so only evaluate the branch we need:
                          (let* ((test (first dargs))
                                 (test-quotep (consp test))
                                 (test-done (or test-quotep
                                                (done-node-arrayi test test-case-stobj))))
                            (if (not test-done)
                                ;;will reanalyze the IF/MYIF node once the test is evaluated:
                                (evaluate-test-case-simple-aux (+ -1 count)
                                                        (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        interpreted-function-alist test-case-stobj)
                              ;;we know the result of the test, so handle the relevant branch
                              (let* ((test-val (if test-quotep
                                                   (unquote test)
                                                 (node-val-arrayi test test-case-stobj)))
                                     (relevant-branch (if test-val (second dargs) (third dargs)))
                                     (quotep-relevant-branch (consp relevant-branch))
                                     (relevant-branch-done (or quotep-relevant-branch
                                                               (done-node-arrayi relevant-branch test-case-stobj))))
                                (if (not relevant-branch-done)
                                    ;;will reanalyze the IF/MYIF again after once the relevant branch is evaluated:
                                    (evaluate-test-case-simple-aux (+ -1 count)
                                                            (cons relevant-branch nodenum-worklist) dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)
                                  ;; if the relevant branch has been computed, the value of the IF/MYIF is just that branch
                                  (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                   (unquote relevant-branch)
                                                                  (node-val-arrayi relevant-branch test-case-stobj)))
                                         (test-case-stobj (update-node-val-arrayi nodenum relevant-branch-value test-case-stobj))
                                         (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                                    (evaluate-test-case-simple-aux (+ -1 count)
                                                            (rest nodenum-worklist)
                                                            dag-array-name dag-array dag-len test-case
                                                            interpreted-function-alist test-case-stobj)))))))
                      (if (eq 'boolif fn)
                          (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                        :logic (<= 3 (len dargs))))
                              (prog2$ (er hard? 'evaluate-test-case-simple-aux "Arity mismatch: ~x0" expr)
                                      (mv :arity-mismatch test-case-stobj))
                            ;; It's a BOOLIF so only evaluate the branch we need:
                            (let* ((test (first dargs))
                                   (test-quotep (consp test))
                                   (test-done (or test-quotep
                                                  (done-node-arrayi test test-case-stobj))))
                              (if (not test-done)
                                  ;;will reanalyze the BOOLIF node once the test is evaluated:
                                  (evaluate-test-case-simple-aux (+ -1 count)
                                                          (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                          interpreted-function-alist test-case-stobj )
                                ;;we know the result of the test, so handle the relevant branch
                                (let* ((test-val (if test-quotep
                                                     (unquote test)
                                                   (node-val-arrayi test test-case-stobj)))
                                       (relevant-branch (if test-val (second dargs) (third dargs)))
                                       (quotep-relevant-branch (consp relevant-branch))
                                       (relevant-branch-done (or quotep-relevant-branch
                                                                 (done-node-arrayi relevant-branch test-case-stobj))))
                                  (if (not relevant-branch-done)
                                      ;;will reanalyze the BOOLIF node once the relevant branch is evaluated:
                                      (evaluate-test-case-simple-aux (+ -1 count)
                                                              (cons relevant-branch nodenum-worklist) dag-array-name
                                                              dag-array dag-len test-case interpreted-function-alist test-case-stobj)
                                    ;; if the relevant branch has been computed, the value of the BOOLIF is just that branch,
                                    ;; except that we have to bvchop/bool-fix it
                                    (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                      (unquote relevant-branch)
                                                                    (node-val-arrayi relevant-branch test-case-stobj)))
                                           (value (bool-fix relevant-branch-value))
                                           (test-case-stobj (update-node-val-arrayi nodenum value test-case-stobj))
                                           (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                                      (evaluate-test-case-simple-aux (+ -1 count)
                                                              (rest nodenum-worklist)
                                                              dag-array-name dag-array dag-len test-case
                                                              interpreted-function-alist test-case-stobj)))))))
                        (if (eq 'bvif fn)
                            (if (not (mbe :exec (consp (cdr (cdr (cdr dargs))))
                                          :logic (<= 4 (len dargs))))
                                (prog2$ (er hard? 'evaluate-test-case-simple-aux "Arity mismatch: ~x0" expr)
                                        (mv :arity-mismatch test-case-stobj))
                              ;; It's a BVIF, so only evaluate the branch we need:
                              (let* ((test (second dargs))
                                     (test-quotep (consp test))
                                     (test-done (or test-quotep
                                                    (done-node-arrayi test test-case-stobj))))
                                (if (not test-done)
                                    ;;will reanalyze the BVIF node once the test is evaluated:
                                    (evaluate-test-case-simple-aux (+ -1 count)
                                                            (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                            interpreted-function-alist test-case-stobj)
                                  ;;we know the result of the test, so handle the relevant branch
                                  (let* ((test-val (if test-quotep
                                                       (unquote test)
                                                     (node-val-arrayi test test-case-stobj)))
                                         (relevant-branch (if test-val (third dargs) (fourth dargs)))
                                         (quotep-relevant-branch (consp relevant-branch))
                                         (relevant-branch-done (or quotep-relevant-branch
                                                                   (done-node-arrayi relevant-branch test-case-stobj))))
                                    (if (not relevant-branch-done)
                                        ;;will reanalyze the BVIF node once the relevant branch is evaluated:
                                        (evaluate-test-case-simple-aux (+ -1 count)
                                                                (cons relevant-branch nodenum-worklist) dag-array-name
                                                                dag-array dag-len test-case interpreted-function-alist test-case-stobj)
                                      ;; if the relevant branch has been computed, the value of the BVIF is just that branch,
                                      ;; except that we have to bvchop it
                                      (let* ((size-not-done (let ((size (first dargs)))
                                                              (not (or (consp size)
                                                                       (done-node-arrayi size test-case-stobj))))))
                                        (if size-not-done
                                            ;;will reanalyze the BVIF node once the size arg. is evaluated: ; TODO: Handle the size and the test together
                                            (evaluate-test-case-simple-aux (+ -1 count)
                                                                    (cons (first dargs) nodenum-worklist) dag-array-name
                                                                    dag-array dag-len test-case interpreted-function-alist test-case-stobj)
                                          (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                            (unquote relevant-branch)
                                                                          (node-val-arrayi relevant-branch test-case-stobj)))
                                                 (value (bvchop (nfix ; justified by bvchop-of-nfix
                                                                  (let ((size (first dargs)))
                                                                    (if (consp size)
                                                                        (unquote size)
                                                                      (node-val-arrayi size test-case-stobj))))
                                                                (ifix ; justified by bvchop-of-ifix
                                                                  relevant-branch-value)))
                                                 (test-case-stobj (update-node-val-arrayi nodenum value test-case-stobj))
                                                 (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                                            (evaluate-test-case-simple-aux (+ -1 count)
                                                                    (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                                    interpreted-function-alist test-case-stobj)))))))))
                          ;;regular function call:
                          (mv-let (nodenum-worklist worklist-extendedp)
                            (add-args-not-done-in-test-case-stobj dargs nodenum-worklist nil test-case-stobj)
                            (if worklist-extendedp
                                ;;will reanalyze this node once the args are done:
                                (evaluate-test-case-simple-aux (+ -1 count)
                                                        nodenum-worklist ;has been extended
                                                        dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)
                              ;;the args are done, so call the function:
                              (b* ((arg-values (get-vals-of-dargs-in-test-case-stobj dargs test-case-stobj))
                                   ((mv erp value) (apply-axe-evaluator-basic fn arg-values interpreted-function-alist 0))
                                   ;; ((mv erp value) (apply-axe-evaluator-basic fn arg-values interpreted-function-alist 1000000000))
                                   ((when erp) (er hard? 'evaluate-test-case-simple-aux "Error (~x0) evaluating: call to ~x1 on ~x2." erp fn arg-values)
                                    (mv :error-evaluating test-case-stobj))
                                   (test-case-stobj (update-node-val-arrayi nodenum value test-case-stobj))
                                   (test-case-stobj (update-done-node-arrayi nodenum t test-case-stobj)))
                                (evaluate-test-case-simple-aux (+ -1 count)
                                                        (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        interpreted-function-alist  test-case-stobj)))))))))))))))))



(local
  (defthm test-case-stobjp-of-mv-nth-1-of-evaluate-test-case-simple-aux
    (implies (and (natp count)
                  (nat-listp nodenum-worklist)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (all-< nodenum-worklist dag-len)
                  (equal (node-val-array-length test-case-stobj) dag-len)
                  (equal (done-node-array-length test-case-stobj) dag-len)
                  (test-casep test-case)
                  (interpreted-function-alistp interpreted-function-alist)
                  (test-case-stobjp test-case-stobj))
             (test-case-stobjp (mv-nth 1 (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))))
    :hints (("Goal"
             :induct t
             :expand ((:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
                      (:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux 0 nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
             :in-theory (e/d ((:i evaluate-test-case-simple-aux) ; avoids opening more than once, for speed
                              cadr-becomes-nth-of-1
                              consp-of-cdr)
                             (natp use-all-rationalp-for-car
                                   nfix ifix ;; these greatly reduce case splits
                                   ))))))

(local
  (defthm node-val-array-length-of-mv-nth-1-of-evaluate-test-case-simple-aux
    (implies (and (natp count)
                  (nat-listp nodenum-worklist)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (all-< nodenum-worklist dag-len)
                  (equal (node-val-array-length test-case-stobj) dag-len)
                  (equal (done-node-array-length test-case-stobj) dag-len)
                  (test-casep test-case)
                  (interpreted-function-alistp interpreted-function-alist)
                  ;(test-case-stobjp test-case-stobj)
                  )
             (equal (node-val-array-length (mv-nth 1 (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
                    (node-val-array-length test-case-stobj)))
    :hints (("Goal"
             :induct t
             :expand ((:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
                      (:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux 0 nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
             :in-theory (e/d ((:i evaluate-test-case-simple-aux) ; avoids opening more than once
                              cadr-becomes-nth-of-1
                              consp-of-cdr)
                             (natp use-all-rationalp-for-car
                                   nfix ifix ;; these greatly reduce case splits
                                   ))))))

(local
  (defthm done-node-array-length-of-mv-nth-1-of-evaluate-test-case-simple-aux
    (implies (and (natp count)
                  (nat-listp nodenum-worklist)
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (all-< nodenum-worklist dag-len)
                  (equal (node-val-array-length test-case-stobj) dag-len)
                  (equal (done-node-array-length test-case-stobj) dag-len)
                  (symbol-alistp test-case)
                  (interpreted-function-alistp interpreted-function-alist)
                  ;(test-case-stobjp test-case-stobj)
                  )
             (equal (done-node-array-length (mv-nth 1 (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
                    (done-node-array-length test-case-stobj)))
    :hints (("Goal"
             :induct t
             :expand ((:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux count nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
                      (:free (dag-len nodenum-worklist test-case) (evaluate-test-case-simple-aux 0 nodenum-worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
             :in-theory (e/d ((:i evaluate-test-case-simple-aux) ; avoids opening more than once
                              cadr-becomes-nth-of-1
                              consp-of-cdr)
                             (natp use-all-rationalp-for-car
                                   nfix ifix ;; these greatly reduce case splits
                                   ))))))

;; Returns (mv erp test-case-stobj) where the test-case-stobj, which has an array (node-val-array) assigning
;; vals to relevant nodes for the test-case and an array (done-node-array)
;; indicating which notes were used on the test case.  TEST-CASE gives values
;; to the vars in the dag.
(defund evaluate-test-case-simple (dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (test-casep test-case)
                              (interpreted-function-alistp interpreted-function-alist))
                  :stobjs test-case-stobj))
  (b* ((max-nodenum (+ -1 dag-len))
       ;; Clear the done bits:
       (test-case-stobj (resize-done-node-array dag-len test-case-stobj))
       (test-case-stobj (set-done-vals-to-nil max-nodenum test-case-stobj)) ; todo: clear less, if resizing made it bigger
       ;; No need to clear out the node-val-array values as all node vals will be set when needed (according to the done-array):
       (test-case-stobj (resize-node-val-array dag-len test-case-stobj))
       (worklist (list max-nodenum))
       ((mv erp test-case-stobj)
        (evaluate-test-case-simple-aux 1000000000 ; todo
                                       worklist dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj))
       ((when erp) (mv erp test-case-stobj)))
    (mv (erp-nil) test-case-stobj)))

(defthm done-node-array-length-of-mv-nth-1-of-evaluate-test-case-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                (test-casep test-case)
                (interpreted-function-alistp interpreted-function-alist))
           (equal (done-node-array-length (mv-nth 1 (evaluate-test-case-simple dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
                  dag-len))
  :hints (("Goal" :in-theory (enable evaluate-test-case-simple))))

(defthm node-val-array-length-of-mv-nth-1-of-evaluate-test-case-simple
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                (test-casep test-case)
                (interpreted-function-alistp interpreted-function-alist))
           (equal (node-val-array-length (mv-nth 1 (evaluate-test-case-simple dag-array-name dag-array dag-len test-case interpreted-function-alist test-case-stobj)))
                  dag-len))
  :hints (("Goal" :in-theory (enable evaluate-test-case-simple))))
