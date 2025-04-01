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

(include-book "dag-arrays")
(include-book "test-cases")
(include-book "evaluator") ; for apply-axe-evaluator ; todo: use basic eval but need to evaluate dag-val-with-axe-evaluator in examples like rc4-loop, make this file a generator that takes an evaluator?
(include-book "kestrel/booleans/bool-fix" :dir :system) ; do not remove
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove
(include-book "kestrel/bv/bvif" :dir :system) ; do not remove
(include-book "kestrel/acl2-arrays/aset1-safe" :dir :system) ; todo: drop once we no longer call aset1-safe below
(include-book "kestrel/acl2-arrays/print-array" :dir :system)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "numeric-lists"))
(local (include-book "rational-lists"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local (in-theory (e/d (true-listp-of-cdr-strong)
                       (true-listp-of-cdr
                        symbol-alistp))))

;args are nodenums and/or quoteps
;;returns (mv worklist worklist-extendedp) where nodenum-worklist has been extended by any args to compute (non quoteps not marked done)
;; and worklist-extendedp indicates whether there were any such args
;rename?
;; Could combine with get-args-not-done-array?  But this one has the array name baked in.
(defund add-args-not-done (dargs done-nodes-array worklist worklist-extendedp)
  (declare (xargs :guard (and (array1p 'done-nodes-array done-nodes-array)
                              (bounded-darg-listp dargs (alen1 'done-nodes-array done-nodes-array)))))
  (if (endp dargs)
      (mv worklist worklist-extendedp)
    (let ((arg (first dargs)))
      (if (or (consp arg) ; skip quoted constants
              (aref1 'done-nodes-array done-nodes-array arg) ;;skip dargs that are marked as done
              )
          (add-args-not-done (rest dargs) done-nodes-array worklist worklist-extendedp)
        (add-args-not-done (rest dargs) done-nodes-array (cons arg worklist) t ;we've extended the worklist
                           )))))

;; (local
;;   (defthm add-args-not-done-of-nil-arg1
;;     (equal (add-args-not-done nil done-nodes-array worklist worklist-extendedp)
;;            (mv worklist worklist-extendedp))
;;     :hints (("Goal" :in-theory (enable add-args-not-done)))))

(local
  (defthm nat-listp-of-mv-nth-0-of-add-args-not-done
    (implies (and ;(array1p 'done-nodes-array done-nodes-array)
               (darg-listp args) ; (bounded-darg-listp args (alen1 'done-nodes-array done-nodes-array))
               (NAT-LISTP WORKLIST))
             (nat-listp (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))))
    :hints (("Goal" :in-theory (enable add-args-not-done)))))

(local
  (defthm all-<-of-mv-nth-0-of-add-args-not-done
    (implies (and ;(array1p 'done-nodes-array done-nodes-array)
               (bounded-darg-listp args bound)
               (all-< WORKLIST bound))
             (all-< (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))
                    bound))
    :hints (("Goal" :in-theory (enable add-args-not-done)))))

(local
  (defthm true-listp-of-mv-nth-0-of-add-args-not-done
    (implies (true-listp worklist)
             (true-listp (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable add-args-not-done)))))

;; once it's true, it stays true
(local
  (defthm mv-nth-1-of-add-args-not-done-of-t
    (mv-nth 1 (add-args-not-done args done-nodes-array worklist t))
    :hints (("Goal" :in-theory (enable add-args-not-done)))))

(local
  (defthm mv-nth-0-of-add-args-not-done-when-not-mv-nth-1-of-add-args-not-done
    (implies (not (mv-nth 1 (add-args-not-done args done-nodes-array worklist worklist-extendedp)))
             (equal (mv-nth 0 (add-args-not-done args done-nodes-array worklist worklist-extendedp))
                    worklist))
    :hints (("Goal" :in-theory (enable add-args-not-done)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;args are nodenums with values in the array, or quoteps
;looks up the nodenums and unquotes the constants
;does similar functionality exist elsewhere (array names might differ)?
(defund get-vals-of-args (dargs test-case-array-name test-case-array)
  (declare (xargs :guard (and (array1p test-case-array-name test-case-array)
                              (bounded-darg-listp dargs (alen1 test-case-array-name test-case-array)))))
  (if (endp dargs)
      nil
    (let ((darg (first dargs)))
      (cons (if (consp darg) ; check for quoted constant
                (unquote darg)
              ;;otherwise it's a nodenum:
              (aref1 test-case-array-name test-case-array darg))
            (get-vals-of-args (rest dargs) test-case-array-name test-case-array)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns test-case-array, which has the name test-case-array-name.
;; TODO: Instead of using the special value :unused, consider tracking that information in a separate array.
;;todo: this seems inefficient for very sparse tests.
(defund tag-not-done-nodes-as-unused (current-nodenum done-nodes-array test-case-array test-case-array-name)
  (declare (xargs :guard (and (integerp current-nodenum)
                              (array1p test-case-array-name test-case-array)
                              (array1p 'done-nodes-array done-nodes-array)
                              (< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                              (< current-nodenum (alen1 test-case-array-name test-case-array)))
                  :hints (("Goal" :in-theory (enable natp)))
                  :measure (nfix (+ 1 current-nodenum))))
  (if (not (natp current-nodenum))
      test-case-array
    (let* ((donep (aref1 'done-nodes-array done-nodes-array current-nodenum)))
      (if donep
          (tag-not-done-nodes-as-unused (+ -1 current-nodenum) done-nodes-array test-case-array test-case-array-name)
        (tag-not-done-nodes-as-unused (+ -1 current-nodenum) done-nodes-array
                                      (aset1-safe test-case-array-name test-case-array current-nodenum :unused)
                                      test-case-array-name)))))

(local
 (defthm array1p-of-tag-not-done-nodes-as-unused
   (implies (and (integerp current-nodenum)
                 (array1p test-case-array-name test-case-array)
                 ;(array1p 'done-nodes-array done-nodes-array)
                 ;(< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                 (< current-nodenum (alen1 test-case-array-name test-case-array)))
            (array1p test-case-array-name (tag-not-done-nodes-as-unused current-nodenum done-nodes-array test-case-array test-case-array-name)))
   :hints (("Goal" :in-theory (enable tag-not-done-nodes-as-unused)))))

(local
 (defthm alen1-of-tag-not-done-nodes-as-unused
   (implies (and ;(integerp current-nodenum)
                 ;(array1p test-case-array-name test-case-array)
                 ;(array1p 'done-nodes-array done-nodes-array)
                 ;(< current-nodenum (alen1 'done-nodes-array done-nodes-array))
                 (< current-nodenum (alen1 test-case-array-name test-case-array))
                 )
            (equal (alen1 test-case-array-name (tag-not-done-nodes-as-unused current-nodenum done-nodes-array test-case-array test-case-array-name))
                   (alen1 test-case-array-name test-case-array)))
   :hints (("Goal" :in-theory (enable tag-not-done-nodes-as-unused)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund print-vals-of-nodes (nodenums array-name array)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (array1p array-name array)
                              (all-< nodenums (alen1 array-name array)))))
  (if (endp nodenums)
      nil
    (prog2$ (cw "Node ~x0 is ~x1.~%" (first nodenums) (aref1 array-name array (car nodenums)))
            (print-vals-of-nodes (rest nodenums) array-name array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv test-case-array done-nodes-array), where TEST-CASE-ARRAY will have values for each node that is relevant (supports the nodes in the initial work-list) on this test case (note that because of ifs, the set of relevant nodes can differ between test cases).  nodes that have had their values set in TEST-CASE-ARRAY will be associated with t in DONE-NODES-ARRAY
;; We could speed this up using stobj arrays, but note that in some cases we return all the test-case-arrays.
;; TODO: If there are no ifs (of any kind) in the dag, it would probably be faster (and safe) to just evaluate every node in order.
;; TODO: Consider adding short-circuit evaluation for booland and boolor (I guess always evaluate the first argument and sometimes evaluate the second argument).
(defund evaluate-test-case-aux (count ; forces termination (todo: try having two kinds of :examined status for IF nodes (whether the test has been pushed, whether the relevant branch has been pushed), and base a measure on that
                                nodenum-worklist
                                dag-array-name dag-array dag-len
                                test-case ; gives values for variables
                                test-case-array
                                done-nodes-array
                                interpreted-function-alist test-case-array-name)
  (declare (xargs ;; :measure (make-ord 1 (+ 1 (- (nfix (alen1 'done-nodes-array done-nodes-array))
            ;;                              (num-true-nodes (+ -1 (alen1 'done-nodes-array done-nodes-array))
            ;;                                              'done-nodes-array done-nodes-array)))
            ;;                    (len nodenum-worklist))
            :guard (and (natp count)
                        (nat-listp nodenum-worklist)
                        (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                        (all-< nodenum-worklist dag-len)
                        (array1p test-case-array-name test-case-array)
                        (equal (alen1 test-case-array-name test-case-array) dag-len)
                        (array1p 'done-nodes-array done-nodes-array)
                        (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                        (symbol-alistp test-case)
                        (interpreted-function-alistp interpreted-function-alist))
            :guard-hints (("Goal" :in-theory (e/d (cadr-becomes-nth-of-1
                                                   consp-of-cdr)
                                                  (natp))))))
  (if (zp count)
      (prog2$ (er hard? 'evaluate-test-case-aux "Limit reached.")
              (mv test-case-array done-nodes-array))
    (if (endp nodenum-worklist)
        (mv test-case-array done-nodes-array)
      (let ((nodenum (first nodenum-worklist)))
        (if (aref1 'done-nodes-array done-nodes-array nodenum)
            ;;it's possible that the node became done while this copy of its nodenum was sitting on the worklist (it was pushed again and processed, while this copy of it was still sitting there)
            (evaluate-test-case-aux (+ -1 count) (rest nodenum-worklist) dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
          ;;the node is not yet done:
          (let ((expr (aref1 dag-array-name dag-array nodenum)))
            (if (variablep expr)
                (b* ((entry (assoc-eq expr test-case))
                     (- (if (not entry)
                            (cw "WARNING: No entry for ~x0 in alist.~%" expr) ;previously this was an error
                          nil))
                     (value (cdr entry)))
                  (evaluate-test-case-aux (+ -1 count)
                                          (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                          (aset1 test-case-array-name test-case-array nodenum value)
                                          (aset1 'done-nodes-array done-nodes-array nodenum t)
                                          interpreted-function-alist test-case-array-name))
              (let ((fn (ffn-symb expr)))
                (if (eq 'quote fn)
                    (let ((value (unquote expr)))
                      (evaluate-test-case-aux (+ -1 count)
                                              (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                              (aset1 test-case-array-name test-case-array nodenum value)
                                              (aset1 'done-nodes-array done-nodes-array nodenum t)
                                              interpreted-function-alist test-case-array-name))
                  ;;function call or if (clean this up?)
                  (let ((dargs (dargs expr)))
                    (if (or (eq 'if fn)
                            (eq 'myif fn))
                        (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                      :logic (<= 3 (len dargs)))) ; for guard proof
                            (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                    (mv test-case-array done-nodes-array))
                          ;; It's an IF/MYIF, so only evaluate the branch we need:
                          (let* ((test (first dargs))
                                 (test-quotep (consp test))
                                 (test-done (or test-quotep
                                                (aref1 'done-nodes-array done-nodes-array test))))
                            (if (not test-done)
                                ;;will reanalyze the IF/MYIF node once the test is evaluated:
                                (evaluate-test-case-aux (+ -1 count)
                                                        (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                              ;;we know the result of the test, so handle the relevant branch
                              (let* ((test-val (if test-quotep
                                                   (unquote test)
                                                 (aref1 test-case-array-name test-case-array test)))
                                     (relevant-branch (if test-val (second dargs) (third dargs)))
                                     (quotep-relevant-branch (consp relevant-branch))
                                     (relevant-branch-done (or quotep-relevant-branch
                                                               (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                (if (not relevant-branch-done)
                                    ;;will reanalyze the IF/MYIF again after once the relevant branch is evaluated:
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (cons relevant-branch nodenum-worklist) dag-array-name
                                                            dag-array dag-len test-case test-case-array done-nodes-array
                                                            interpreted-function-alist test-case-array-name)
                                  ;; if the relevant branch has been computed, the value of the IF/MYIF is just that branch
                                  (let ((relevant-branch-value (if quotep-relevant-branch
                                                                   (unquote relevant-branch)
                                                                 (aref1 test-case-array-name test-case-array relevant-branch))))
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (rest nodenum-worklist)
                                                            dag-array-name dag-array dag-len
                                                            test-case
                                                            (aset1 test-case-array-name test-case-array nodenum relevant-branch-value)
                                                            (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                            interpreted-function-alist test-case-array-name)))))))
                      (if (eq 'boolif fn)
                          (if (not (mbe :exec (consp (cdr (cdr dargs)))
                                        :logic (<= 3 (len dargs))))
                              (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                      (mv test-case-array done-nodes-array))
                            ;; It's a BOOLIF so only evaluate the branch we need:
                            (let* ((test (first dargs))
                                   (test-quotep (consp test))
                                   (test-done (or test-quotep
                                                  (aref1 'done-nodes-array done-nodes-array test))))
                              (if (not test-done)
                                  ;;will reanalyze the BOOLIF node once the test is evaluated:
                                  (evaluate-test-case-aux (+ -1 count)
                                                          (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                          test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                                ;;we know the result of the test, so handle the relevant branch
                                (let* ((test-val (if test-quotep
                                                     (unquote test)
                                                   (aref1 test-case-array-name test-case-array test)))
                                       (relevant-branch (if test-val (second dargs) (third dargs)))
                                       (quotep-relevant-branch (consp relevant-branch))
                                       (relevant-branch-done (or quotep-relevant-branch
                                                                 (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                  (if (not relevant-branch-done)
                                      ;;will reanalyze the BOOLIF node once the relevant branch is evaluated:
                                      (evaluate-test-case-aux (+ -1 count)
                                                              (cons relevant-branch nodenum-worklist) dag-array-name
                                                              dag-array dag-len test-case test-case-array done-nodes-array
                                                              interpreted-function-alist test-case-array-name)
                                    ;; if the relevant branch has been computed, the value of the BOOLIF is just that branch,
                                    ;; except that we have to bvchop/bool-fix it
                                    (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                      (unquote relevant-branch)
                                                                    (aref1 test-case-array-name test-case-array relevant-branch)))
                                           (value (bool-fix relevant-branch-value)))
                                      (evaluate-test-case-aux (+ -1 count)
                                                              (rest nodenum-worklist)
                                                              dag-array-name dag-array dag-len test-case
                                                              (aset1 test-case-array-name test-case-array nodenum value)
                                                              (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                              interpreted-function-alist test-case-array-name)))))))
                        (if (eq 'bvif fn)
                            (if (not (mbe :exec (consp (cdr (cdr (cdr dargs))))
                                          :logic (<= 4 (len dargs))))
                                (prog2$ (er hard? 'evaluate-test-case-aux "Arity mismatch: ~x0" expr)
                                        (mv test-case-array done-nodes-array))
                              ;; It's a BVIF, so only evaluate the branch we need:
                              (let* ((test (second dargs))
                                     (test-quotep (consp test))
                                     (test-done (or test-quotep
                                                    (aref1 'done-nodes-array done-nodes-array test))))
                                (if (not test-done)
                                    ;;will reanalyze the BVIF node once the test is evaluated:
                                    (evaluate-test-case-aux (+ -1 count)
                                                            (cons test nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                            test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
                                  ;;we know the result of the test, so handle the relevant branch
                                  (let* ((test-val (if test-quotep
                                                       (unquote test)
                                                     (aref1 test-case-array-name test-case-array test)))
                                         (relevant-branch (if test-val (third dargs) (fourth dargs)))
                                         (quotep-relevant-branch (consp relevant-branch))
                                         (relevant-branch-done (or quotep-relevant-branch
                                                                   (aref1 'done-nodes-array done-nodes-array relevant-branch))))
                                    (if (not relevant-branch-done)
                                        ;;will reanalyze the BVIF node once the relevant branch is evaluated:
                                        (evaluate-test-case-aux (+ -1 count)
                                                                (cons relevant-branch nodenum-worklist) dag-array-name
                                                                dag-array dag-len test-case test-case-array done-nodes-array
                                                                interpreted-function-alist test-case-array-name)
                                      ;; if the relevant branch has been computed, the value of the BVIF is just that branch,
                                      ;; except that we have to bvchop it
                                      (let* ((size-not-done (let ((size (first dargs)))
                                                              (not (or (consp size)
                                                                       (aref1 'done-nodes-array done-nodes-array size))))))
                                        (if size-not-done
                                            ;;will reanalyze the BVIF node once the size arg. is evaluated: ; TODO: Handle the size and the test together
                                            (evaluate-test-case-aux (+ -1 count)
                                                                    (cons (first dargs) nodenum-worklist) dag-array-name
                                                                    dag-array dag-len test-case test-case-array done-nodes-array
                                                                    interpreted-function-alist test-case-array-name)
                                          (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                            (unquote relevant-branch)
                                                                          (aref1 test-case-array-name test-case-array relevant-branch)))
                                                 (value (bvchop (nfix ; justified by bvchop-of-nfix
                                                                 (let ((size (first dargs)))
                                                                   (if (consp size)
                                                                       (unquote size)
                                                                     (aref1 test-case-array-name test-case-array size))))
                                                                (ifix ; justified by bvchop-of-ifix
                                                                 relevant-branch-value))))
                                            (evaluate-test-case-aux (+ -1 count)
                                                                    (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                                    (aset1 test-case-array-name test-case-array nodenum value)
                                                                    (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                                    interpreted-function-alist test-case-array-name)))))))))
                          ;;regular function call:
                          (mv-let (nodenum-worklist worklist-extendedp)
                            (add-args-not-done dargs done-nodes-array nodenum-worklist nil)
                            (if worklist-extendedp
                                ;;will reanalyze this node once the args are done:
                                (evaluate-test-case-aux (+ -1 count)
                                                        nodenum-worklist ;has been extended
                                                        dag-array-name dag-array dag-len test-case test-case-array
                                                        done-nodes-array interpreted-function-alist test-case-array-name)
                              ;;the args are done, so call the function:
                              (b* ((arg-values (get-vals-of-args dargs test-case-array-name test-case-array))
                                   (value (apply-axe-evaluator fn arg-values interpreted-function-alist 0))
                                   ;; ((mv erp value) (apply-axe-evaluator-basic fn arg-values interpreted-function-alist 1000000000))
                                   ;; ((when erp) (er hard? 'evaluate-test-case-aux "Error (~x0) evaluating: ~x1" erp expr)
                                   ;;  (mv test-case-array done-nodes-array))
                                   )
                                (evaluate-test-case-aux (+ -1 count)
                                                        (rest nodenum-worklist) dag-array-name dag-array dag-len test-case
                                                        (aset1 test-case-array-name test-case-array nodenum value)
                                                        (aset1 'done-nodes-array done-nodes-array nodenum t)
                                                        interpreted-function-alist
                                                        test-case-array-name)))))))))))))))))

(local
 (defthm array1p-of-mv-nth-0-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 test-case-array-name test-case-array) dag-len))
            (array1p test-case-array-name
                     (mv-nth 0 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name))))
   :hints (("Goal"
            :induct t
            :expand ((:free (dag-len nodenum-worklist) (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once, for speed
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp use-all-rationalp-for-car
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm alen1-of-mv-nth-0-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (array1p test-case-array-name test-case-array)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 test-case-array-name test-case-array) dag-len))
            (equal (alen1 test-case-array-name (mv-nth 0 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
                   (alen1 test-case-array-name test-case-array)))
   :hints (("Goal"
            :induct t
            :expand ((:free (dag-len nodenum-worklist) (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp use-all-rationalp-for-car
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm array1p-of-mv-nth-1-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                 (array1p 'done-nodes-array done-nodes-array))
            (array1p 'done-nodes-array
                     (mv-nth 1 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name))))
   :hints (("Goal"
            :induct t
            :expand ((:free (dag-len nodenum-worklist) (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp use-all-rationalp-for-car
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

(local
 (defthm alen1-of-mv-nth-1-of-evaluate-test-case-aux
   (implies (and (nat-listp nodenum-worklist)
                 (all-< nodenum-worklist dag-len)
                 (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                 (equal (alen1 'done-nodes-array done-nodes-array) dag-len)
                 (array1p 'done-nodes-array done-nodes-array))
            (equal (alen1 'done-nodes-array (mv-nth 1 (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
                   (alen1 'done-nodes-array done-nodes-array)))
   :hints (("Goal"
            :induct t
            :expand ((:free (dag-len nodenum-worklist) (evaluate-test-case-aux count nodenum-worklist dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)))
            :in-theory (e/d ((:i evaluate-test-case-aux) ; avoids opening more than once
                             cadr-becomes-nth-of-1
                             consp-of-cdr)
                            (natp use-all-rationalp-for-car
                                  nfix ifix ;; these greatly reduce case splits
                                  ))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns TEST-CASE-ARRAY, which has the name TEST-CASE-ARRAY-NAME and which has values for each node that supports any node in NODES-TO-EVAL for this test case (different test cases may evaluate the ifs differently)
; TEST-CASE-ARRAY will associate irrelevant nodes with the value :unused - FFIXME what if a node actually evaluates to :unused?  could return done-nodes-array (but if we are keeping several done-node-arrays we might want to give them different names paralleling the test case array names)
;; todo: count and print the number of nodes that are not :unused
(defund evaluate-test-case (nodes-to-eval ; we'll find values for all of these nodes
                            dag-array-name dag-array
                            test-case
                            interpreted-function-alist
                            test-case-array-name)
  (declare (xargs :guard (and (nat-listp nodes-to-eval)
                              (consp nodes-to-eval) ; must be at least one node, so we can find the max
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                              (test-casep test-case)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbolp test-case-array-name))))
  (let* ((max-nodenum (maxelem nodes-to-eval))
         (dag-len (+ 1 max-nodenum)) ; the effective length of the dag, for the purposes of this test case
         ;;would it be faster to reuse this array and just clear it out here?
         (test-case-array (make-empty-array test-case-array-name dag-len))
         ;;would it be faster to reuse this array and just clear it out here?
         (done-nodes-array (make-empty-array 'done-nodes-array dag-len)))
    (mv-let (test-case-array done-nodes-array)
      (evaluate-test-case-aux 1000000000 ; todo
                              nodes-to-eval ;initial worklist
                              dag-array-name dag-array dag-len test-case test-case-array done-nodes-array interpreted-function-alist test-case-array-name)
      ;; todo: can we avoid this step? just return the done-nodes-array?  or use :unused as the default value of the array?
      (tag-not-done-nodes-as-unused max-nodenum done-nodes-array test-case-array test-case-array-name))))

;; non-local, since evaluate-test-case is called in equivalence-checker.lisp
(defthm array1p-of-evaluate-test-case
  (implies (and (nat-listp nodes-to-eval)
                (consp nodes-to-eval) ; must be at least one node, so we can find the max
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                (symbolp test-case-array-name))
           (array1p test-case-array-name (evaluate-test-case nodes-to-eval dag-array-name dag-array test-case interpreted-function-alist test-case-array-name)))
  :hints (("Goal" :in-theory (enable evaluate-test-case))))

;; non-local, since evaluate-test-case is called in equivalence-checker.lisp
(defthm alen1-of-evaluate-test-case
  (implies (and (nat-listp nodes-to-eval)
                (consp nodes-to-eval) ; must be at least one node, so we can find the max
                (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodes-to-eval)))
                (symbolp test-case-array-name))
           (equal (alen1 test-case-array-name (evaluate-test-case nodes-to-eval dag-array-name dag-array test-case interpreted-function-alist test-case-array-name))
                  (+ 1 (maxelem nodes-to-eval))))
  :hints (("Goal" :in-theory (enable evaluate-test-case))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If the test passes (top node evaluated to T), this returns TEST-CASE-ARRAY, which
;; has a value for each node that supports the top node for this test (and
;; :unused for other nodes) and which has name TEST-CASE-ARRAY-NAME.  If the
;; test fails, this returns nil.
(defund evaluate-and-check-test-case (test-case
                                      dag-array-name dag-array dag-len
                                      interpreted-function-alist
                                      test-case-array-name
                                      debug-nodes ; nodes whose values we want to print for each test case
                                      )
  (declare (xargs :guard (and (test-casep test-case)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< 0 dag-len)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbolp test-case-array-name)
                              (nat-listp debug-nodes)
                              (all-< debug-nodes dag-len))))
  (let* ((top-nodenum (+ -1 dag-len))
         (test-case-array
           (evaluate-test-case (list top-nodenum) dag-array-name dag-array test-case interpreted-function-alist test-case-array-name))
         (top-node-value (aref1 test-case-array-name test-case-array top-nodenum)))
    (if (eq t top-node-value) ; TODO: Consider relaxing this to allow any non-nil value.
        (prog2$ (print-vals-of-nodes debug-nodes test-case-array-name test-case-array)
                test-case-array)
      ;; todo: return an error flag and catch it later?
      (progn$ (cw "!!!! We found a test case that does not evaluate to true:~%")
              (cw "Test case: ~x0~%" test-case)
              (print-array test-case-array-name test-case-array dag-len) ;this can be big!
              (er hard? 'evaluate-and-check-test-case "Untrue test case (see above)")
              nil))))

(defthm array1p-of-evaluate-and-check-test-case
  (implies (and (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes) ; no error
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                (symbolp test-case-array-name))
           (array1p test-case-array-name (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes)))
  :hints (("Goal" :in-theory (enable evaluate-and-check-test-case))))

(defthm alen1-of-evaluate-and-check-test-case
  (implies (and (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes) ; no error
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (< 0 dag-len)
                (symbolp test-case-array-name))
           (equal (alen1 test-case-array-name (evaluate-and-check-test-case test-case dag-array-name dag-array dag-len interpreted-function-alist test-case-array-name debug-nodes))
                  dag-len))
  :hints (("Goal" :in-theory (enable evaluate-and-check-test-case))))
