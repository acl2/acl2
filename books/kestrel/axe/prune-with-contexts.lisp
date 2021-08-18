; A utility to remove unreachable if-branches using contexts
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(include-book "dag-array-builders")
(include-book "contexts")
(include-book "renaming-array")
(include-book "make-dag-indices")
(include-book "def-dag-builder-theorems")
(include-book "supporting-nodes")
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))

(local (in-theory (disable natp member-equal len)))

(local (in-theory (enable <-of-+-of-minus1-arith-hack
                          natp-of-+-of-1)))

(defthm dargp-of-if
  (equal (dargp (if test tp ep))
         (if test
             (dargp tp)
           (dargp ep))))

(defthm wf-dagp-of-make-empty-array-and-make-dag-parent-array-with-name2-of-make-empty-array
  (implies (and (posp size)
                (<= size *maximum-1-d-array-length*))
           (wf-dagp 'dag-array
                    (make-empty-array 'dag-array size)
                    '0
                    'dag-parent-array
                    (make-dag-parent-array-with-name2
                     '0
                     'dag-array
                     (make-empty-array 'dag-array size)
                     'dag-parent-array)
                    'nil
                    'nil))
  :hints (("Goal" :in-theory (enable wf-dagp))))

;; given:
;;  context array
;;  old dag-array (alt name)
;;  new dag-array (and aux structures?) (standard name)
;;  renaming-array from old to new
;; move nodes from old dag-array to new-dag-array, except resolve ifs
;; given an if: get its context.  try to extend the context with the test, and with the negation of the test.  replace with the (renamed) then/else branch as appropriate.  if handling bvif/boolif, may have to build some fresh nodes that do the fixing (maybe skip if we can tell it's not needed from the type).  maybe handle boolor/booland (in general, any boolean node).  the context analysis will re-do some work already done when determining how contexts propagate from the if to its childern.
;; Returns (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
(defund prune-with-contexts-aux (old-nodenum ; counts up
                                 old-dag-array
                                 old-dag-len
                                 context-array ;for the old dag
                                 ;; the new dag:
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 renaming-array ;maps nodes already seen in old-dag-array to new nodes in dag-array
                                 )
  (declare (xargs :guard (and (natp old-nodenum)
                              (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (pseudo-dag-arrayp 'old-dag-array old-dag-array old-dag-len)
                              ;; everything in the renaming array up through old-nodenum-1 maps to a valid node in the new dag:
                              (bounded-renaming-arrayp 'renaming-array renaming-array old-nodenum dag-len)
                              (equal (alen1 'renaming-array renaming-array)
                                     old-dag-len)
                              (context-arrayp 'context-array context-array old-dag-len))
                  :guard-hints (("Goal" :in-theory (enable
                                                    bounded-renaming-arrayp ;todo
                                                    rename-darg ;todo
                                                    dargp-rules)))
                  :measure (nfix (+ 1 (- old-dag-len old-nodenum)))))
  (if (or (not (and (mbt (natp old-nodenum))
                    (mbt (natp old-dag-len))))
          (>= old-nodenum old-dag-len))
      (mv (erp-nil) renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (let ((expr (aref1 'old-dag-array old-dag-array old-nodenum)))
      (if (atom expr)
          (b* (((mv erp nodenum dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (add-variable-to-dag-array expr dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               ((when erp)
                (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               (renaming-array (aset1 'renaming-array renaming-array old-nodenum nodenum)))
            (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                     dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                     renaming-array))
        (let ((fn (ffn-symb expr)))
          (case fn
            (quote
             ;; expr is a quoted constant:
             (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      ;; This node maps to a constant (so it will get inlined):
                                      (aset1 'renaming-array renaming-array old-nodenum expr)
                                      ))
            ((if myif)
             ;; expr is a call of if or myif:
             (if (not (= 3 (len (dargs expr)))) ; should never happen
                 (mv :bad-arity-for-if-or-myif renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               ;; Try to resolve the test of the if/myif
               (let ((resolved-test ; will be :true, :false, or :unknown
                      (let* ((test-darg (darg1 expr))
                             (renamed-test (if (consp test-darg) ;test for quotep (rare)
                                               test-darg ;don't attempt to rename
                                             (rename-darg test-darg 'renaming-array renaming-array))))
                        (if (consp renamed-test) ; test for quotep
                            (if (unquote renamed-test)
                                :true
                              :false)
                          ;; test wasn't renamed to a constant, so try to use the context:
                          (let* ((context (aref1 'context-array context-array old-nodenum))
                                 (context-with-test (conjoin-contexts (context-representing-node test-darg 'old-dag-array old-dag-array old-dag-len)
                                                                      context)))
                            (if (false-contextp context-with-test)
                                ;; test is known to be false (assuming the context):
                                :false
                              (let* ((context-with-negated-test (conjoin-contexts (context-representing-negation-of-node test-darg 'old-dag-array old-dag-array old-dag-len)
                                                                                  context)))
                                (if (false-contextp context-with-negated-test)
                                    ;; test is known to be true (assuming the context):
                                    :true
                                  :unknown))))))))
                 (if (eq :false resolved-test)
                     ;; test is known to be false (assuming the context), so replace with (renamed) else branch:
                     (let* ((else-darg (darg3 expr))
                            (renamed-else-darg (if (consp else-darg) ; test for quotep
                                                   else-darg
                                                 (rename-darg else-darg 'renaming-array renaming-array)))
                            ;; This node maps to its (renamed) else branch:
                            (renaming-array (aset1 'renaming-array renaming-array old-nodenum renamed-else-darg)))
                       (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                renaming-array))
                   (if (eq :true resolved-test)
                       ;; test is known to be true (assuming the context), so replace with (renamed) then branch:
                       (let* ((then-darg (darg2 expr))
                              (renamed-then-darg (if (consp then-darg) ; test for quotep
                                                     then-darg
                                                   (rename-darg then-darg 'renaming-array renaming-array)))
                              ;; This node maps to its (renamed) then branch:
                              (renaming-array (aset1 'renaming-array renaming-array old-nodenum renamed-then-darg)))
                         (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                  renaming-array))
                     ;; Couldn't resolve test:
                     (b* ((renamed-args (rename-args (dargs expr) 'renaming-array renaming-array))
                          ((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                           (add-function-call-expr-to-dag-array2 fn renamed-args dag-array dag-len dag-parent-array dag-constant-alist))
                          ((when erp)
                           (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                          (renaming-array (aset1 'renaming-array renaming-array old-nodenum new-nodenum)))
                       (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                renaming-array)))))))
            ;; todo: add support for bvif? boolif? booland? boolor? not?
            (t ;; Normal function (nothing to resolve):
             (b* ((renamed-args (rename-args (dargs expr) 'renaming-array renaming-array))
                  ((mv erp new-nodenum dag-array dag-len dag-parent-array dag-constant-alist)
                   (add-function-call-expr-to-dag-array2 fn renamed-args dag-array dag-len dag-parent-array dag-constant-alist))
                  ((when erp)
                   (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                  (renaming-array (aset1 'renaming-array renaming-array old-nodenum new-nodenum)))
               (prune-with-contexts-aux (+ 1 old-nodenum) old-dag-array old-dag-len context-array
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        renaming-array)))))))))

;; (defthm <=-of-mv-nth-2-of-prune-with-contexts-aux-linear
;;   (implies (and (not (mv-nth 0 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
;;                 (natp old-nodenum)
;;                 (natp old-dag-len))
;;            (<= old-dag-len
;;                (mv-nth 2 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
;;            )
;;   :rule-classes :linear
;;   :hints (("Goal" :in-theory (enable prune-with-contexts-aux))))

;(local (in-theory (enable renaming-arrayp))) ;todo

(def-dag-builder-theorems (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
  (mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps (;; (natp old-nodenum)
         (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
         (pseudo-dag-arrayp 'old-dag-array old-dag-array old-dag-len)
         (renaming-arrayp 'renaming-array renaming-array old-nodenum)
         (equal (alen1 'renaming-array renaming-array)
                old-dag-len)
         (bounded-renaming-entriesp (+ -1 old-nodenum) 'renaming-array renaming-array dag-len)
         (context-arrayp 'context-array context-array old-dag-len)))

(defthm renaming-arrayp-of-mv-nth-1-of-prune-with-contexts-aux
  (implies (and (not (mv-nth 0 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
                ;;(<= old-nodenum old-dag-len)
                (natp old-nodenum)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (pseudo-dag-arrayp 'old-dag-array old-dag-array old-dag-len)
                (bounded-renaming-arrayp 'renaming-array renaming-array old-nodenum dag-len)
                ;(renaming-arrayp 'renaming-array renaming-array old-nodenum)
                (equal (alen1 'renaming-array renaming-array)
                       old-dag-len)
                (context-arrayp 'context-array context-array old-dag-len))
           (renaming-arrayp 'renaming-array
                            (mv-nth 1 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                            old-dag-len))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
           :in-theory (enable PRUNE-WITH-CONTEXTS-AUX
                              ;;rename-args
                              bounded-renaming-arrayp ;todo
                              ))))

(defthm bounded-renaming-arrayp-of-mv-nth-1-of-prune-with-contexts-aux
  (implies (and (not (mv-nth 0 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
                ;;(<= old-nodenum old-dag-len)
                (natp old-nodenum)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (pseudo-dag-arrayp 'old-dag-array old-dag-array old-dag-len)
                (bounded-renaming-arrayp 'renaming-array renaming-array old-nodenum dag-len)
                ;(renaming-arrayp 'renaming-array renaming-array old-nodenum)
                (equal (alen1 'renaming-array renaming-array)
                       old-dag-len)
                (context-arrayp 'context-array context-array old-dag-len))
           (bounded-renaming-arrayp 'renaming-array
                                    (mv-nth 1 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))
                                    old-dag-len
                                    (mv-nth 3 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
           :in-theory (enable PRUNE-WITH-CONTEXTS-AUX
                              ;;rename-args
                              bounded-renaming-arrayp ;todo
                              ))))

(defthm bounded-renaming-entriesp-of-mv-nth-1-of-prune-with-contexts-aux
  (implies (and (not (mv-nth 0 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)))
                (<= old-nodenum old-dag-len)
                (natp old-nodenum)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (pseudo-dag-arrayp 'old-dag-array old-dag-array old-dag-len)
                (bounded-renaming-arrayp 'renaming-array renaming-array old-nodenum dag-len)
                ;;(renaming-arrayp 'renaming-array renaming-array old-nodenum)
                (equal (alen1 'renaming-array renaming-array)
                       old-dag-len)
                (context-arrayp 'context-array context-array old-dag-len))
           (bounded-renaming-entriesp (+ -1 old-dag-len)
                                      'renaming-array
                                      (mv-nth 1 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))

                                      (mv-nth 3 (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (prune-with-contexts-aux old-nodenum old-dag-array old-dag-len context-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist renaming-array)
           :in-theory (enable PRUNE-WITH-CONTEXTS-AUX
                              ;;rename-args
                              bounded-renaming-arrayp ;todo
                              ))))

;; ;; Returns (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; (defund prune-with-contexts (dag
;;                              context-array ;must be the context computed from dag
;;                              )
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               (context-arrayp 'context-array context-array (+ 1 (top-nodenum-of-dag dag))))
;;                   :guard-hints (("Goal" :in-theory (enable wf-dagp len-when-pseudo-dagp)))))
;;   (b* ((old-dag-len (+ 1 (top-nodenum-of-dag dag)))
;;        (old-dag-array (make-into-array-with-len 'old-dag-array dag old-dag-len)) ; no slack needed since this won't grow
;;        (renaming-array (make-empty-array 'renaming-array old-dag-len)) ;will rename nodes in old dag to nodes in the new dag
;;        ;;todo: make a util for making an empty dag and its aux structures
;;        (dag-array (make-empty-array 'dag-array old-dag-len)) ;todo: leave some slack space?
;;        (dag-len 0)
;;        ;; make aux structures for new dag:
;;        ((mv dag-parent-array dag-constant-alist dag-variable-alist)
;;         (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len)))
;; need to drop-non-supporters
;;     (prune-with-contexts-aux 0
;;                              old-dag-array
;;                              old-dag-len
;;                              context-array ;for the old dag
;;                              ;; the new dag:
;;                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                              renaming-array ;maps nodes already seen in old-dag-array to new nodes in dag-array
;;                              )))

;todo: track whether a change was made.  if not, can reuse the dag-array, etc. and context-array

(local (in-theory (enable <-OF-+-OF-1-STRENGTHEN-2)))

;; Returns (mv erp dag-or-quotep).
(defund prune-with-contexts (dag)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (< (top-nodenum-of-dag dag)
                                 *maximum-1-d-array-length*))
                  :guard-hints (("Goal" :in-theory (enable ;wf-dagp len-when-pseudo-dagp top-nodenum-of-dag
                                                    )))))
  (b* ((old-dag-len (+ 1 (top-nodenum-of-dag dag)))
       (old-dag-array (make-into-array-with-len 'old-dag-array dag old-dag-len)) ; no slack needed since this won't grow
       ;; Make the auxiliary data structures for the DAG:
       ((mv old-dag-parent-array
            & ;dag-constant-alist (todo: don't generate)
            & ;dag-variable-alist (todo: don't generate)
            )
        (make-dag-indices 'old-dag-array old-dag-array 'dag-parent-array old-dag-len)) ;note the old-dag-parent-array has name 'dag-parent-array (todo: generalize make-full-context-array-with-parents below?)
       ;; Now figure out the context we can use for each node
       ;; TODO: If this doesn't contain any information, consider skipping the prune
       (context-array (make-full-context-array-with-parents 'old-dag-array old-dag-array old-dag-len old-dag-parent-array))
       ;; ((when ...) ; could check here whether there is any context information to use
       ;;  (and print (cw ")~%"))
       ;;  (mv (erp-nil) dag limits state))

       (renaming-array (make-empty-array 'renaming-array old-dag-len)) ;will rename nodes in old dag to nodes in the new dag
       ;;todo: make a util for making an empty dag and its aux structures
       (dag-array (make-empty-array 'dag-array old-dag-len)) ;todo: leave some slack space?
       (dag-len 0)
       ;; make aux structures for new dag:
       ((mv dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len))
       ((mv erp renaming-array dag-array
            dag-len
            & & & ;dag-parent-array dag-constant-alist dag-variable-alist ; todo: save time by not making these?
            )
        (prune-with-contexts-aux 0
                                 old-dag-array
                                 old-dag-len
                                 context-array ;for the old dag
                                 ;; the new dag:
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                 renaming-array ;maps nodes already seen in old-dag-array to new nodes in dag-array
                                 ))
       ((when erp) (mv erp nil))
       ((when (< dag-len 1)) ;todo: prove that this can't happen
        (mv :bad-dag-len nil))
       (new-top-nodenum-or-quotep (rename-darg (top-nodenum-of-dag dag) 'renaming-array renaming-array)))
    (if (consp new-top-nodenum-or-quotep) ;check for quotep
        (mv (erp-nil)
            new-top-nodenum-or-quotep)
      (mv (erp-nil)
          (drop-non-supporters-array 'dag-array dag-array new-top-nodenum-or-quotep nil)))))

;; Pruning either returns a dag or a quoted constant
(defthm pseudo-dagp-of-prune-with-contexts
  (implies (and (not (mv-nth 0 (prune-with-contexts dag)))
                (pseudo-dagp dag)
                (< (top-nodenum-of-dag dag)
                   *maximum-1-d-array-length*))
           (equal (pseudo-dagp (mv-nth 1 (prune-with-contexts dag)))
                  (not (myquotep (mv-nth 1 (prune-with-contexts dag))))))
  :hints (("Goal" :in-theory (enable prune-with-contexts
                                     dargp-rules))))


;; (defthm wf-dagp-after-prune-with-contexts2
;;   (implies (and (pseudo-dagp dag)
;;                 (< (top-nodenum-of-dag dag)
;;                    *maximum-1-d-array-length*)
;;                 (not (mv-nth 0 (prune-with-contexts2 dag))) ;no error
;;                 )
;;            (wf-dagp 'dag-array
;;                     (mv-nth 1 (prune-with-contexts2 dag))
;;                     (mv-nth 2 (prune-with-contexts2 dag))
;;                     'dag-parent-array
;;                     (mv-nth 3 (prune-with-contexts2 dag))
;;                     (mv-nth 4 (prune-with-contexts2 dag))
;;                     (mv-nth 5 (prune-with-contexts2 dag))))
;;   :hints (("Goal" :in-theory (enable prune-with-contexts2
;;                                      top-nodenum-of-dag
;;                                      len-when-pseudo-dagp))))

;; todo: this is currently not really appropriate since the function doesn't take the dag-array as an arg:
;; (def-dag-builder-theorems (prune-with-contexts2 dag)
;;   (mv erp dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;   :hyps ((pseudo-dagp dag)
;;          (< (top-nodenum-of-dag dag)
;;             *maximum-1-d-array-length*))
;;   :hyps-everywhere t
;;   :recursivep nil
;;   :hints (("Goal" :in-theory (enable prune-with-contexts2 wf-dagp top-nodenum-of-dag LEN-WHEN-PSEUDO-DAGP))))
