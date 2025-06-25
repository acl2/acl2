; Pruning irrelevant IF-branches in a DAG
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This utility tries to resolve IF/MYIF/BOOLIF/BVIF tests in the dag, using STP and the contexts of the nodes.

;; TODO: Add the ability to rewrite IF tests when pruning.

(include-book "prove-with-stp")
(include-book "rewriter-basic") ; just for the post-rewrite
(include-book "./cars-increasing-by-1")
(include-book "dag-size-fast")
(include-book "basic-rules")
(include-book "rule-lists") ; for unsigned-byte-p-forced-rules
(include-book "bv-rules-axe") ; for bvchop-identity-axe
(include-book "kestrel/booleans/booleans" :dir :system) ; for MYIF-OF-BOOL-FIX-ARG1
(include-book "kestrel/bv/rules" :dir :system) ; todo: reduce, for the unsigned-byte-p-forced rules
(include-book "kestrel/bv/sbvrem" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced-rules" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-rules" :dir :system)
(include-book "kestrel/utilities/if" :dir :system) ; for rules mentioned below
(include-book "kestrel/utilities/myif-def" :dir :system) ; do not remove (since this book knows about myif)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove (since this book knows about boolif)
(include-book "kestrel/booleans/bool-fix" :dir :system) ; do not remove (since this book knows about bool-fix$inline)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)
(include-book "merge-term-into-dag-array-simple")
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "cars-decreasing-by-1"))
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/integer-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable state-p natp w
                           ;; for speed:
                           use-all-rationalp-for-car
                           consp-from-len-cheap
                           default-+-2
                           default-cdr
                           member-equal
                           nat-listp ; prevent induction
                           ilks-plist-worldp)))

;move:

;; ;; Checks that DAG is a true-list of pairs of the form (<nodenum> . <bounded-dag-expr>).
;; (defund bounded-weak-dagp-aux (dag bound)
;;   (declare (xargs :guard (natp bound)))
;;   (if (atom dag)
;;       (null dag)
;;     (let ((entry (car dag)))
;;       (and (consp entry)
;;            (let* ((nodenum (car entry))
;;                   (expr (cdr entry)))
;;              (and (natp nodenum)
;;                   (< nodenum bound)
;;                   (bounded-dag-exprp nodenum expr)
;;                   (bounded-weak-dagp-aux (cdr dag) bound)))))))

;; (defthm weak-dagp-aux-when-bounded-weak-dagp-aux
;;   (implies (bounded-weak-dagp-aux dag bound) ; free var
;;            (weak-dagp-aux dag))
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux
;;                                      weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-of-cdr
;;   (implies (bounded-weak-dagp-aux dag bound)
;;            (bounded-weak-dagp-aux (cdr dag) bound))
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-forward-to-alistp
;;   (implies (bounded-weak-dagp-aux dag bound)
;;            (alistp dag))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux alistp))))

;; (defthm bounded-weak-dagp-aux-when-pseudo-dagp-aux
;;   (implies (and (pseudo-dagp-aux dag n)
;;                 (< n bound)
;;                 (natp n)
;;                 (natp bound))
;;            (bounded-weak-dagp-aux dag bound))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-weak-dagp-aux))))

;; (defthm bounded-weak-dagp-aux-of-len-when-pseudo-dagp
;;   (implies (pseudo-dagp dag)
;;            (bounded-weak-dagp-aux dag (len dag)))
;;   :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux bounded-weak-dagp-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When the test of an IF or MYIF can be resolved, the IF/MYIF can be replaced
;; by a call of ID around either its then-branch or its else-branch.  This
;; ensures the resulting DAG is still legal and has no changes in node
;; numbering.  The calls to ID can be removed by a subsequent call of the
;; rewriter.  TODO: Do better?
(defun id (x) x)

;move
(defund prune-dag-post-rewrite-rules ()
  (declare (xargs :guard t))
  (append
  '(id
    bool-fix-when-booleanp ; todo: add more booleanp rules, or even pass them in?
    bool-fix-of-bool-fix
    boolif-of-bool-fix-arg1
    boolif-of-bool-fix-arg2
    boolif-of-bool-fix-arg3
    if-of-bool-fix-arg1
    myif-of-bool-fix-arg1
    bvif-of-bool-fix
    not-of-bool-fix
    boolor-of-bool-fix-arg1
    boolor-of-bool-fix-arg2
    booland-of-bool-fix-arg1
    booland-of-bool-fix-arg2
    booleanp-of-bool-fix-rewrite
    if-same-branches
    if-when-non-nil-constant
    if-of-nil
    ;; if-of-not ; maybe
    if-of-t-and-nil-when-booleanp ; or bool-fix it
    myif-same-branches
    myif-of-nil
    myif-of-constant-when-not-nil
    myif-nil-t
    myif-of-t-and-nil-when-booleanp
    ;; todo: more rules?  try the bv-function-of-bvchop-rules?
    bvchop-identity-axe
    )
  (unsigned-byte-p-forced-rules)
  ;; todo: add rules like bvif-of-bvchop-arg3 (make a rule-list for them)
  ;; (bv-function-of-bvchop-rules) ;; hmmm, maybe we should pass in these rules?
  ))

(ensure-rules-known (prune-dag-post-rewrite-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These justify the pruning done by prune-dag-approximately-aux:
(thm (implies test (equal (myif test x y) (if test x y)))) ; myif can be treated just like if
(thm (implies test (equal (if test x y) (id x))))
(thm (implies test (equal (myif test x y) (id x))))
(thm (implies (not test) (equal (if test x y) (id y))))
(thm (implies (not test) (equal (myif test x y) (id y))))
(thm (implies test (equal (boolif test x y) (bool-fix$inline x))))
(thm (implies (not test) (equal (boolif test x y) (bool-fix$inline y))))
(thm (implies test (equal (bvif size test x y) (bvchop size x))))
(thm (implies (not test) (equal (bvif size test x y) (bvchop size y))))

;; Returns (mv erp dag state).
;; Recreates DAG, pruning as it goes.  May insert calls to ID, BOOL-FIX$INLINE, and BVCHOP but does not change any node numbering.
;; The dag-array does not change.
(defund prune-dag-approximately-aux (dag
                                     original-dag-len ; without the assumptions; the context array only covers nodenums less than this
                                     assumption-nodenums
                                     dag-array dag-len dag-parent-array context-array print max-conflicts
                                     dag-acc ;reverse order (lower nodenums first)
                                     state)
  (declare (xargs :guard (and (or (null dag)
                                  (pseudo-dagp dag))
                              (natp original-dag-len)
                              (if (null dag)
                                  t
                                (< (car (first dag)) original-dag-len))
                              (nat-listp assumption-nodenums)
                              ;; can't call wf-dagp because we don't have the dag-variable-alist and dag-constant-alist.
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (all-< assumption-nodenums dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (<= original-dag-len dag-len) ;drop?
                              (bounded-context-arrayp 'context-array context-array original-dag-len original-dag-len)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (weak-dagp-aux dag-acc) ; ignores the order
                              (cars-increasing-by-1 dag-acc)
                              (if (and (consp dag)
                                       (consp dag-acc))
                                  (equal (car (first dag-acc)) (+ 1 (car (first dag))))
                                t))
                  :guard-hints (("Goal" ;:expand (bounded-weak-dagp-aux dag dag-len)
                                 ;; :expand (pseudo-dagp dag) ; caused a loop
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d (;pseudo-dagp-aux
                                                  true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
                                                  car-of-car-when-pseudo-dagp
                                                  symbolp-of-car-when-dag-exprp)
                                                 (weak-dagp-aux myquotep))))
                  :stobjs state))
  (if (endp dag)
      (mv (erp-nil) (reverse-list dag-acc) state)
    (let* ((entry (first dag))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (atom expr) ; variable (nothing to do):
          (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)
        (let ((fn (ffn-symb expr)))
          (case fn
            ;; quoted constant (nothing to do):
            (quote (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))
            ((if myif) ; (if/myif test then-branch else-branch)
             (b* (((when (not (consp (cdr (cdr (dargs expr))))))
                   (mv :bad-if-arity nil state))
                  ;; Get the context for this IF/MYIF node (note that its test node may appear in other contexts too):
                  (context (conjoin-contexts (aref1 'context-array context-array nodenum)
                                             assumption-nodenums))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   ;; We use a wrapper of ID here (and below) to ensure the node is
                   ;; still legal (not a naked nodenum) and to preserve the node
                   ;; numbering (calls to ID will later be removed by rewriting):
                   (let ((expr `(id ,(darg2 expr))))
                     (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
                  ;; Try to resolve the IF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-darg-with-stp (darg1 expr) ; the test of the IF/MYIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  (expr (if (eq result :true)
                            `(id ,(darg2 expr)) ; the IF/MYIF is equal to its then-branch
                          (if (eq result :false)
                              `(id ,(darg3 expr)) ; the IF/MYIF is equal to its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            ((boolif) ; (boolif test then-branch else-branch)
             (b* (((when (not (consp (cdr (cdr (dargs expr))))))
                   (mv :bad-boolif-arity nil state))
                  ;; Get the context for this BOOLIF node (note that its test node may appear in other contexts too):
                  (context (conjoin-contexts (aref1 'context-array context-array nodenum)
                                             assumption-nodenums))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (let ((expr `(bool-fix$inline ,(darg2 expr))))
                     (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
                  ;; Try to resolve the BOOLIF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-darg-with-stp (darg1 expr) ; the test of the BOOLIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; Even if we can resolve the test, we have to keep the
                  ;; bool-fixing.  This also ensures the node is still legal
                  ;; (not a naked nodenum) and preserves the node numbering
                  ;; (calls to bool-fix$inline will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(bool-fix$inline ,(darg2 expr)) ; the BOOLIF is equal to the bool-fix of its then-branch
                          (if (eq result :false)
                              `(bool-fix$inline ,(darg3 expr)) ; the BOOLIF is equal to the bool-fix of its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            ((bvif) ; (bvif size test then-branch else-branch)
             (b* (((when (not (consp (cdddr (dargs expr)))))
                   (mv :bad-bvif-arity nil state))
                  ;; Get the context for this BVIF node (note that its test node may appear in other contexts too):
                  (context (conjoin-contexts (aref1 'context-array context-array nodenum)
                                             assumption-nodenums))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (let ((expr `(bvchop ,(darg1 expr) ,(darg3 expr))))
                     (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
                  ;; Try to resolve the BVIF test:
                  ((mv erp result state)
                   ;; TODO: What if the test is among the context assumptions?
                   ;; TODO: Should we use any rewriting here?
                   (try-to-resolve-darg-with-stp (darg2 expr) ; the test of the BVIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; Even if we can resolve the test, we have to keep the
                  ;; chopping.  This also ensures the node is still legal
                  ;; (not a naked nodenum) and preserves the node numbering
                  ;; (calls to bvchop will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(bvchop ,(darg1 expr) ,(darg3 expr)) ; the BVIF is equal to the bvchop of its then-branch
                          (if (eq result :false)
                              `(bvchop ,(darg1 expr) ,(darg4 expr)) ; the BVIF is equal to the bvchop of its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            (t
             (prune-dag-approximately-aux (rest dag) original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))))))))

(local
 (defthmd pseudo-dagp-aux-of-top-nodenum-of-dag-when-weak-dagp-aux-and-cars-decreasing-by-1
   (implies (and (consp dag)
                 (cars-decreasing-by-1 dag)
                 (equal 0 (car (car (last dag))))
                 (weak-dagp-aux dag))
            (pseudo-dagp-aux dag (top-nodenum-of-dag dag)))
   :hints (("Goal" :induct (weak-dagp-aux dag)
            :in-theory (enable cars-decreasing-by-1 weak-dagp-aux pseudo-dagp-aux top-nodenum-of-dag)))))

(local
 (defthm prune-dag-approximately-aux-return-type
   (implies (and ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
;;                 (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                 ;; (equal (alen1 'dag-parent-array dag-parent-array)
                 ;;        (alen1 'dag-array dag-array))
                 (or (null dag)
                     (pseudo-dagp dag))
                 ;; (bounded-context-arrayp 'context-array context-array original-dag-len original-dag-len)
                 ;; (or (null max-conflicts)
                 ;;     (natp max-conflicts))
                 (weak-dagp-aux dag-acc) ; ignores the order
                 (cars-increasing-by-1 dag-acc)
                 (if (and (consp dag)
                          (consp dag-acc))
                     (equal (car (first dag-acc)) (+ 1 (car (first dag))))
                   t)
                 (or (consp dag) (consp dag-acc)) ; at least one of them is a cons
                 (if (not (consp dag))
                     (equal (car (first dag-acc)) 0)
                   t))
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)
              (declare (ignore state))
              (implies (not erp)
                       (and (cars-decreasing-by-1 new-dag)
                            (weak-dagp-aux new-dag)
                            (consp new-dag)
                            (equal (car (car (last new-dag))) 0)))))
   :rule-classes nil
   :hints (("Goal" :induct t
            :expand ((prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print nil dag-acc state)
                     (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print nil nil state))
            :in-theory (e/d (prune-dag-approximately-aux
                             true-listp-of-dargs-of-cdr-of-car-when-pseudo-dagp-type
                             car-of-car-when-pseudo-dagp
                             integer-listp-of-strip-cars-when-weak-dagp-aux)
                            (nth
                             len-of-cdr
                             member-equal
                             weak-dagp-aux
                             myquotep))))))

;special case of dag-acc=nil, as it will be initially
(local
 (defthm prune-dag-approximately-aux-return-type-special
   (implies (and ;;(pseudo-dag-arrayp 'dag-array dag-array dag-len)
                 ;;(bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                 ;; (equal (alen1 'dag-parent-array dag-parent-array)
                 ;;        (alen1 'dag-array dag-array))
                 (pseudo-dagp dag)
 ;                (<= (len dag) dag-len)
;                 (bounded-context-arrayp 'context-array context-array original-dag-len original-dag-len)
                 ;; (or (null max-conflicts)
                 ;;     (natp max-conflicts))
                 ;(consp dag)
                 )
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts nil state)
              (declare (ignore state))
              (implies (not erp)
                       (and (cars-decreasing-by-1 new-dag)
                            (weak-dagp-aux new-dag)
                            (consp new-dag)
                            (equal (car (car (last new-dag))) 0)))))
   :hints (("Goal" :use (:instance prune-dag-approximately-aux-return-type (dag-acc nil))))))

(local
 (defthm prune-dag-approximately-aux-return-type-special-corollary
   (implies (and (pseudo-dagp dag)
;                 (consp dag)
                 )
            (mv-let (erp new-dag state)
              (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts nil state)
              (declare (ignore state))
              (implies (not erp)
                       (pseudo-dagp new-dag))))
   :hints (("Goal" :use (prune-dag-approximately-aux-return-type-special
                         (:instance pseudo-dagp-aux-of-top-nodenum-of-dag-when-weak-dagp-aux-and-cars-decreasing-by-1
                                    (dag (mv-nth 1 (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts nil state)))))
            :in-theory (e/d (pseudo-dagp top-nodenum-of-dag) (prune-dag-approximately-aux-return-type-special))))))

(local
 (defthm w-of-mv-nth-2-of-prune-dag-approximately-aux
   (equal (w (mv-nth 2 (prune-dag-approximately-aux dag original-dag-len assumption-nodenums dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
          (w state))
   :hints (("Goal" :in-theory (enable prune-dag-approximately-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp dag-or-quotep state).
;; Smashes the arrays named 'dag-array, 'temp-dag-array, and 'context-array.
;; todo: may need multiple passes, but watch for loops!
;; todo: optimize in the common case when nothing is changed
(defund prune-dag-approximately (dag
                                 assumptions
                                 ;; rules ; todo: add support for this
                                 ;; interpreted-fns
                                 ;; monitored-rules
                                 ;;call-stp
                                 print
                                 max-conflicts
                                 state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              ;(<= (len dag) *max-1d-array-length*)
                              (pseudo-term-listp assumptions)
                              ;; (symbol-listp rules)
                              ;; (symbol-listp interpreted-fns)
                              ;; (symbol-listp monitored-rules)
                              ;; (call-stp-optionp call-stp)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (ilks-plist-worldp (w state)))
                  :guard-hints (("Goal" :in-theory (enable car-of-car-when-pseudo-dagp)))
                  :stobjs state))
  (b* (((when (> (top-nodenum-of-dag dag) *max-1d-array-index*)) (mv :dag-too-big dag state))
       (- (cw "(Pruning DAG with approx. contexts (~x0 nodes, ~x1 unique):~%" (dag-or-quotep-size-fast dag) (len dag)))
       (old-dag dag)
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ;; Generate the (approximate) contexts:
       (context-array (make-full-context-array-for-dag dag))
       ;; Make the dag into an array and make the 3 indices:
       (dag-array (make-into-array 'dag-array dag))
       (original-dag-len (+ 1 (top-nodenum-of-dag dag)))
       ((mv dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices 'dag-array dag-array 'dag-parent-array original-dag-len))
       ;; Add the assumptions:
       ;; TOOD: Consider allowing the result to contain negated nodenums, for assumptions that are negations.
       ((mv erp assumption-nodenums-or-quoteps dag-array dag-len dag-parent-array
            & & ; dag-constant-alist dag-variable-alist
            )
        (merge-terms-into-dag-array-simple (keep-smt-assumptions assumptions) ; filter out non-SMT assumptions, which can be large, like (equal (read-bytes ..) ...manybytes...)
                                           nil ; var-replacement-alist
                                           dag-array original-dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array))
       ((when erp) (mv erp dag state))
       ;; Filter out constant assumptions:
       (assumption-nodenums (append-nodenum-dargs assumption-nodenums-or-quoteps nil))
       ;; Do the pruning:
       ((mv erp dag state) ; cannot be a quotep?
        (prune-dag-approximately-aux dag
                                     original-dag-len
                                     assumption-nodenums
                                     dag-array dag-len dag-parent-array ; these do not get changed
                                     context-array
                                     print
                                     max-conflicts
                                     nil   ; dag-acc
                                     state))
       ((when erp) (mv erp old-dag state))
       ;; Ensure we can continue with the processing below:
       ((when (> (top-nodenum-of-dag dag) *max-1d-array-index*)) (mv :dag-too-big old-dag state))
       ;; There may be orphan nodes if some pruning was done:
       (dag-or-quotep (drop-non-supporters dag))
       ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
       (dag dag-or-quotep) ; it's not a quotep
       ;; Get rid of any calls to ID that got introduced during pruning (TODO: skip if there were none):
       ;; Similarly, try to get rid of calls of BVCHOP and BOOL-FIX$INLINE that got introduced.
       ;; And try to propagate successful resolution of tests upward in the DAG.
       ((mv erp rule-alist) (make-rule-alist (prune-dag-post-rewrite-rules) ; todo: don't do this over and over!
                                             (w state)))
       ((when erp) (mv erp nil state))
       ((mv erp result-dag-or-quotep &) (simplify-dag-basic dag
                                                          nil ; assumptions
                                                          rule-alist
                                                          nil ; interpreted-function-alist
                                                          (known-booleans (w state))
                                                          nil ; normalize-xors
                                                          nil ; limits
                                                          nil ; memoize
                                                          nil ; count-hits
                                                          nil ; print
                                                          nil ; monitored-symbols
                                                          nil ; fns-to-elide
                                                          ))
       ((when erp) (mv erp nil state))
       ((mv elapsed state) (real-time-since start-real-time state))
       (- (cw " (Pruning took ") ; todo: print for early exits above?
          (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       ((when (quotep result-dag-or-quotep))
        (cw " Done pruning. Result: ~x0)~%" result-dag-or-quotep)
        (mv (erp-nil) result-dag-or-quotep state))
       (result-dag result-dag-or-quotep)
       ;; It's a dag:
       (result-dag-len (len result-dag))
       (result-dag-size (if (not (<= result-dag-len *max-1d-array-length*))
                            "many" ; too big to call dag-or-quotep-size-fast (todo: impossible?)
                          (dag-or-quotep-size-fast result-dag)))
       (changep (not (equal old-dag result-dag)))
       (- (cw " Done pruning ")
          (if changep
              (cw "(~x0 nodes, ~x1 unique)." result-dag-size result-dag-len)
            (cw "(no change)."))
          (cw ")~%")))
    (mv (erp-nil) result-dag-or-quotep state)))

(local
  (defthm w-of-mv-nth-2-of-prune-dag-approximately
    (equal (w (mv-nth 2 (prune-dag-approximately dag assumptions print max-conflicts state)))
           (w state))
    :hints (("Goal" :in-theory (enable prune-dag-approximately)))))

(local
  (defthm pseudo-dagp-of-mv-nth-1-of-prune-dag-approximately
    (implies (and (not (mv-nth 0 (prune-dag-approximately dag assumptions print max-conflicts state))) ; no error
                  (pseudo-dagp dag)
                  ;; (<= (len dag) *max-1d-array-length*)
                  (pseudo-term-listp assumptions)
                  (ilks-plist-worldp (w state))
                  (not (quotep (mv-nth 1 (prune-dag-approximately dag assumptions print max-conflicts state)))))
             (pseudo-dagp (mv-nth 1 (prune-dag-approximately dag assumptions print max-conflicts state))))
    :hints (("Goal" :in-theory (e/d (prune-dag-approximately car-of-car-when-pseudo-dagp)
                                    (myquotep ; loop on simplify-dag-basic-return-type-corollary-2 without this
                                     ))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Disabled to speed up later guard proofs
(defund prune-approx-optionp (p)
  (declare (xargs :guard t))
  (or (booleanp p)
      (natp p)))

;; Returns (mv erp dag-or-quotep state).
;; TODO: Add option of which kinds of IF to prune
;; TODO: Add support for pruning bv-array-ifs?
;; TODO: Add support for not trying to resolve conditions that are too large (e.g., top-level conjuncts of crypto tests).
(defund maybe-prune-dag-approximately (prune-branches ; t, nil, or dag-size limit
                                       dag assumptions print max-conflicts state)
  (declare (xargs :guard (and (prune-approx-optionp prune-branches)
                              (pseudo-dagp dag)
                              ;; (<= (len dag) *max-1d-array-length*)
                              (pseudo-term-listp assumptions)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* (((when (not prune-branches))
        ;; We print nothing, as we've been told not to prune:
        (mv nil dag state))
       ((when (not (dag-fns-include-anyp dag '(if myif boolif bvif))))
        (and (print-level-at-least-tp print) (cw "(No approx pruning to do.)~%"))
        (mv nil dag state))
       ((when (> (top-nodenum-of-dag dag) *max-1d-array-index*)) (mv :dag-too-big dag state)) ; due to guard of dag-or-quotep-size-less-thanp
       ((when (and (natp prune-branches) ; it's a limit on the dag-size
                   ;; todo: allow this to fail fast:
                   (not (dag-or-quotep-size-less-thanp dag prune-branches))))
        (cw "(Note: Not pruning with approximate contexts (DAG size exceeds ~x0.)~%" prune-branches)
        (mv nil dag state)))
    ;; prune-branches is either t or is a size limit and the dag is small enough, so we prune:
    (prune-dag-approximately dag
                             assumptions
                             print max-conflicts
                             state)))

(defthm w-of-mv-nth-2-of-maybe-prune-dag-approximately
  (equal (w (mv-nth 2 (maybe-prune-dag-approximately prune-branches dag assumptions print max-conflicts state)))
         (w state))
  :hints (("Goal" :in-theory (enable maybe-prune-dag-approximately))))

(defthm pseudo-dagp-of-mv-nth-1-of-maybe-prune-dag-approximately
  (implies (and (not (mv-nth 0 (maybe-prune-dag-approximately prune-branches dag assumptions print max-conflicts state))) ; no error
                (not (quotep (mv-nth 1 (maybe-prune-dag-approximately prune-branches dag assumptions print max-conflicts state))))
                ;; (prune-approx-optionp prune-branches)
                (pseudo-dagp dag)
                ;; (<= (len dag) *max-1d-array-length*)
                (pseudo-term-listp assumptions)
                ;; (print-levelp print)
                (or (null max-conflicts)
                    (natp max-conflicts))
                (ilks-plist-worldp (w state)))
           (pseudo-dagp (mv-nth 1 (maybe-prune-dag-approximately prune-branches dag assumptions print max-conflicts state))))
  :hints (("Goal" :in-theory (e/d (maybe-prune-dag-approximately) (quotep)))))
